//! A test that no term with fewer nodes equals a given one, so saturating it cannot help.

use crate::eval::{apply, size, vars, NumType, Op, Term};

const POINTS: usize = 64;
const BINARY: [Op; 11] = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Mod, Op::And, Op::Or, Op::Xor, Op::Shl, Op::Shr, Op::Mulhi];

/// Whether every term with fewer nodes than `t` differs from `t` at some point; `false`
/// when that is not proved.
///
/// A term depending on `k` variables has at least `k` leaves, so at least `2k - 1` nodes;
/// a smaller term than one of at most `2k + 1` nodes therefore has exactly the `k`
/// variables as leaves and at most one unary operation, which leaves few to rule out.
pub fn is_minimal(t: &Term, ty: NumType) -> bool {
    let n = size(t);
    if n == 1 {
        return true;
    }
    let names = vars(t);
    let k = names.len();
    if k == 0 || n > 2 * k + 1 || (n > 2 * k - 1 && k > 3) {
        return false;
    }
    let points = points(k);
    let at = |e: &Term, p: &[u64]| strict_eval(e, ty, &names, p);
    let values: Vec<Option<u64>> = points.iter().map(|p| at(t, p)).collect();
    // Each variable must change the value somewhere, or a term without it could be equal.
    let relevant = (0..k).all(|v| {
        points.iter().zip(&values).enumerate().any(|(i, (p, x))| {
            let mut q = p.clone();
            q[v] = points[(i + 1) % POINTS][v];
            matches!((x, at(t, &q)), (Some(x), Some(y)) if *x != y)
        })
    });
    if !relevant {
        return false;
    }
    (0..n - (2 * k - 1)).all(|u| {
        trees((1u32 << k) - 1, u).iter().all(|c| {
            points.iter().zip(&values).any(|(p, x)| matches!((x, at(c, p)), (Some(x), Some(y)) if *x != y))
        })
    })
}

/// Whether `t` has none of the forms the rules replace by more readable ones of the same
/// size: `~-a` and `-~a` (`a - 1`, `a + 1`), and a binary operation on equal operands
/// (`a + a` is `2 * a`).
pub fn is_tidy(t: &Term) -> bool {
    match t {
        Term::Op(Op::Not, a) if matches!(&a[0], Term::Op(Op::Neg, _)) => false,
        Term::Op(Op::Neg, a) if matches!(&a[0], Term::Op(Op::Not, _)) => false,
        Term::Op(_, a) if a.len() == 2 && a[0] == a[1] => false,
        Term::Op(_, a) => a.iter().all(is_tidy),
        _ => true,
    }
}

/// Terms with each variable of `set` (a bit set of indices) as exactly one leaf and `u`
/// unary operations.
fn trees(set: u32, u: usize) -> Vec<Term> {
    let mut out = Vec::new();
    if set.count_ones() == 1 && u == 0 {
        out.push(Term::Var(format!("\u{1}{}", set.trailing_zeros())));
    }
    if u > 0 {
        for t in trees(set, u - 1) {
            out.push(Term::Op(Op::Not, vec![t.clone()]));
            out.push(Term::Op(Op::Neg, vec![t]));
        }
    }
    let mut a = (set - 1) & set;
    while a > 0 {
        let b = set & !a;
        for ua in 0..=u {
            let (left, right) = (trees(a, ua), trees(b, u - ua));
            for l in &left {
                for r in &right {
                    for op in BINARY {
                        out.push(Term::Op(op, vec![l.clone(), r.clone()]));
                    }
                }
            }
        }
        a = (a - 1) & set;
    }
    out
}

/// Evaluation points: the corner values, then pseudo-random ones, half of them of small
/// magnitude so that shift amounts such as `~y` or `x + y` stay below the width.
fn points(k: usize) -> Vec<Vec<u64>> {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let corner = [0u64, 1, u64::MAX, 2, 3, 5];
    (0..POINTS)
        .map(|i| {
            (0..k)
                .map(|v| match i {
                    _ if i < corner.len() => corner[(i + v) % corner.len()],
                    _ if i % 4 == 0 => (next() % 9).wrapping_sub(4),
                    _ if i % 4 == 2 => (next() % 81).wrapping_sub(40),
                    _ => next() >> (next() % 64),
                })
                .collect()
        })
        .collect()
}

/// Value of `t` with variable `names[i]` (in `trees`, `\u{1}i`) set to `p[i]`;
/// `None` where an operation is outside the range all rewrite rules agree on (a zero
/// divisor or a shift by at least the width).
fn strict_eval(t: &Term, ty: NumType, names: &[String], p: &[u64]) -> Option<u64> {
    match t {
        Term::Num(c) => Some(*c as u64 & ty.mask()),
        Term::Var(v) => {
            let i = match v.strip_prefix('\u{1}') {
                Some(i) => i.parse().ok()?,
                None => names.iter().position(|n| n == v)?,
            };
            Some(p[i] & ty.mask())
        }
        Term::Op(op, a) => {
            let x = strict_eval(&a[0], ty, names, p)?;
            let y = match a.get(1) {
                Some(b) => strict_eval(b, ty, names, p)?,
                None => 0,
            };
            if matches!(op, Op::Shl | Op::Shr) && y >= ty.bits as u64 {
                return None;
            }
            apply(*op, x, y, ty)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr_convert::infix_to_egglog;

    fn minimal(e: &str, ty: &str) -> bool {
        is_minimal(&crate::eval::parse(&infix_to_egglog(e, true)), NumType::from_name(ty).unwrap())
    }

    #[test]
    fn small_terms() {
        for e in ["x", "~x", "x + y", "x & 5", "x - 1", "~-x", "x * 2", "x + y + 0x10", "(x ^ y) + z", "x*y + z*w", "~(x + y)", "~x & (y | z)"] {
            assert!(minimal(e, "i64"), "{e}");
        }
        for e in ["x * -1", "0 - y", "x ^ x", "x + 0", "(x | y) - (x & y)", "~(~x + y)", "-(x - y)", "(x & y) + (x | y)"] {
            assert!(!minimal(e, "i64"), "{e}");
        }
        assert!(!minimal("x * 255", "u8"));
        assert!(minimal("x * 255", "u16"));
    }
}
