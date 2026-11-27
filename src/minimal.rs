//! A test that no term with fewer nodes equals a given one, so saturating it cannot help.

use crate::eval::{apply, size, vars, NumType, Op, Term};
use crate::sched::{limit, Limit};

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
    if k == 0 || n > 2 * k + 1 || (n > 2 * k - 1 && k > limit(Limit::MinimalMaxVars)) {
        return false;
    }
    let points = points(k, limit(Limit::MinimalPoints));
    let at = |e: &Term, p: &[u64]| strict_eval(e, ty, &names, p);
    let values: Vec<Option<u64>> = points.iter().map(|p| at(t, p)).collect();
    // Each variable must change the value somewhere, or a term without it could be equal.
    let relevant = (0..k).all(|v| {
        points.iter().zip(&values).enumerate().any(|(i, (p, x))| {
            let mut q = p.clone();
            q[v] = points[(i + 1) % points.len()][v];
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

const T_OPS: [Op; 6] = [Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor];
/// Most lanes (`minimal_lanes`) of the value vectors; the variables are 0 in the lanes past it.
pub(crate) const LANES_CAP: usize = 16;

/// Whether no term with fewer nodes than `t` built of `+ - * & | ^ ~` and negation,
/// variables of `t` and any constants equals `t`; `false` when that is not proved.
///
/// Such terms commute with truncation, so one equal to `t` would also be equal in the
/// low bits with its constants cut to them. In 4 bits (up to `minimal_max_size_4bit` nodes)
/// and in 8 (up to `minimal_max_size_8bit`), all terms are built bottom up by size, each
/// distinct vector of values at the points kept once, and none smaller than `t` may give
/// `t`'s vector.
pub fn is_t_minimal(t: &Term) -> bool {
    let n = size(t);
    n == 1 || t_term(t) && (n <= limit(Limit::MinimalMaxSize4bit) && none_smaller_low(t, 4) || n <= limit(Limit::MinimalMaxSize8bit) && none_smaller_low(t, 8))
}

fn none_smaller_low(t: &Term, bits: u32) -> bool {
    let n = size(t);
    let names = vars(t);
    let ty = NumType { bits, signed: false };
    let m = ty.mask() as u8;
    let (lanes, budget) = (limit(Limit::MinimalLanes), limit(Limit::MinimalBudget));
    let mut s = 0x2545_f491_4f6c_dd1du64;
    let mut points: Vec<Vec<u64>> = (0..lanes)
        .map(|_| {
            (0..names.len())
                .map(|_| {
                    s ^= s << 13;
                    s ^= s >> 7;
                    s ^= s << 17;
                    s >> (64 - bits)
                })
                .collect()
        })
        .collect();
    points.resize(LANES_CAP, vec![0; names.len()]);
    let mut target = [0u8; LANES_CAP];
    for (i, p) in points.iter().enumerate() {
        match strict_eval(t, ty, &names, p) {
            Some(v) => target[i] = v as u8,
            None => return false,
        }
    }
    let mut seen: crate::eval::FastSet<[u8; LANES_CAP]> = Default::default();
    let mut levels: Vec<Vec<[u8; LANES_CAP]>> = vec![Vec::new(), Vec::new()];
    for v in 0..names.len() {
        levels[1].push(std::array::from_fn(|i| points[i][v] as u8));
    }
    for c in 0..=m {
        levels[1].push([c; LANES_CAP]);
    }
    levels[1].retain(|v| seen.insert(*v));
    let mut work = 0;
    for size in 2..n {
        if seen.contains(&target) {
            return false;
        }
        let mut next = Vec::new();
        let mut add = |v: [u8; LANES_CAP], next: &mut Vec<[u8; LANES_CAP]>| {
            if seen.insert(v) {
                next.push(v);
            }
        };
        for a in &levels[size - 1] {
            add(a.map(|x| !x & m), &mut next);
            add(a.map(|x| x.wrapping_neg() & m), &mut next);
        }
        for i in 1..size - 1 {
            let (left, right) = (&levels[i], &levels[size - 1 - i]);
            work += left.len() * right.len();
            if work > budget {
                return false;
            }
            for a in left {
                for b in right {
                    let f = |g: fn(u8, u8) -> u8| -> [u8; LANES_CAP] { std::array::from_fn(|l| g(a[l], b[l]) & m) };
                    add(f(u8::wrapping_add), &mut next);
                    add(f(u8::wrapping_sub), &mut next);
                    add(f(u8::wrapping_mul), &mut next);
                    add(f(|x, y| x & y), &mut next);
                    add(f(|x, y| x | y), &mut next);
                    add(f(|x, y| x ^ y), &mut next);
                }
            }
        }
        levels.push(next);
    }
    !seen.contains(&target)
}

/// Whether `t` has only the operations of `is_t_minimal`.
pub fn t_term(t: &Term) -> bool {
    match t {
        Term::Op(op, a) => (T_OPS.contains(op) || matches!(op, Op::Not | Op::Neg)) && a.iter().all(t_term),
        _ => true,
    }
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
fn points(k: usize, n: usize) -> Vec<Vec<u64>> {
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let corner = [0u64, 1, u64::MAX, 2, 3, 5];
    (0..n)
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
        crate::sched::in_default_run(|| is_minimal(&crate::eval::parse(&infix_to_egglog(e, true)), NumType::from_name(ty).unwrap()))
    }

    /// `drive` relies on this to use `is_t_minimal`.
    #[test]
    fn rules_make_no_shift_division_or_mulhi() {
        enum S {
            Atom(String),
            List(Vec<S>),
        }
        fn parse(toks: &[String], i: &mut usize) -> S {
            *i += 1;
            if toks[*i - 1] != "(" {
                return S::Atom(toks[*i - 1].clone());
            }
            let mut out = Vec::new();
            while toks[*i] != ")" {
                out.push(parse(toks, i));
            }
            *i += 1;
            S::List(out)
        }
        fn heads(s: &S, out: &mut Vec<String>) {
            if let S::List(l) = s {
                if let Some(S::Atom(h)) = l.first() {
                    out.push(h.clone());
                }
                l.iter().for_each(|x| heads(x, out));
            }
        }
        let opaque = |s: &S| {
            let mut h = Vec::new();
            heads(s, &mut h);
            h.iter().any(|h| ["Shl", "Shr", "Div", "Mod", "Mulhi"].contains(&h.as_str()))
        };
        for ty in ["i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8"] {
            let text: String = crate::make_egg(ty).lines().map(|l| l.split(';').next().unwrap()).collect::<Vec<_>>().join("\n");
            let text = text.replace('(', " ( ").replace(')', " ) ");
            let toks: Vec<String> = text.split_whitespace().map(String::from).collect();
            let (mut i, mut rules) = (0, 0);
            while i < toks.len() {
                let S::List(f) = parse(&toks, &mut i) else { continue };
                let (S::Atom(kind), Some(l), Some(r)) = (&f[0], f.get(1), f.get(2)) else { continue };
                let ok = |l: &S, r: &S| opaque(l) || !opaque(r);
                match kind.as_str() {
                    "rewrite" | "rule" => assert!(ok(l, r), "{ty}: a {kind} makes a shift, division or mulhi"),
                    "birewrite" => assert!(ok(l, r) && ok(r, l), "{ty}: a birewrite makes a shift, division or mulhi"),
                    _ => continue,
                }
                rules += 1;
            }
            assert!(rules > 200, "{ty}: {rules} rules read");
        }
    }

    #[test]
    fn t_terms() {
        let t = |e: &str| crate::sched::in_default_run(|| is_t_minimal(&crate::eval::parse(&infix_to_egglog(e, true))));
        for e in ["-2*(x|y) + 1", "(x & -4) ^ 0x1234567", "14 * ~(y|x)", "6 * ~x", "(x ^ y) * (x | 5)", "(x & 0x7f) * 3"] {
            assert!(t(e), "{e}");
        }
        for e in ["(x|y) - (x&y)", "x * -1", "(x & 3) + (x & ~3)", "2*(x|y) - (x^y)", "(x + 1) * (x - 1) + 1", "-(~x * 3)"] {
            assert!(!t(e), "{e}");
        }
    }

    #[test]
    fn small_terms() {
        for e in ["x", "~x", "x + y", "x & 5", "x - 1", "~-x", "x * 2", "x + y + 0x10", "(x ^ y) + z", "x*y + z*w", "~(x + y)", "~x & (y | z)", "(z & y) ^ (z | x)"] {
            assert!(minimal(e, "i64"), "{e}");
        }
        for e in ["x * -1", "0 - y", "x ^ x", "x + 0", "(x | y) - (x & y)", "~(~x + y)", "-(x - y)", "(x & y) + (x | y)"] {
            assert!(!minimal(e, "i64"), "{e}");
        }
        assert!(!minimal("x * 255", "u8"));
        assert!(minimal("x * 255", "u16"));
    }
}
