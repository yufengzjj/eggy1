//! Shortest bitwise expressions for truth tables, and `g(A) op h(B)` decompositions.

use super::*;

#[derive(Clone)]
pub(super) enum B {
    V(usize),
    Not(Arc<B>),
    Bin(Op, Arc<B>, Arc<B>),
}

/// Smallest bitwise expression for every truth table over `n` variables.
/// Table bit `p` is the value at the point whose bit `i` is variable `i`.
fn bool_table(n: usize) -> &'static [Option<(usize, B)>] {
    static TABLES: [OnceLock<Vec<Option<(usize, B)>>>; 4] =
        [OnceLock::new(), OnceLock::new(), OnceLock::new(), OnceLock::new()];
    TABLES[n].get_or_init(|| {
        let pts = 1usize << n;
        let full = (1usize << pts) - 1;
        let mut best: Vec<Option<(usize, B)>> = vec![None; full + 1];
        for i in 0..n {
            let tt = (0..pts).filter(|p| p >> i & 1 == 1).fold(0, |acc, p| acc | 1 << p);
            best[tt] = Some((1, B::V(i)));
        }
        loop {
            let known: Vec<(usize, usize, Arc<B>)> = best
                .iter()
                .enumerate()
                .filter_map(|(tt, e)| e.as_ref().map(|(c, b)| (tt, *c, Arc::new(b.clone()))))
                .collect();
            let mut changed = false;
            let mut offer = |best: &mut Vec<Option<(usize, B)>>, tt: usize, c: usize, b: &dyn Fn() -> B| {
                if best[tt].as_ref().is_none_or(|(old, _)| c < *old) {
                    best[tt] = Some((c, b()));
                    changed = true;
                }
            };
            for (ta, ca, ba) in &known {
                offer(&mut best, !ta & full, ca + 1, &|| B::Not(ba.clone()));
                for (tb, cb, bb) in &known {
                    if ta > tb {
                        continue;
                    }
                    let c = ca + cb + 1;
                    for (op, tt) in [(Op::And, ta & tb), (Op::Or, ta | tb), (Op::Xor, ta ^ tb)] {
                        offer(&mut best, tt, c, &|| B::Bin(op, ba.clone(), bb.clone()));
                    }
                }
            }
            if !changed {
                break best;
            }
        }
    })
}

#[derive(Clone)]
pub(super) enum BE {
    Zero,
    Ones,
    E(usize, B),
}

pub(super) fn remap(b: &B, vars: &[usize]) -> B {
    match b {
        B::V(i) => B::V(vars[*i]),
        B::Not(x) => B::Not(Arc::new(remap(x, vars))),
        B::Bin(op, x, y) => B::Bin(*op, Arc::new(remap(x, vars)), Arc::new(remap(y, vars))),
    }
}

/// Short bitwise expression for truth table `tt` over `vars` (table bit `p`
/// is the value where bit `j` of `p` is `vars[j]`). Exact table lookup up to 3
/// variables; above that, Shannon expansion on the best variable.
pub(super) fn bool_expr(tt: u64, vars: &[usize]) -> BE {
    match bool_expr_canon(tt, vars.len()) {
        BE::E(c, b) => BE::E(c, remap(&b, vars)),
        other => other,
    }
}

pub(super) fn table_full(n: usize) -> u64 {
    if n >= 6 { u64::MAX } else { (1u64 << (1 << n)) - 1 }
}

/// `bool_expr` over variables `0..n`, cached.
pub(super) fn bool_expr_canon(tt: u64, n: usize) -> BE {
    thread_local! {
        static CACHE: std::cell::RefCell<crate::eval::FastMap<(u64, usize), BE>> = Default::default();
    }
    if n <= 3 {
        return bool_expr_uncached(tt, n);
    }
    if let Some(r) = CACHE.with(|c| c.borrow().get(&(tt, n)).cloned()) {
        return r;
    }
    let r = bool_expr_uncached(tt, n);
    CACHE.with(|c| c.borrow_mut().insert((tt, n), r.clone()));
    r
}

fn bool_expr_uncached(tt: u64, n: usize) -> BE {
    let pts = 1usize << n;
    if tt == 0 {
        return BE::Zero;
    }
    if tt == table_full(n) {
        return BE::Ones;
    }
    if n <= 3 {
        let (c, b) = bool_table(n)[tt as usize].as_ref().expect("non-constant table");
        return BE::E(*c, b.clone());
    }
    let not = |b: B| B::Not(Arc::new(b));
    let bin = |op, x: B, y: B| B::Bin(op, Arc::new(x), Arc::new(y));
    let mut best: Option<(usize, B)> = None;
    for i in 0..n {
        let rest: Vec<usize> = (0..n).filter(|&j| j != i).collect();
        let (mut f0, mut f1) = (0u64, 0u64);
        for p in 0..pts {
            if tt >> p & 1 == 1 {
                let q = (p & ((1 << i) - 1)) | (p >> (i + 1) << i);
                if p >> i & 1 == 0 { f0 |= 1 << q } else { f1 |= 1 << q }
            }
        }
        let x = B::V(i);
        let sub_full = table_full(n - 1);
        let cost = match (bool_expr_canon(f0, n - 1), bool_expr_canon(f1, n - 1)) {
            (BE::Zero, BE::Ones) => 1,
            (BE::Ones, BE::Zero) => 2,
            (BE::Zero, BE::E(c, _)) | (BE::E(c, _), BE::Ones) => c + 2,
            (BE::E(c, _), BE::Zero) | (BE::Ones, BE::E(c, _)) => c + 3,
            (BE::E(c, _), _) if f0 == f1 => c,
            (BE::E(c, _), _) if f1 == !f0 & sub_full => c + 2,
            (BE::E(c0, _), BE::E(c1, _)) => match bool_expr_canon(f0 ^ f1, n - 1) {
                BE::E(cd, _) if c0 + cd + 3 < c0 + c1 + 6 => c0 + cd + 3,
                _ => c0 + c1 + 6,
            },
            (BE::Zero, BE::Zero) | (BE::Ones, BE::Ones) => unreachable!("tt is not constant"),
        };
        if best.as_ref().is_some_and(|(c, _)| cost >= *c) {
            continue;
        }
        let cand = match (bool_expr(f0, &rest), bool_expr(f1, &rest)) {
            (BE::Zero, BE::Ones) => (1, x),
            (BE::Ones, BE::Zero) => (2, not(x)),
            (BE::Zero, BE::E(c, e)) => (c + 2, bin(Op::And, x, e)),
            (BE::E(c, e), BE::Zero) => (c + 3, bin(Op::And, not(x), e)),
            (BE::Ones, BE::E(c, e)) => (c + 3, bin(Op::Or, not(x), e)),
            (BE::E(c, e), BE::Ones) => (c + 2, bin(Op::Or, x, e)),
            (BE::E(c, e), _) if f0 == f1 => (c, e),
            (BE::E(c, e), _) if f1 == !f0 & sub_full => (c + 2, bin(Op::Xor, x, e)),
            (BE::E(c0, e0), BE::E(c1, e1)) => {
                let mux = (c0 + c1 + 6, bin(Op::Or, bin(Op::And, x.clone(), e1), bin(Op::And, not(x.clone()), e0.clone())));
                match bool_expr(f0 ^ f1, &rest) {
                    BE::E(cd, d) if c0 + cd + 3 < mux.0 => (c0 + cd + 3, bin(Op::Xor, e0, bin(Op::And, x, d))),
                    _ => mux,
                }
            }
            (BE::Zero, BE::Zero) | (BE::Ones, BE::Ones) => unreachable!("tt is not constant"),
        };
        if best.as_ref().is_none_or(|(c, _)| cand.0 < *c) {
            best = Some(cand);
        }
    }
    let bound = best.as_ref().map_or(usize::MAX, |b| b.0);
    if let Some(cand) = if n <= MAX_DECOMPOSE { decompose(tt, n, bound) } else { None } {
        best = Some(cand);
    }
    let (c, b) = best.unwrap();
    BE::E(c, b)
}

/// Most variables `bool_expr` tries `decompose` on; its cost grows with the pairs of
/// subsets (`decompose_regions` goes to 6 on the final result).
pub(super) const MAX_DECOMPOSE: usize = 5;

/// Smallest `g(A) op h(B)` with `A ∪ B` all variables and both proper subsets, as in
/// `((w ^ x) | (x & y)) & ~(y ^ z)`. For `&`, `g` and `h` are `tt` ORed over the
/// variables outside their set; for `|`, ANDed; for `^`, `g = tt(B \ A = 0)` and
/// `h = tt(A \ B = 0) ^ tt(A \ B = 0, B \ A = 0)`. Each is checked against `tt`. Only
/// splits smaller than `bound` are returned.
pub(super) fn decompose(tt: u64, n: usize, bound: usize) -> Option<(usize, B)> {
    let full_vars = (1usize << n) - 1;
    let full = table_full(n);
    // Table with variable `i` forced to `v`, still over all `n` variables.
    let fix = |t: u64, i: usize, v: usize| {
        let low = [0x5555_5555_5555_5555u64, 0x3333_3333_3333_3333, 0x0f0f_0f0f_0f0f_0f0f, 0x00ff_00ff_00ff_00ff, 0x0000_ffff_0000_ffff, 0x0000_0000_ffff_ffff][i];
        let half = (if v == 0 { t } else { t >> (1 << i) }) & low & full;
        half | half << (1 << i)
    };
    let over = |t: u64, keep: usize, f: &dyn Fn(u64, u64) -> u64| {
        (0..n).filter(|&i| keep >> i & 1 == 0).fold(t, |t, i| f(fix(t, i, 0), fix(t, i, 1)))
    };
    let zero_out = |t: u64, keep: usize| (0..n).filter(|&i| keep >> i & 1 == 0).fold(t, |t, i| fix(t, i, 0));
    // The points with no variable outside `keep`, in increasing order, are the points of
    // the table over `keep`'s variables.
    let sub = |t: u64, keep: usize| -> Option<(usize, B)> {
        let (mut st, mut p, mut q) = (0u64, 0usize, 0);
        loop {
            st |= (t >> p & 1) << q;
            q += 1;
            p = p.wrapping_sub(keep) & keep;
            if p == 0 {
                break;
            }
        }
        match bool_expr_canon(st, keep.count_ones() as usize) {
            BE::E(c, b) => Some((c, b)),
            _ => None,
        }
    };
    let vars = |keep: usize| -> Vec<usize> { (0..n).filter(|&i| keep >> i & 1 == 1).collect() };
    let any: Vec<u64> = (0..=full_vars).map(|k| over(tt, k, &|x, y| x | y)).collect();
    let all: Vec<u64> = (0..=full_vars).map(|k| over(tt, k, &|x, y| x & y)).collect();
    let zero: Vec<u64> = (0..=full_vars).map(|k| zero_out(tt, k)).collect();
    // The size to beat, and the best split below it (built once at the end).
    let mut best: (usize, Option<(Op, usize, usize, u64, u64)>) = (bound, None);
    for a in 1..full_vars {
        for b in a..full_vars {
            if a | b != full_vars {
                continue;
            }
            let pairs = [(Op::And, any[a], any[b]), (Op::Or, all[a], all[b]), (Op::Xor, zero[a], zero[b] ^ zero[a & b])];
            for (op, g, h) in pairs {
                let joined = match op {
                    Op::And => g & h,
                    Op::Or => g | h,
                    _ => g ^ h,
                } & full;
                if joined != tt {
                    continue;
                }
                let Some((cg, _)) = sub(g, a) else { continue };
                if cg + 2 >= best.0 {
                    continue;
                }
                let Some((ch, _)) = sub(h, b) else { continue };
                if cg + ch + 1 < best.0 {
                    best = (cg + ch + 1, Some((op, a, b, g, h)));
                }
            }
        }
    }
    let (op, a, b, g, h) = best.1?;
    let (eg, eh) = (sub(g, a)?.1, sub(h, b)?.1);
    Some((best.0, B::Bin(op, Arc::new(remap(&eg, &vars(a))), Arc::new(remap(&eh, &vars(b))))))
}

pub(super) fn b_to_t(b: &B, leaves: &[T]) -> T {
    match b {
        B::V(i) => leaves[*i].clone(),
        B::Not(x) => T::Op(Op::Not, vec![b_to_t(x, leaves)]),
        B::Bin(op, x, y) => T::Op(*op, vec![b_to_t(x, leaves), b_to_t(y, leaves)]),
    }
}

/// `b_to_t` of `b` with variable `i` standing for `leaves[vars[i]]`.
pub(super) fn b_to_t_at(b: &B, vars: &[usize], leaves: &[T]) -> T {
    match b {
        B::V(i) => leaves[vars[*i]].clone(),
        B::Not(x) => T::Op(Op::Not, vec![b_to_t_at(x, vars, leaves)]),
        B::Bin(op, x, y) => T::Op(*op, vec![b_to_t_at(x, vars, leaves), b_to_t_at(y, vars, leaves)]),
    }
}
