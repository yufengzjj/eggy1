//! `unshift`, `halve`, `split_bits` and the rebuilds with subterms abstracted to variables.

use super::*;

/// `t` with each `p·(a >> s)` (`p = 2^s·q` as `split_low` builds it) and `(a >> s) << s'` (`s' ≥ s`) written
/// with `a & -2^s` (or `~(a | (2^s - 1))` under a `~`), so that the semi-linear
/// rebuild sees `a`: `7·(x & 0xffffffff) + 0x700000000·(x >> 32)` is `7·x`. Only for
/// `a` built of T-function operations, so `(mulhi(x, M) >> 1)·12` keeps the shape the
/// magic-number division rules match.
pub(super) fn unshift(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| unshift(x, w)).collect();
    // `(a >> s) << s` for both shifts: the bits filled in by `>>` are shifted out.
    let low_cleared = |x: &T, k: u32| -> Option<(T, u32)> {
        let num = |v: u64| T::Num(w.signed(v & w.mask));
        let bin = |o: Op, p: T, q: T| T::Op(o, vec![p, q]);
        fn tfunc_ops(t: &T, w: &Ctx) -> bool {
            match t {
                T::Op(o, a) if *o == Op::Shl => const_shift(&a[1], w).is_some() && tfunc_ops(&a[0], w),
                T::Op(o, a) => matches!(o, Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Not | Op::And | Op::Or | Op::Xor) && a.iter().all(|x| tfunc_ops(x, w)),
                _ => true,
            }
        }
        match x {
            T::Op(o, b) if *o == Op::Shr && tfunc_ops(&b[0], w) => {
                let s = const_shift(&b[1], w).filter(|&s| s > 0 && s <= k)?;
                Some((bin(Op::And, b[0].clone(), num(u64::MAX << s)), s))
            }
            T::Op(o, b) if *o == Op::Not => match &b[0] {
                T::Op(o, c) if *o == Op::Shr && tfunc_ops(&c[0], w) => {
                    let s = const_shift(&c[1], w).filter(|&s| s > 0 && s <= k)?;
                    let or = bin(Op::Or, c[0].clone(), num((1u64 << s) - 1));
                    Some((T::Op(Op::Not, vec![or]), s))
                }
                _ => None,
            },
            _ => None,
        }
    };
    match (op, &a[..]) {
        (Op::Mul, [T::Num(c), x]) | (Op::Mul, [x, T::Num(c)]) if *c as u64 & w.mask != 0 => {
            if let Some((y, s)) = low_cleared(x, (*c as u64 & w.mask).trailing_zeros()) {
                return T::Op(Op::Mul, vec![T::Num(w.signed(*c as u64 & w.mask) >> s), y]);
            }
        }
        (Op::Mul, [x, p]) | (Op::Mul, [p, x]) if low_cleared(x, w.w).is_some() => {
            let (y, s) = low_cleared(x, w.w).unwrap();
            if let Some((q, 0)) = split_low(p, s, w) {
                return T::Op(Op::Mul, vec![y, q]);
            }
        }
        (Op::Shl, [x, k]) => {
            if let Some((y, s)) = const_shift(k, w).and_then(|k| low_cleared(x, k)) {
                let k = const_shift(k, w).unwrap() - s;
                return if k == 0 { y } else { T::Op(Op::Shl, vec![y, T::Num(k as i64)]) };
            }
        }
        _ => {}
    }
    T::Op(*op, a)
}

/// `(a, c)` with `t = 2^k·a + c` and `0 ≤ c < 2^k`, if `t` is built so.
fn split_low(t: &T, k: u32, w: &Ctx) -> Option<(T, u64)> {
    let lk = (1u64 << k) - 1;
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    let num = |v: u64| T::Num(w.signed(v & w.mask));
    let scaled = |c: i64, e: &T| -> Option<(T, u64)> {
        let c = c as u64 & w.mask;
        if c == 0 || c.trailing_zeros() < k {
            return None;
        }
        let c = w.signed(c) >> k;
        Some((if c == 1 { e.clone() } else { op(Op::Mul, vec![T::Num(c), e.clone()]) }, 0))
    };
    match t {
        T::Num(v) => Some((T::Num(w.signed(*v as u64 & w.mask) >> k), *v as u64 & lk)),
        T::Op(o, a) => match (o, &a[..]) {
            (Op::Mul, [T::Num(c), e]) | (Op::Mul, [e, T::Num(c)]) => scaled(*c, e),
            (Op::Mul, [x, y]) => match (split_low(x, k, w), split_low(y, k, w)) {
                (Some((p, 0)), _) => Some((op(Op::Mul, vec![p, y.clone()]), 0)),
                (_, Some((q, 0))) => Some((op(Op::Mul, vec![x.clone(), q]), 0)),
                _ => None,
            },
            (Op::Shl, [x, s]) => {
                let s = const_shift(s, w).filter(|&s| s >= k)?;
                Some((if s == k { x.clone() } else { op(Op::Shl, vec![x.clone(), T::Num((s - k) as i64)]) }, 0))
            }
            (Op::Neg, [x]) => match split_low(x, k, w)? {
                (p, 0) => Some((op(Op::Neg, vec![p]), 0)),
                (p, c) => Some((op(Op::Not, vec![p]), (1 << k) - c)),
            },
            (Op::Not, [x]) => split_low(x, k, w).map(|(p, c)| (op(Op::Not, vec![p]), lk - c)),
            (o @ (Op::Add | Op::Sub), [x, y]) => {
                let ((p, c), (q, d)) = (split_low(x, k, w)?, split_low(y, k, w)?);
                let (v, carry) = if *o == Op::Add { (c + d, c + d > lk) } else { (c.wrapping_sub(d), c < d) };
                let s = op(*o, vec![p, q]);
                let s = match (carry, o) {
                    (false, _) => s,
                    (true, Op::Add) => op(Op::Add, vec![s, num(1)]),
                    _ => op(Op::Sub, vec![s, num(1)]),
                };
                Some((s, v & lk))
            }
            (o @ (Op::And | Op::Or | Op::Xor), [x, y]) => {
                let ((p, c), (q, d)) = (split_low(x, k, w)?, split_low(y, k, w)?);
                let v = match o {
                    Op::And => c & d,
                    Op::Or => c | d,
                    _ => c ^ d,
                };
                Some((op(*o, vec![p, q]), v))
            }
            _ => None,
        },
        _ => None,
    }
}

/// `t` with the constants its low `r` bits depend on sign-extended from bit `r - 1`.
pub(crate) fn low_consts(t: &T, r: u32) -> T {
    match t {
        T::Num(v) => T::Num(v << (64 - r) >> (64 - r)),
        T::Op(op, a) if *op == Op::Shl => T::Op(*op, vec![low_consts(&a[0], r), a[1].clone()]),
        T::Op(op, a) if matches!(op, Op::Add | Op::Sub | Op::Mul | Op::And | Op::Or | Op::Xor | Op::Not | Op::Neg) => {
            T::Op(*op, a.iter().map(|x| low_consts(x, r)).collect())
        }
        _ => t.clone(),
    }
}

/// `t` with each bitwise operation whose operands are `2^k·a + c` (`c < 2^k`)
/// written as `2^k·(a op b) + (c op d)`, for the largest such `k`: a bitwise
/// operation only sees the bits of `a` that `2^k·a` keeps, so the rebuild can
/// treat `x - ((2·x) | ~(2·K)) - K - 1` as the semi-linear `x - 2·(x | ~K) - K - 2`,
/// which is `x ^ K`.
pub(super) fn halve(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| halve(x, w)).collect();
    let node = T::Op(*op, a);
    let T::Op(_, a) = &node else { unreachable!() };
    if !matches!(op, Op::And | Op::Or | Op::Xor) || a.iter().all(|x| matches!(x, T::Num(_))) {
        return node;
    }
    let mut best = None;
    for k in 1..w.w {
        match split_low(&node, k, w) {
            Some(s) => best = Some((k, s)),
            None => break,
        }
    }
    let Some((k, (T::Op(op, a), c))) = best else { return node };
    // Only the low `w - k` bits of the operands matter, so their constants are cut
    // to that width, once the rebuild has merged them: `(2^63 + 1)·y` becomes `y`.
    let inner = T::Op(op, a.iter().map(|x| low_consts(&rewrite(x, w), w.w - k)).collect());
    let scaled = T::Op(Op::Mul, vec![T::Num(w.signed(1 << k)), inner]);
    if c == 0 { scaled } else { T::Op(Op::Add, vec![scaled, T::Num(c as i64)]) }
}

/// Most variable bits `split_bits` tries on one term, how deep it nests, and the
/// largest first rebuild it runs on.
const MAX_SPLITS: usize = 4;
const SPLIT_DEPTH: usize = 2;
pub(super) const MAX_SPLIT_SIZE: usize = 64;
/// Most rebuilds one `split_bits` call runs.
const SPLIT_RUNS: usize = 16;

/// `(s, k)` for a product factor with one or two bits not known, `k` the lowest of them:
/// first the subterm `s` it is built from with constants alone, as `z + x` in
/// `3 & ((z + x) + 5)`, then each variable `s` of it.
fn split_points(t: &T, w: &Ctx) -> Vec<(T, u32)> {
    fn is_const(t: &T) -> bool {
        match t {
            T::Var(_) => false,
            T::Num(_) => true,
            T::Op(_, a) => a.iter().all(is_const),
        }
    }
    fn core(t: &T) -> &T {
        match t {
            T::Op(_, a) if a.iter().filter(|x| !is_const(x)).count() == 1 => core(a.iter().find(|x| !is_const(x)).unwrap()),
            _ => t,
        }
    }
    fn go(t: &T, w: &Ctx, out: &mut Vec<(T, u32)>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) {
            for f in a {
                let g = match f {
                    T::Op(Op::Neg, b) => &b[0],
                    _ => f,
                };
                let bits = crate::lowbits::unknown_bits(g, w);
                if bits != 0 && bits.count_ones() <= 2 {
                    let k = bits.trailing_zeros();
                    let s = core(f);
                    let vars = crate::eval::vars(f).into_iter().map(T::Var);
                    for s in std::iter::once(s.clone()).filter(|s| matches!(s, T::Op(..))).chain(vars) {
                        if !out.contains(&(s.clone(), k)) {
                            out.push((s, k));
                        }
                    }
                }
            }
        }
        a.iter().for_each(|x| go(x, w, out));
    }
    let mut out = Vec::new();
    go(t, w, &mut out);
    out
}

/// `(v, k)` for each variable `v` of a product factor that is 0 or `2^k` by known bits.
pub(super) fn selectors(t: &T, w: &Ctx) -> Vec<(String, u32)> {
    fn go(t: &T, w: &Ctx, out: &mut Vec<(String, u32)>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) {
            for f in a {
                let bits = crate::lowbits::possible_bits(f, w);
                if bits.is_power_of_two() {
                    for v in crate::eval::vars(f) {
                        if !out.contains(&(v.clone(), bits.trailing_zeros())) {
                            out.push((v, bits.trailing_zeros()));
                        }
                    }
                }
            }
        }
        a.iter().for_each(|x| go(x, w, out));
    }
    let mut out = Vec::new();
    go(t, w, &mut out);
    out
}

/// `t` rebuilt by cases on bit `k` of a variable `v` that selects a product, as in
/// `(1 & ~y)*(-y & -2) + (-y | 1)*(y & 1)`, which is `-y`: with `r0` and `r1` the
/// rebuilds of `t` with that bit cleared and set, `t = r0 + ((v >> k) & 1)*(r1 - r0)`.
/// A subterm `s` is split as a variable `v` that replaces it, which holds for any `v`
/// and so for `v = s`. The halves are split again, up to `depth` times.
/// Returns `t` when nothing smaller without selecting products is found or `budget`
/// (rebuilds left) runs out.
pub(super) fn split_bits(t: T, depth: usize, budget: &std::cell::Cell<usize>, w: &Ctx, run: &dyn Fn(&T) -> T) -> T {
    if depth == 0 {
        return t;
    }
    let run = |t: &T| {
        budget.set(budget.get().saturating_sub(1));
        run(t)
    };
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    for (s, k) in split_points(&t, w).into_iter().take(MAX_SPLITS) {
        if budget.get() < 3 {
            break;
        }
        let (var, ts) = match s {
            T::Var(_) => (s.clone(), t.clone()),
            _ => {
                let v = T::Var(format!("\u{3}{depth}"));
                let ts = crate::lowbits::replace(&t, std::slice::from_ref(&s), std::slice::from_ref(&v));
                (v, ts)
            }
        };
        let m = 1u64 << k;
        let half = |b: T| split_bits(run(&crate::lowbits::replace(&ts, std::slice::from_ref(&var), &[b])), depth - 1, budget, w, &run);
        let r0 = half(op(Op::And, vec![var.clone(), T::Num(w.signed(!m & w.mask))]));
        if !selectors(&r0, w).is_empty() {
            continue;
        }
        let r1 = half(op(Op::Or, vec![var.clone(), T::Num(w.signed(m))]));
        if !selectors(&r1, w).is_empty() {
            continue;
        }
        let d = run(&op(Op::Sub, vec![r1, r0.clone()]));
        let ty = crate::eval::NumType { bits: w.w, signed: false };
        // Only T-function operations: `/ % >> mulhi` depend on the signedness, which `w` does not give.
        let c = Some(()).filter(|_| crate::eval::vars(&d).is_empty() && crate::minimal::t_term(&d)).and_then(|_| crate::eval::eval(&d, ty, &|_| 0));
        let sel = match c {
            Some(c) if c & (m - 1) == 0 => op(Op::Mul, vec![op(Op::And, vec![var.clone(), T::Num(w.signed(m))]), T::Num(w.signed(c >> k))]),
            _ if k == 0 => op(Op::Mul, vec![op(Op::And, vec![var.clone(), T::Num(1)]), d]),
            _ => op(Op::Mul, vec![op(Op::And, vec![op(Op::Shr, vec![var.clone(), T::Num(k as i64)]), T::Num(1)]), d]),
        };
        let mut r = run(&op(Op::Add, vec![r0, sel]));
        if var != s {
            r = run(&crate::lowbits::replace(&r, std::slice::from_ref(&var), std::slice::from_ref(&s)));
        }
        if size(&r) < size(&t) && selectors(&r, w).is_empty() {
            return r;
        }
    }
    t
}

/// `rebuild_once` with each bitwise operation of a term and a constant (`y ^ 0xdeadbeef`)
/// first replaced by a fresh variable: a region whose constants all sit in such subterms
/// becomes linear, `(z & (u ^ ((K & p) ^ ~w))) + 2·(z & p & ~(u ^ w) & K)` is
/// `(z & ~(u ^ w)) + (z & p & K)`.
pub(super) fn over_const_bitwise(t: &T, w: &Ctx) -> T {
    over_subterms(t, w, &|x| match x {
        T::Op(Op::And | Op::Or | Op::Xor, a) => a.iter().any(|y| matches!(y, T::Num(_))) && !a.iter().all(|y| matches!(y, T::Num(_))),
        _ => false,
    })
}

/// `rebuild_once` with each bitwise subterm of at least 3 nodes that occurs more than once
/// first replaced by a fresh variable: the region then has fewer leaves, and a table over
/// few leaves rebuilds exactly, `6·(t & u & A & B) - 3·(A ^ (t & ~(B & u)))` is
/// `3·((t & u & B) - (t ^ A))` with `A = y ^ (u + w)`, `B = y ^ w`.
pub(super) fn over_shared_bitwise(t: &T, w: &Ctx) -> T {
    fn count(t: &T, seen: &mut crate::eval::FastMap<T, usize>) {
        let T::Op(op, a) = t else { return };
        if matches!(op, Op::And | Op::Or | Op::Xor) && size(t) >= 3 {
            let n = seen.entry(t.clone()).or_insert(0);
            *n += 1;
            if *n > 1 {
                return;
            }
        }
        a.iter().for_each(|x| count(x, seen));
    }
    let mut seen = crate::eval::FastMap::default();
    count(t, &mut seen);
    over_subterms(t, w, &|x| seen.get(x).is_some_and(|&n| n > 1))
}

/// `rebuild_once` with the outermost subterms that `pick` selects replaced by fresh
/// variables, which are put back after; kept when smaller. The identity found holds for
/// every value of the variables, so for the subterms too.
fn over_subterms(t: &T, w: &Ctx, pick: &dyn Fn(&T) -> bool) -> T {
    fn go(t: &T, pick: &dyn Fn(&T) -> bool, found: &mut Vec<T>) -> T {
        if pick(t) {
            let i = found.iter().position(|f| f == t).unwrap_or_else(|| {
                found.push(t.clone());
                found.len() - 1
            });
            return T::Var(format!("%k{i}"));
        }
        let T::Op(op, a) = t else { return t.clone() };
        T::Op(*op, a.iter().map(|x| go(x, pick, found)).collect())
    }
    let mut found = Vec::new();
    let a = go(t, pick, &mut found);
    if found.is_empty() {
        return t.clone();
    }
    let r = rebuild_once(&a, w);
    if r == a {
        return t.clone();
    }
    let vars: Vec<T> = (0..found.len()).map(|i| T::Var(format!("%k{i}"))).collect();
    let back = crate::lowbits::replace(&r, &vars, &found);
    if size(&back) < size(t) { back } else { t.clone() }
}

/// `split_bits` on `t`, then on the operands of `t` when it is a bitwise operation, since
/// a case split rarely gives a constant difference through one; each with its own budget.
pub(super) fn split_in(t: &T, w: &Ctx, run: &dyn Fn(&T) -> T) -> T {
    let s = split_bits(t.clone(), SPLIT_DEPTH, &std::cell::Cell::new(SPLIT_RUNS), w, run);
    if s != *t {
        return s;
    }
    match t {
        T::Op(op, a) if matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) => {
            let b: Vec<T> = a.iter().map(|x| if split_points(x, w).is_empty() { x.clone() } else { split_in(x, w, run) }).collect();
            if b == *a {
                return t.clone();
            }
            let r = run(&T::Op(*op, b));
            if size(&r) < size(t) { r } else { t.clone() }
        }
        _ => t.clone(),
    }
}
