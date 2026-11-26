//! `polish`, the passes run on the final result.

use super::*;

/// `t` with the constant of each linear region rebuilt together with one leaf group (of at
/// most `max_leaves` leaves), or two groups of at most `join_constants_max_leaves` leaves,
/// where that is smaller: the rebuild of a
/// whole region (or of its groups, `clustered`) keeps the constant apart, but
/// `3·((r | 0x7fffffff) ^ u)` is `-3·u + (r & 2^31) + 0x7ffffffd`, one term only when
/// rebuilt with its constant.
fn join_constants(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| join_constants(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    join_constant(&node, w).unwrap_or(node)
}

fn join_constant(t: &T, w: &Ctx) -> Option<T> {
    let (mut terms, mut konst) = region_terms(t, w);
    // Constants also hide in complemented terms: `c·~B` is `-c·B - c`.
    for (c, y) in terms.iter_mut() {
        if let T::Op(Op::Not, a) = y {
            konst = konst.wrapping_sub(*c) & w.mask;
            *c = c.wrapping_neg() & w.mask;
            *y = a[0].clone();
        }
    }
    if konst == 0 || terms.len() < 2 {
        return None;
    }
    let groups = leaf_groups(terms, w);
    let n = groups.len();
    let joined = |s: &[usize]| {
        let mut leaves: Vec<u64> = s.iter().flat_map(|&i| groups[i].0.clone()).collect();
        leaves.sort_unstable();
        leaves.dedup();
        leaves.len()
    };
    let mut sets: Vec<Vec<usize>> = (0..n).map(|i| vec![i]).chain((0..n).flat_map(|i| (i + 1..n).map(move |j| vec![i, j]))).collect();
    let (most, most_two) = (max_leaves(), limit(Limit::JoinConstantsMaxLeaves));
    sets.retain(|s| joined(s) <= if s.len() == 1 { most } else { most_two });
    // Each rebuild searches a semi-linear region with a constant, which is slow.
    sets.sort_by_key(|s| joined(s));
    sets.truncate(limit(Limit::JoinConstantsMaxSets));
    let mut best = t.clone();
    for set in sets {
        let g: Vec<(u64, T)> = set.iter().flat_map(|&i| groups[i].1.clone()).collect();
        let others: Vec<(u64, T)> = (0..n).filter(|j| !set.contains(j)).flat_map(|j| groups[j].1.clone()).collect();
        let alt = T::Op(Op::Add, vec![build_sum(&others, 0, w), sub(sub_index("polish"), &build_sum(&g, konst, w), w)]);
        if size(&alt) < size(&best) {
            best = alt;
        }
    }
    (best != *t).then_some(best)
}

/// `t` with each bitwise region of 6 leaves written as its smallest `g(A) op h(B)`
/// (`decompose`), where that is smaller; `bool_expr` only splits up to `decompose_max_vars`
/// variables, since over 6 it takes milliseconds per table:
/// `(((y·s) | (2·v)) ^ ((s ^ w) & (v + t))) | (u & w)`.
pub(super) fn decompose_regions(t: &T, w: &Ctx, in_bit: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let bit = matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) && kind(t, w) == Kind::Bit;
    let node = T::Op(*op, a.iter().map(|x| decompose_regions(x, w, bit)).collect());
    if !bit || in_bit {
        return node;
    }
    let mut lv = Vec::new();
    leaves(&node, w, &mut lv);
    if lv.len() != 6 {
        return node;
    }
    let vars: Vec<T> = (0..6).map(|i| T::Var(format!("%d{i}"))).collect();
    let x = crate::lowbits::replace(&node, &lv, &vars);
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    let tt = (0..64usize).fold(0u64, |acc, p| {
        let env = |v: &str| if p >> v[2..].parse::<usize>().unwrap() & 1 == 1 { w.mask } else { 0 };
        acc | (crate::eval::eval(&x, ty, &env).unwrap_or(0) & 1) << p
    });
    let Some((_, b)) = decompose(tt, 6, usize::MAX, true, Dec::read()) else { return node };
    let r = b_to_t(&b, &lv);
    if size(&r) < size(&node) { r } else { node }
}

/// `t` with each linear region written as `factored_sum` of its terms where that is smaller:
/// the rules do not always gather `c·a + c·b` or absorb a constant `c` into a `c·~a`.
fn factor_regions(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| factor_regions(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    let (terms, konst) = region_terms(&node, w);
    let f = factored_sum(&terms, konst, w);
    if size(&f) < size(&node) { f } else { node }
}

/// Multiples of a shared leaf `join_linear` moves between two leaf groups; 0 rebuilds the
/// two groups as they are.
const MOVED_MULTIPLES: [i64; 7] = [0, 1, -1, 2, -2, 3, -3];

/// `t` with each linear region's smallest rebuild after moving `a·v` or `a·~v` from one leaf
/// group to another that also uses leaf `v` (and the region's constant into the first, or
/// not), also two such moves when the first adds at most `join_linear_near_slack` nodes:
/// the groups are rebuilt apart, and which group takes a shared leaf's linear part is not
/// known (each ordered pair of groups is rebuilt for every shared leaf and multiple);
/// `(s - (z & (y | s))) + z + (u ^ x ^ z)` is `((z & ~y) | s) + (u ^ x ^ z)`.
fn join_linear(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| join_linear(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    move_linear(&node, w).unwrap_or(node)
}

fn move_linear(t: &T, w: &Ctx) -> Option<T> {
    let (terms, konst) = region_terms(t, w);
    if terms.len() < 2 {
        return None;
    }
    let groups: Vec<Vec<(u64, T)>> = leaf_groups(terms, w).into_iter().map(|(_, g)| g).collect();
    let max_groups = limit(Limit::JoinLinearMaxGroups);
    if groups.len() > max_groups {
        return None;
    }
    let mut best = t.clone();
    let mut near = Vec::new();
    move_groups(&groups, konst, size(t), w, &mut best, Some(&mut near));
    near.sort_by_key(|(_, _, alt)| size(alt));
    for (groups, konst, alt) in near.into_iter().take(limit(Limit::JoinLinearNearMoves)) {
        move_groups(&groups, konst, size(t), w, &mut best, None);
        let (terms, konst) = region_terms(&alt, w);
        let regrouped: Vec<Vec<(u64, T)>> = leaf_groups(terms, w).into_iter().map(|(_, g)| g).collect();
        if regrouped.len() <= max_groups {
            move_groups(&regrouped, konst, size(t), w, &mut best, None);
        }
    }
    (best != *t).then_some(best)
}

/// A region's leaf groups, its constant kept apart, and their sum.
type Moved = (Vec<Vec<(u64, T)>>, u64, T);

/// `best` replaced by each smaller move between `groups`; with `near`, the moves (not the
/// plain rebuilds, `a = 0`) of at most `join_linear_near_slack` nodes more than `size0` are
/// collected there with the moved groups kept apart: grouping their sum again by leaves
/// can undo the move, or allow other moves.
fn move_groups(groups: &[Vec<(u64, T)>], konst: u64, size0: usize, w: &Ctx, best: &mut T, mut near: Option<&mut Vec<Moved>>) {
    let n = groups.len();
    let (slack, near_groups) = (limit(Limit::JoinLinearNearSlack), limit(Limit::JoinLinearMaxNearGroups));
    let leaf_terms: Vec<Vec<T>> = groups
        .iter()
        .map(|g| {
            let mut lv = Vec::new();
            g.iter().for_each(|(_, x)| leaves(x, w, &mut lv));
            lv
        })
        .collect();
    for i in 0..n {
        for j in (0..n).filter(|&j| j != i) {
            let shared = leaf_terms[j].iter().filter(|v| leaf_terms[i].contains(v));
            // `a·~v` moves the constant `-a` along with `-a·v`.
            let moved: Vec<T> = shared.into_iter().flat_map(|v| [v.clone(), T::Op(Op::Not, vec![v.clone()])]).collect();
            for v in &moved {
                for a in MOVED_MULTIPLES.into_iter().filter(|&a| a != 0 || !matches!(v, T::Op(Op::Not, _))) {
                    let a = a as u64 & w.mask;
                    let (mut gi, mut gj) = (groups[i].clone(), groups[j].clone());
                    if a != 0 {
                        gi.push((a, v.clone()));
                        gj.push((a.wrapping_neg() & w.mask, v.clone()));
                    }
                    let rj = sub(sub_index("polish"), &build_sum(&gj, 0, w), w);
                    let others: Vec<(u64, T)> = (0..n).filter(|&k| k != i && k != j).flat_map(|k| groups[k].clone()).collect();
                    for with_konst in [false, true] {
                        let (k_in, k_out) = if with_konst { (konst, 0) } else { (0, konst) };
                        let ri = sub(sub_index("polish"), &build_sum(&gi, k_in, w), w);
                        let mut all = others.clone();
                        all.extend([(1, ri.clone()), (1, rj.clone())]);
                        // A negative first term costs a `Neg`; later ones become `Sub`.
                        if let Some(p) = all.iter().position(|(c, _)| w.signed(*c) > 0) {
                            all[..=p].rotate_right(1);
                        }
                        let alt = build_sum(&all, k_out, w);
                        if size(&alt) < size(best) {
                            *best = alt;
                        } else if let Some(near) = near.as_deref_mut().filter(|_| a != 0 && n <= near_groups && size(&alt) <= size0.saturating_add(slack)) {
                            if !near.iter().any(|(_, _, x)| *x == alt) {
                                let mut moved: Vec<Vec<(u64, T)>> = (0..n).filter(|&k| k != i && k != j).map(|k| groups[k].clone()).collect();
                                moved.extend([vec![(1, ri)], vec![(1, rj.clone())]]);
                                near.push((moved, k_out, alt));
                            }
                        }
                    }
                }
            }
        }
    }
}

/// `t` rebuilt by cases of a variable shift amount `s` of `a << s`, when smaller and equal
/// to `t` in every case (the rebuild of their difference is 0). The candidates are the
/// rebuild with each such shift a fresh `2^K·v` (`K` = 1, 2), checked for `s = k < K`; for
/// `s = (b & (w-1))` or `~b`, also the rebuild of case `s = k` with `b` put back, checked
/// for every `k`. Case `k` sets the low bits of each `b` there, so other uses of `b` see
/// them: `(A | (~c & ((A << (c & 63)) & 1))) + y` is `A + y`.
fn shift_cases(t: &T, w: &Ctx) -> T {
    if size(t) > limit(Limit::ShiftCasesMaxSize) {
        return t.clone();
    }
    shift_cases_in(t, w, limit(Limit::ShiftCasesDepth))
}

fn shift_cases_in(t: &T, w: &Ctx, depth: usize) -> T {
    fn amounts(t: &T, out: &mut Vec<T>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Shl && !matches!(a[1], T::Num(_)) && !out.contains(&a[1]) {
            out.push(a[1].clone());
        }
        a.iter().for_each(|x| amounts(x, out));
    }
    fn wide(t: &T, s: &T, k: u32, tag: &str, fresh: &mut Vec<T>) -> T {
        let T::Op(op, a) = t else { return t.clone() };
        if *op == Op::Shl && a[1] == *s {
            let i = fresh.iter().position(|f| *f == a[0]).unwrap_or_else(|| {
                fresh.push(a[0].clone());
                fresh.len() - 1
            });
            return T::Op(Op::Mul, vec![T::Num(1 << k), T::Var(format!("{tag}{i}"))]);
        }
        T::Op(*op, a.iter().map(|x| wide(x, s, k, tag, fresh)).collect())
    }
    let once = |x: &T| sub(sub_index("shift_cases"), x, w);
    let rebuild = |x: &T| if depth > 1 { shift_cases_in(&once(x), w, depth - 1) } else { once(x) };
    let m = (w.w - 1) as i64;
    let tag = format!("%s{depth}_");
    let mut found = Vec::new();
    amounts(t, &mut found);
    let mut best = t.clone();
    for s in found.iter().take(2) {
        let var = match s {
            T::Op(Op::And, a) if a.contains(&T::Num(m)) => match a.iter().find(|x| **x != T::Num(m)) {
                Some(T::Op(Op::Not, b)) => Some((b[0].clone(), true)),
                Some(b) => Some((b.clone(), false)),
                None => None,
            },
            _ => None,
        };
        let set = |k: i64| {
            let (b, not) = var.as_ref().unwrap();
            let low = if *not { m - k } else { k };
            (b.clone(), T::Op(Op::Or, vec![T::Op(Op::And, vec![b.clone(), T::Num(!m)]), T::Num(low)]))
        };
        let case = |x: &T, k: i64| match &var {
            Some(_) => {
                let (v, e) = set(k);
                crate::lowbits::replace(x, &[v], &[e])
            }
            None => crate::lowbits::replace(x, std::slice::from_ref(s), &[T::Num(k)]),
        };
        let holds = |r: &T, k: i64| fold_consts(&rebuild_once(&T::Op(Op::Sub, vec![case(t, k), case(r, k)]), w), w) == T::Num(0);
        let mut tried = Vec::new();
        let mut candidates: Vec<(T, i64)> = Vec::new();
        for k in 1..=2u32 {
            let r = rebuild(&wide(t, s, k, &tag, &mut Vec::new()));
            if !has_var_prefix(&r, &tag) {
                candidates.push((r, k as i64));
            }
        }
        if var.is_some() {
            for k in [0, 1, m] {
                let (v, e) = set(k);
                let e2 = rebuild_once(&e, w);
                let r = crate::lowbits::replace(&rebuild(&case(t, k)), &[e, e2], &[v.clone(), v]);
                candidates.push((r, m + 1));
            }
        }
        for (r, cases) in candidates {
            if size(&r) >= size(&best) || tried.contains(&r) {
                continue;
            }
            tried.push(r.clone());
            if !(0..cases).any(|k| differs(&case(t, k), &case(&r, k), w)) && (0..cases).all(|k| holds(&r, k)) {
                best = r;
            }
        }
    }
    best
}

/// Whether `x` and `y` take different values at some of a few fixed points, read both as
/// unsigned and as signed, so that they differ in either type.
pub(super) fn differs(x: &T, y: &T, w: &Ctx) -> bool {
    let value = |v: &str, p: u64| {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        (v, p).hash(&mut h);
        h.finish()
    };
    [false, true].into_iter().all(|signed| {
        let ty = crate::eval::NumType { bits: w.w, signed };
        (0..4).any(|p| {
            let env = |v: &str| value(v, p);
            matches!((crate::eval::eval(x, ty, &env), crate::eval::eval(y, ty, &env)), (Some(a), Some(b)) if a != b)
        })
    })
}

fn has_var_prefix(t: &T, p: &str) -> bool {
    match t {
        T::Var(v) => v.starts_with(p),
        T::Op(_, a) => a.iter().any(|x| has_var_prefix(x, p)),
        _ => false,
    }
}

/// The smallest of `~t` and forms with the `~` moved inward: `~~a = a`, `~(a + K) = ~K - a`,
/// `~(a - K) = (K - 1) - a`, `~(K - a) = a + ~K`, De Morgan, `~(a ^ b) = ~a ^ b`.
pub(super) fn complement(t: &T, w: &Ctx) -> T {
    let not = |k: i64| w.signed(!(k as u64) & w.mask);
    let neg = |x: &T| T::Op(Op::Neg, vec![x.clone()]);
    let sub_from = |k: i64, x: &T| if w.signed(k as u64 & w.mask) == 0 { neg(x) } else { T::Op(Op::Sub, vec![T::Num(w.signed(k as u64 & w.mask)), x.clone()]) };
    let plain = T::Op(Op::Not, vec![t.clone()]);
    let c = match t {
        T::Num(k) => T::Num(not(*k)),
        T::Op(Op::Not, a) => a[0].clone(),
        T::Op(Op::Add, a) => match (&a[0], &a[1]) {
            (x, T::Num(k)) | (T::Num(k), x) => sub_from(not(*k), x),
            _ => plain.clone(),
        },
        T::Op(Op::Sub, a) => match (&a[0], &a[1]) {
            (x, T::Num(k)) => sub_from(k.wrapping_sub(1), x),
            (T::Num(k), x) if not(*k) == 0 => x.clone(),
            (T::Num(k), x) => T::Op(Op::Add, vec![x.clone(), T::Num(not(*k))]),
            _ => plain.clone(),
        },
        T::Op(op @ (Op::And | Op::Or), a) => {
            let dual = if *op == Op::And { Op::Or } else { Op::And };
            T::Op(dual, vec![complement(&a[0], w), complement(&a[1], w)])
        }
        T::Op(Op::Xor, a) => {
            let l = T::Op(Op::Xor, vec![complement(&a[0], w), a[1].clone()]);
            let r = T::Op(Op::Xor, vec![a[0].clone(), complement(&a[1], w)]);
            if size(&r) < size(&l) { r } else { l }
        }
        _ => plain.clone(),
    };
    if size(&c) < size(&plain) { c } else { plain }
}

/// `t` with `~x` written by `complement`, and `x + 1`, `x - -1` as `-~x`, wherever that is
/// smaller (`((a - 1) | b) + 1` is `-(-a & ~b)`).
fn push_not(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let t = T::Op(*op, a.iter().map(|x| push_not(x, w)).collect());
    let is = |k: i64, v: i64| (k as u64 ^ v as u64) & w.mask == 0;
    let r = match &t {
        T::Op(Op::Not, a) => complement(&a[0], w),
        T::Op(Op::Add, a) => match (&a[0], &a[1]) {
            (x, T::Num(k)) | (T::Num(k), x) if is(*k, 1) => T::Op(Op::Neg, vec![complement(x, w)]),
            _ => return t,
        },
        T::Op(Op::Sub, a) => match (&a[0], &a[1]) {
            (x, T::Num(k)) if is(*k, -1) => T::Op(Op::Neg, vec![complement(x, w)]),
            _ => return t,
        },
        _ => return t,
    };
    if size(&r) < size(&t) { r } else { t }
}


type Pass = (&'static str, fn(&T, &Ctx) -> T);

/// The polish passes by name, in their default order.
pub(crate) const POLISH: [Pass; 10] = [
    ("push_not", push_not),
    ("join_constants", |t, w| join_constants(t, w, false)),
    ("join_linear", |t, w| join_linear(t, w, false)),
    ("over_const_bitwise", over_const_bitwise),
    ("over_shared_bitwise", over_shared_bitwise),
    ("over_products", |t, w| crate::lowbits::over_products(t, w, |a| sub(sub_index("over_products"), a, w))),
    ("recombine", |t, w| if selectors(t, w).is_empty() { recombine_regions(t, w, false) } else { t.clone() }),
    ("shift_cases", shift_cases),
    ("decompose", |t, w| decompose_regions(t, w, false)),
    ("factor", |t, w| factor_regions(t, w, false)),
];

/// `crate::sched::polish` with the default passes on the egglog term `egg` of type `ty`.
pub fn polish(egg: &str, ty: crate::eval::NumType) -> String {
    crate::pipe::polish(egg, ty.bits, Some(ty.signed), &crate::sched::Passes::default()).0
}
