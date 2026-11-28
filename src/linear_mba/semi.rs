//! Semi-linear regions: per-bit tables, their groupings, and `bit_split`.

use super::*;

/// Semi-linear region: `e(x) = e(0) + Σ_j D_j(bit j of x)` with
/// `D_j(q) = e(q << j) - e(0)`, a multiple of `2^j`. `g_j = D_j >> j` only
/// matters modulo `2^(w-j)`, so bit `j` joins a group (found from the low bits
/// up) whose table agrees with `g_j` in its low `w-j` bits. Each group has mask `M`;
/// each group is rebuilt as a linear MBA `L` of the leaves and contributes
/// `L(x & M)`, i.e. `c·(b(x) & M)` per term `c·b`, plus `c·~M` when `b(0) = -1`.
/// Also tries `t - a·v`, added back as a term, for the leaf `v` and small `a`
/// that leave no more groups and the smallest table values: in
/// `((x ^ K) | C) + x` the bits of the bitwise term have tables 0, ±1, but the
/// `+ x` makes them 0, 1, 2.
pub(super) fn semi_linear(t: &T, lv: &[T], w: &Ctx, sub: &Sub) -> Option<T> {
    if lv.len() > w.semi_leaves() {
        return None;
    }
    let m = w.mask;
    let pts = 1usize << lv.len();
    let base: Vec<u64> = {
        let prog = Prog::new(t, lv, w);
        (0..w.w).flat_map(|j| prog.run_many(pts, |i, q| ((q >> i & 1) as u64) << j, w)).collect()
    };
    let (e0, all_groups) = groups_from(&|j, q| base[j as usize * pts + q], lv.len(), w)?;
    // Leaves that cancel out are dropped, so the shape search sees fewer leaves.
    let used: Vec<usize> = (0..lv.len())
        .filter(|&i| all_groups.iter().any(|(g, _)| (0..g.len()).any(|q| g[q] != g[q & !(1 << i)])))
        .collect();
    if used.is_empty() {
        return Some(T::Num(w.signed(e0)));
    }
    let project = |gs: Vec<(Vec<u64>, u64)>| -> Vec<(Vec<u64>, u64)> {
        let at = |q: usize| used.iter().enumerate().fold(0, |p, (j, &i)| p | (q >> j & 1) << i);
        gs.into_iter().map(|(g, mask)| ((0..1usize << used.len()).map(|q| g[at(q)]).collect(), mask)).collect()
    };
    let groups = project(all_groups);
    let full_lv = lv;
    let real: Vec<&T> = used.iter().map(|&i| &full_lv[i]).collect();
    let arith = real.iter().any(|l| kind(l, w) == Kind::Lin);
    // The search only needs each leaf's size, so it runs on slots: cheap to copy,
    // and the memoized searches repeat across regions with other leaves.
    let lv: &[T] = &real.iter().enumerate().map(|(i, l)| T::Op(Op::Slot(i as u32, size(l) as u32), Vec::new())).collect::<Vec<_>>();
    use crate::stats::optional;
    let mut cands = Vec::new();
    optional("semi_grouped", || semi_linear_candidates(&groups, lv, e0, w, &mut cands));
    let mut from = vec![(cands.len(), "semi_grouped")];
    let mut peels = Vec::new();
    let mut best: Option<((u64, u64), usize)> = None;
    for i in 0..lv.len() {
        for a in [1i64, -1, 2, -2, 3, -3] {
            let peeled = |j: u32, q: usize| base[j as usize * pts + q].wrapping_sub((a as u64).wrapping_mul(((q >> used[i] & 1) as u64) << j)) & m;
            let Some((e0, gs)) = groups_from(&peeled, full_lv.len(), w) else { continue };
            let gs = project(gs);
            let s = spread(&gs, w);
            if gs.len() <= groups.len() && s < best.map_or(spread(&groups, w), |b| b.0) {
                best = Some((s, peels.len()));
            }
            peels.push((i, a, e0, gs));
        }
    }
    let add = |c: T, i: usize, a: i64| build_sum(&[(1, c), (a as u64 & m, lv[i].clone())], 0, w);
    if let Some((_, k)) = best {
        let (i, a, e0, gs) = &peels[k];
        let mut sub = Vec::new();
        optional("semi_peel_grouped", || semi_linear_candidates(gs, lv, *e0, w, &mut sub));
        cands.extend(sub.into_iter().map(|c| add(c, *i, *a)));
    }
    from.push((cands.len(), "semi_peel_grouped"));
    // Leaves can be large, so each candidate's size is taken once.
    let (mut sized, mut limit) = (0, size(t));
    let mut smallest = |cands: &[T]| {
        limit = cands[sized..].iter().map(size).fold(limit, usize::min);
        sized = cands.len();
        limit
    };
    let limit = smallest(&cands);
    optional("semi_shapes", || shape_candidates(&groups, lv, e0, w, limit, &mut cands));
    from.push((cands.len(), "semi_shapes"));
    let limit = smallest(&cands);
    optional("semi_pairs", || pair_candidates(&groups, lv, e0, w, limit, &mut cands));
    from.push((cands.len(), "semi_pairs"));
    for (i, a, e0, gs) in &peels {
        let limit = smallest(&cands);
        let extra = size(&add(T::Num(1), *i, *a)) - 1;
        if limit > extra {
            let mut sub = Vec::new();
            optional("semi_peel_shapes", || shape_candidates(gs, lv, *e0, w, limit - extra, &mut sub));
            cands.extend(sub.into_iter().map(|c| add(c, *i, *a)));
        }
    }
    from.push((cands.len(), "semi_peel_shapes"));
    let limit = smallest(&cands);
    cands.extend(optional("semi_split", || semi_split(&groups, lv, e0, w, limit)));
    from.push((cands.len(), "semi_split"));
    let limit = smallest(&cands);
    cands.extend(optional("semi_scaled", || scaled(&groups, lv, e0, w, limit)));
    from.push((cands.len(), "semi_scaled"));
    let limit = smallest(&cands);
    cands.extend(optional("semi_bit_split", || bit_split(&groups, lv, arith, e0, w, limit, sub)));
    from.push((cands.len(), "semi_bit_split"));
    // Masks that differ only in bits that cannot matter tie on size; keep the short one.
    let i = (0..cands.len()).min_by_key(|&i| (size(&cands[i]), const_bits(&cands[i])))?;
    let source = |j: usize| from.iter().find(|(end, _)| j < *end).map_or("", |f| f.1);
    let won = (crate::stats::on() && size(&cands[i]) < size(t)).then(|| {
        let next = (0..cands.len()).filter(|&j| source(j) != source(i)).map(|j| size(&cands[j])).fold(size(t), usize::min);
        (source(i), next)
    });
    let best = cands.swap_remove(i);
    let r = fill_slots(&crate::stats::pass("semi_short_consts", &best, || short_consts(best.clone(), lv, w)), &real);
    if let Some((name, next)) = won {
        crate::stats::won(name, next, &r);
    }
    Some(r)
}

fn fill_slots(t: &T, lv: &[&T]) -> T {
    match t {
        T::Op(Op::Slot(i, _), _) => lv[*i as usize].clone(),
        T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill_slots(x, lv)).collect()),
        _ => t.clone(),
    }
}


/// A purely bitwise semi-linear region of 4 to 6 leaves as `P op Q`, `P` over the
/// leaves `A` and `Q` over `B` (they may share leaves, neither holds the other),
/// each rebuilt on its own: `(x0 ^ x3 ^ K1) & (x3 | K2 | (x5 & x6))`. Bits are grouped
/// by their Boolean function `f`; `P` and `Q` take its projections onto `A` and `B`
/// (`f(x & !onlyB)` and the rest for `^`), and bits with a constant `f` try each
/// pair of constants that gives it.
fn bit_split(groups: &[(Vec<u64>, u64)], lv: &[T], arith: bool, e0: u64, w: &Ctx, mut limit: usize, sub: &Sub) -> Vec<T> {
    let n = lv.len();
    // Arithmetic leaves are left to `relate`, which needs the rebuilt region's shape.
    if !(4..=6).contains(&n) || arith {
        return Vec::new();
    }
    if crate::lang::vars::get(crate::rust_vars::BIT_SPLIT_BUDGET) == 0 {
        w.read(|d| d.cut = true);
        return Vec::new();
    }
    let pts = 1usize << n;
    let all = if pts == 64 { u64::MAX } else { (1u64 << pts) - 1 };
    let mut funcs: Vec<(u64, u64)> = Vec::new();
    for (g, mask) in groups {
        for b in [0u64, 1] {
            let sub = mask & if b == 1 { e0 } else { !e0 } & w.mask;
            if sub == 0 {
                continue;
            }
            let rest = w.w - sub.trailing_zeros();
            let rm = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
            let mut table = 0u64;
            for (q, &v) in g.iter().enumerate() {
                let f = b.wrapping_add(v) & 1;
                if (f.wrapping_sub(b) ^ v) & rm != 0 {
                    return Vec::new();
                }
                table |= f << q;
            }
            match funcs.iter_mut().find(|(_, t)| *t == table) {
                Some(e) => e.0 |= sub,
                None => funcs.push((sub, table)),
            }
        }
    }
    let at = |t: u64, p: usize| t >> p & 1;
    // Points with leaf `i` set, as a table.
    let ones: Vec<u64> = (0..n).map(|i| (0..pts).filter(|p| p >> i & 1 == 1).fold(0, |m, p| m | 1 << p)).collect();
    let over = |mut t: u64, free: usize, any: bool| -> u64 {
        for i in (0..n).filter(|i| free >> i & 1 == 1) {
            let (hi, lo) = (t & ones[i], t & !ones[i] & all);
            let (up, down) = (lo << (1 << i), hi >> (1 << i));
            t = if any { t | up | down } else { (hi & up) | (lo & down) };
        }
        t
    };
    let zeroed = |mut t: u64, free: usize| -> u64 {
        for i in (0..n).filter(|i| free >> i & 1 == 1) {
            let lo = t & !ones[i] & all;
            t = lo | lo << (1 << i);
        }
        t
    };
    let split = |op: Op, t: u64, a: usize, b: usize| -> Option<(u64, u64)> {
        let (only_a, only_b) = (a & !b, b & !a);
        let (p, q) = match op {
            Op::And => (over(t, only_b, true), over(t, only_a, true)),
            Op::Or => (over(t, only_b, false), over(t, only_a, false)),
            _ => {
                let p = zeroed(t, only_b);
                (p, t ^ p)
            }
        };
        let ok = match op {
            Op::And => p & q == t,
            Op::Or => p | q == t,
            _ => zeroed(q, only_a) == q,
        };
        ok.then_some((p, q))
    };
    let const_pairs = |op: Op, f: u64| -> Vec<(u64, u64)> {
        match (op, f) {
            (Op::And, 0) => vec![(0, 0), (0, 1), (1, 0)],
            (Op::And, _) => vec![(1, 1)],
            (Op::Or, 0) => vec![(0, 0)],
            (Op::Or, _) => vec![(1, 1), (1, 0), (0, 1)],
            (_, 0) => vec![(0, 0), (1, 1)],
            _ => vec![(1, 0), (0, 1)],
        }
    };
    let full = pts - 1;
    // Variants 0-2 give constant bits each constant pair; 3 and 4 leave the side that
    // does not decide such bits (`q` in `1 | q`) the table of the widest other bits.
    let pick = |op: Op, a: usize, b: usize, v: usize| -> Option<(Vec<(u64, u64)>, Vec<(u64, u64)>)> {
        let mut split_all = Vec::new();
        for &(_, t) in &funcs {
            split_all.push(if t == 0 || t == all { None } else { Some(split(op, t, a, b)?) });
        }
        let widest = funcs.iter().zip(&split_all).filter_map(|((m, _), s)| s.map(|s| (m.count_ones(), s))).max_by_key(|x| x.0).map(|x| x.1);
        let (mut ps, mut qs, mut fresh) = (Vec::new(), Vec::new(), v == 0);
        for (&(mask, t), s) in funcs.iter().zip(&split_all) {
            let (p, q) = match s {
                Some(pq) => *pq,
                None => {
                    let pairs = const_pairs(op, t & 1);
                    let forced = pairs.len() == 3;
                    let (p, q) = match (v, widest) {
                        (0..3, _) => {
                            fresh |= v < pairs.len();
                            let (p, q) = pairs[v.min(pairs.len() - 1)];
                            (p * all, q * all)
                        }
                        (3, Some((_, wq))) if forced => {
                            fresh = true;
                            (pairs[1].0 * all, wq)
                        }
                        (4, Some((wp, _))) if forced => {
                            fresh = true;
                            (wp, pairs[2].1 * all)
                        }
                        _ => (pairs[0].0 * all, pairs[0].1 * all),
                    };
                    (p, q)
                }
            };
            let joined = match op {
                Op::And => p & q,
                Op::Or => p | q,
                _ => p ^ q,
            };
            if joined != t {
                return None;
            }
            ps.push((mask, p));
            qs.push((mask, q));
        }
        fresh.then_some((ps, qs))
    };
    let support = |parts: &[(u64, u64)]| -> u32 {
        let dep = (0..n).filter(|&i| parts.iter().any(|&(_, t)| (0..pts).any(|p| at(t, p) != at(t, p ^ 1 << i)))).count();
        let mut tables: Vec<u64> = parts.iter().map(|&(_, t)| t).filter(|&t| t != 0 && t != all).collect();
        tables.sort_unstable();
        tables.dedup();
        dep as u32 + tables.len() as u32
    };
    let mut found: Vec<(u32, Op, usize, usize, Vec<(u64, u64)>, Vec<(u64, u64)>)> = Vec::new();
    for code in 0..3usize.pow(n as u32) {
        let (mut a, mut b, mut c) = (0usize, 0usize, code);
        for i in 0..n {
            match c % 3 {
                0 => a |= 1 << i,
                1 => b |= 1 << i,
                _ => {
                    a |= 1 << i;
                    b |= 1 << i;
                }
            }
            c /= 3;
        }
        if a == full || b == full || a > b {
            continue;
        }
        for op in [Op::And, Op::Or, Op::Xor] {
            if let Some((ps, qs)) = pick(op, a, b, 0)
                && !found.iter().any(|f| f.1 == op && f.4 == ps && f.5 == qs)
            {
                found.push((support(&ps) + support(&qs), op, a, b, ps, qs));
            }
        }
    }
    found.sort_by_key(|f| f.0);
    let side = |parts: &[(u64, u64)], vars: usize| -> T {
        let terms: Vec<T> = parts
            .iter()
            .filter(|&&(_, t)| t != 0)
            .map(|&(mask, t)| {
                let k = T::Num(w.signed(mask));
                if t == all {
                    return k;
                }
                let minterms = (0..pts).filter(|&p| p & !vars == 0 && at(t, p) == 1).map(|p| {
                    (0..n)
                        .filter(|i| vars >> i & 1 == 1)
                        .map(|i| if p >> i & 1 == 1 { lv[i].clone() } else { T::Op(Op::Not, vec![lv[i].clone()]) })
                        .reduce(|x, y| T::Op(Op::And, vec![x, y]))
                        .unwrap()
                });
                T::Op(Op::And, vec![k, minterms.reduce(|x, y| T::Op(Op::Or, vec![x, y])).unwrap()])
            })
            .collect();
        terms.into_iter().reduce(|x, y| T::Op(Op::Or, vec![x, y])).unwrap_or(T::Num(0))
    };
    let mut out = Vec::new();
    // Each side has a leaf per leaf it depends on and a mask per table, so most
    // splits are ruled out by size before they are rebuilt.
    for &(low, op, a, b, ..) in found.iter().take(crate::rust_vars::limit(Limit::BitSplits)) {
        for (ps, qs) in (0..5).filter_map(|v| pick(op, a, b, v)) {
            if low as usize + 1 >= limit || !w.take_budget(crate::rust_vars::BIT_SPLIT_BUDGET) {
                return out;
            }
            let t = T::Op(op, vec![sub.term(&side(&ps, a), w), sub.term(&side(&qs, b), w)]);
            limit = limit.min(size(&t));
            out.push(t);
        }
    }
    out
}

/// When `e0` and every table value are multiples of `2^k`, the region is `2^k·L`.
/// `L` only matters modulo `2^(w-k)`, so it is rebuilt in that width, where bit
/// `j` has the table `g_j / 2^k` and bits `j ≥ w-k` are free:
/// `(-((z | y) | (x & 0xff00)) - z) << 5`.
pub(super) fn scaled(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let low_bits = |r: u32| if r == 64 { u64::MAX } else { (1u64 << r) - 1 };
    let mut k = if e0 == 0 { w.w } else { e0.trailing_zeros() };
    for (g, mask) in groups {
        let rest = low_bits(w.w - mask.trailing_zeros());
        k = g.iter().filter(|&&v| v & rest != 0).fold(k, |k, &v| k.min((v & rest).trailing_zeros()));
    }
    if k == 0 || k >= w.w || limit <= 3 {
        return None;
    }
    let nw = w.narrow(w.w - k);
    let gs: Vec<(Vec<u64>, u64)> = groups
        .iter()
        .filter(|(_, mask)| mask.trailing_zeros() < nw.w)
        .map(|(g, mask)| (g.iter().map(|&v| (w.signed(v) >> k) as u64 & nw.mask).collect(), mask & nw.mask))
        .collect();
    if gs.is_empty() {
        return None;
    }
    let e0 = e0 >> k;
    let mut cands = Vec::new();
    semi_linear_candidates(&gs, lv, e0, &nw, &mut cands);
    let inner = limit - 2;
    let limit = cands.iter().map(size).min().unwrap_or(inner).min(inner);
    shape_candidates(&gs, lv, e0, &nw, limit, &mut cands);
    let limit = cands.iter().map(size).min().unwrap_or(limit);
    cands.extend(semi_split(&gs, lv, e0, &nw, limit));
    let best = cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))?;
    Some(T::Op(Op::Mul, vec![T::Num(w.signed(1 << k)), short_consts(best, lv, &nw)]))
}

/// `t` with each constant replaced by the shortest sign- or zero-extension of its
/// low bits that leaves the function unchanged (`-0x7fffffffffffff6e` → `0x92`):
/// semi-linear terms are equal exactly when `e(0)` and every bit's table agree.
fn short_consts(t: T, lv: &[T], w: &Ctx) -> T {
    // `Prog` finds leaves by their context, which a rebuilt term may change, so
    // the leaves are replaced by placeholder variables first.
    let ph: Vec<T> = (0..lv.len()).map(|i| T::Var(format!("\u{4}{i}"))).collect();
    fn hide(t: &T, lv: &[T], ph: &[T]) -> T {
        if let Some(i) = lv.iter().position(|l| l == t) {
            return ph[i].clone();
        }
        match t {
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| hide(x, lv, ph)).collect()),
            _ => t.clone(),
        }
    }
    // Placeholders as the only variables, and no arithmetic under a bitwise operation.
    fn only_ph(t: &T, in_bit: bool) -> bool {
        match t {
            T::Var(v) => v.starts_with('\u{4}'),
            T::Num(_) => true,
            T::Op(op, a) => {
                let bit = matches!(op, Op::And | Op::Or | Op::Xor | Op::Not);
                (bit || !in_bit) && a.iter().all(|x| only_ph(x, bit))
            }
        }
    }
    fn show_leaves(t: &T, lv: &[T]) -> T {
        match t {
            T::Var(v) if v.starts_with('\u{4}') => lv[v[1..].parse::<usize>().unwrap()].clone(),
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| show_leaves(x, lv)).collect()),
            _ => t.clone(),
        }
    }
    let hidden = hide(&t, lv, &ph);
    if !only_ph(&hidden, false) {
        return t;
    }
    let Some(r) = short_consts_over(hidden, &ph, w) else { return t };
    show_leaves(&r, lv)
}

fn short_consts_over(t: T, lv: &[T], w: &Ctx) -> Option<T> {
    let reference = bit_groups(&t, lv, w)?;
    // Equal tables mean equal functions, so values at a few points rule out most
    // candidates before their tables are computed. A changed constant bit shows only
    // where the leaves have certain bits, so 2 points let through about a quarter.
    const SEEDS: [u64; 8] = [
        0x9e37_79b9_7f4a_7c15,
        0x6a09_e667_f3bc_c909,
        0xbb67_ae85_84ca_a73b,
        0x3c6e_f372_fe94_f82b,
        0xa54f_f53a_5f1d_36f1,
        0x510e_527f_ade6_82d1,
        0x9b05_688c_2b3e_6c1f,
        0x1f83_d9ab_fb41_bd6b,
    ];
    let probe = |t: &T| {
        let prog = Prog::new(t, lv, w);
        SEEDS.map(|s| prog.run(|i| s.wrapping_mul(2 * i as u64 + 1).rotate_left(i as u32 * 7), w) & w.mask)
    };
    let at_probes = probe(&t);
    let same = |cand: &T| probe(cand) == at_probes && bit_groups(cand, lv, w).as_ref() == Some(&reference);
    let mut t = t;
    let count = {
        fn n(t: &T) -> usize {
            match t {
                T::Num(_) => 1,
                T::Op(_, a) => a.iter().map(n).sum(),
                _ => 0,
            }
        }
        n(&t)
    };
    fn replace(t: &T, idx: &mut usize, target: usize, v: i64) -> T {
        match t {
            T::Num(_) => {
                *idx += 1;
                if *idx - 1 == target { T::Num(v) } else { t.clone() }
            }
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| replace(x, idx, target, v)).collect()),
            _ => t.clone(),
        }
    }
    fn nth(t: &T, idx: &mut usize, target: usize) -> Option<i64> {
        match t {
            T::Num(v) => {
                *idx += 1;
                (*idx - 1 == target).then_some(*v)
            }
            T::Op(_, a) => a.iter().find_map(|x| nth(x, idx, target)),
            _ => None,
        }
    }
    let large = |k: i64| w.signed(k as u64 & w.mask).unsigned_abs() >> (w.w / 2) != 0;
    // Bits that cancel between constants (`(w ^ K) - (z ^ K')` with the top bit in
    // both) only go away together, so first all large constants are cut at once.
    for b in 0..w.w {
        let low = if b + 1 >= 64 { u64::MAX } else { (1u64 << (b + 1)) - 1 };
        fn cut(t: &T, f: &dyn Fn(i64) -> i64) -> T {
            match t {
                T::Num(v) => T::Num(f(*v)),
                T::Op(op, a) => T::Op(*op, a.iter().map(|x| cut(x, f)).collect()),
                _ => t.clone(),
            }
        }
        let f = |v: i64| {
            let k = v as u64 & w.mask;
            if !large(v) {
                return v;
            }
            let sign = if k >> b & 1 == 1 { !low } else { 0 };
            w.signed((k & low | sign) & w.mask)
        };
        let cand = cut(&t, &f);
        if cand != t && same(&cand) {
            t = cand;
            break;
        }
    }
    for i in 0..count {
        let Some(k) = nth(&t, &mut 0, i) else { continue };
        if !large(k) {
            continue;
        }
        let k = k as u64 & w.mask;
        let mut options: Vec<i64> = (0..w.w)
            .flat_map(|b| {
                let low = if b + 1 >= 64 { u64::MAX } else { (1u64 << (b + 1)) - 1 };
                let sign = if k >> b & 1 == 1 { !low } else { 0 };
                [w.signed((k & low | sign) & w.mask), w.signed(k & low)]
            })
            .filter(|&v| v != w.signed(k))
            .collect();
        options.sort_by_key(|v| v.unsigned_abs());
        options.dedup();
        for v in options.into_iter().filter(|v| v.unsigned_abs() < w.signed(k).unsigned_abs()) {
            let cand = replace(&t, &mut 0, i, v);
            if same(&cand) {
                t = cand;
                break;
            }
        }
    }
    Some(t)
}

/// Smallest of the grouped and shape candidates for a semi-linear table.
fn semi_from_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let mut cands = Vec::new();
    semi_linear_candidates(groups, lv, e0, w, &mut cands);
    let limit = cands.iter().map(size).min().unwrap_or(limit).min(limit);
    shape_candidates(groups, lv, e0, w, limit, &mut cands);
    cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))
}

/// Leaves split into sets with no mixed difference in any bit's table, so each
/// table is the sum of its restrictions to the sets and each set is rebuilt on
/// its own: `(~w ^ 0x72) - 2*((v & 0x4bfa) | (x | 0xf))`. One set takes the rest of
/// `e(0)` so its shape can absorb it; each is tried in that role. The others take
/// either a constant their single term would have (`own_consts`) or the one their
/// own rebuild leaves.
pub(super) fn semi_split(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let n = lv.len();
    let mut root: Vec<usize> = (0..n).collect();
    fn find(root: &mut [usize], i: usize) -> usize {
        if root[i] != i {
            root[i] = find(root, root[i]);
        }
        root[i]
    }
    for (g, mask) in groups {
        let rest = w.w - mask.trailing_zeros();
        let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
        for i in 0..n {
            for j in i + 1..n {
                let (bi, bj) = (1usize << i, 1usize << j);
                let joined = (0..1usize << n).filter(|p| p & (bi | bj) == 0).any(|p| g[p | bi | bj].wrapping_sub(g[p | bi]).wrapping_sub(g[p | bj]).wrapping_add(g[p]) & low != 0);
                if joined {
                    let (ri, rj) = (find(&mut root, i), find(&mut root, j));
                    root[ri] = rj;
                }
            }
        }
    }
    let mut sets: Vec<Vec<usize>> = Vec::new();
    for i in 0..n {
        let r = find(&mut root, i);
        match sets.iter_mut().find(|s| find(&mut root, s[0]) == r) {
            Some(s) => s.push(i),
            None => sets.push(vec![i]),
        }
    }
    if sets.len() < 2 {
        return None;
    }
    let restrict = |set: &[usize]| -> Vec<(Vec<u64>, u64)> {
        let at = |q: usize| set.iter().enumerate().fold(0, |p, (j, &i)| p | (q >> j & 1) << i);
        let mut out: Vec<(Vec<u64>, u64)> = Vec::new();
        for (g, mask) in groups {
            let h: Vec<u64> = (0..1usize << set.len()).map(|q| g[at(q)]).collect();
            match out.iter_mut().find(|(o, _)| *o == h) {
                Some(o) => o.1 |= mask,
                None => out.push((h, *mask)),
            }
        }
        out.sort_by_key(|(_, mask)| mask.trailing_zeros());
        out
    };
    let parts: Vec<(Vec<(Vec<u64>, u64)>, Vec<T>)> = sets.iter().map(|s| (restrict(s), s.iter().map(|&i| lv[i].clone()).collect())).collect();
    let free: Vec<Option<T>> = parts.iter().map(|(gs, sl)| semi_from_groups(gs, sl, 0, w, limit)).collect();
    let mut best: Option<T> = None;
    let mut keep = |cand: T| {
        if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
            best = Some(cand);
        }
    };
    let own: Vec<Vec<u64>> = parts.iter().map(|(gs, _)| own_consts(gs, w)).collect();
    let mut memo: crate::eval::FastMap<(usize, u64), Option<T>> = Default::default();
    let max_combos = crate::rust_vars::limit(Limit::SemiSplitMaxCombos);
    for last in 0..parts.len() {
        let others: Vec<usize> = (0..parts.len()).filter(|&k| k != last).collect();
        if others.iter().any(|&k| own[k].is_empty()) || others.iter().map(|&k| own[k].len()).try_fold(1usize, |a, l| a.checked_mul(l)).is_none_or(|c| c > max_combos) {
            continue;
        }
        let mut choice = vec![0usize; others.len()];
        'combos: loop {
            let mut terms = Vec::new();
            let mut target = e0;
            for (a, &k) in others.iter().enumerate() {
                let kc = own[k][choice[a]];
                target = target.wrapping_sub(kc) & w.mask;
                let (gs, sl) = &parts[k];
                match memo.entry((k, kc)).or_insert_with(|| semi_from_groups(gs, sl, kc, w, limit)) {
                    Some(t) => terms.push((1, t.clone())),
                    None => terms.clear(),
                }
            }
            let (gs, sl) = &parts[last];
            if terms.len() == others.len() {
                if let Some(t) = memo.entry((last, target)).or_insert_with(|| semi_from_groups(gs, sl, target, w, limit)) {
                    terms.push((1, t.clone()));
                    keep(build_sum(&terms, 0, w));
                }
            }
            let mut a = 0;
            loop {
                if a == choice.len() {
                    break 'combos;
                }
                choice[a] += 1;
                if choice[a] < own[others[a]].len() {
                    break;
                }
                choice[a] = 0;
                a += 1;
            }
        }
    }
    for last in 0..parts.len() {
        // The other sets either keep their own constant, or drop it and pass it to `last`.
        for strip in [false, true] {
            let mut terms = Vec::new();
            let mut target = e0;
            for (k, f) in free.iter().enumerate().filter(|&(k, _)| k != last) {
                let (body, k) = if strip { split_const(f.as_ref()?, &parts[k].1, w) } else { (f.clone()?, 0) };
                target = target.wrapping_add(k) & w.mask;
                terms.push((1, body));
            }
            let (gs, sl) = &parts[last];
            let Some(t) = semi_from_groups(gs, sl, target, w, limit) else { continue };
            terms.push((1, t));
            keep(build_sum(&terms, 0, w));
        }
    }
    best
}

/// Constants a set could absorb if it were one term `c·B`: bit `j` of `B(0)` is
/// set where bit `j`'s table takes `-c`, and bits with a zero table, or one that
/// is both `c` and `-c` in its width, may go either way; `-c·~B` gives the same
/// table with `c` more.
fn own_consts(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<u64> {
    let m = w.mask;
    let Some(c) = groups.iter().flat_map(|(g, _)| g.iter().copied()).find(|&v| v != 0) else { return Vec::new() };
    let neg_c = c.wrapping_neg() & m;
    let (mut n, mut f, mut amb) = (0u64, 0u64, 0u64);
    for (g, mask) in groups {
        let rest = w.w - mask.trailing_zeros();
        let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
        let is = |v: u64, x: u64| (v ^ x) & low == 0;
        let (pos, neg) = (g.iter().any(|&v| !is(v, 0) && is(v, c)), g.iter().any(|&v| !is(v, 0) && is(v, neg_c)));
        if g.iter().any(|&v| !is(v, 0) && !is(v, c) && !is(v, neg_c)) {
            return Vec::new();
        }
        match (pos, neg) {
            (_, false) if !g.iter().any(|&v| !is(v, 0)) => f |= mask,
            (true, true) => amb |= mask,
            (false, true) => n |= mask,
            _ => {}
        }
    }
    // At bits with `c ≡ -c` in their width the table cannot tell, whatever group
    // they joined.
    let hi = m & !((1u64 << (w.w - 1 - c.trailing_zeros().min(w.w - 1))) - 1);
    amb = (amb | hi) & !f;
    n &= !amb;
    let mut out: Vec<u64> = [n, n | f, n | amb, n | f | amb]
        .into_iter()
        .flat_map(|b| [c.wrapping_mul(b) & m, c.wrapping_mul(b).wrapping_add(c) & m])
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// `(x, k)` with `t = x + k` for a trailing constant `k` of `t`, else `(t, 0)`; a leaf
/// `t` is kept whole.
fn split_const(t: &T, lv: &[T], w: &Ctx) -> (T, u64) {
    match t {
        _ if lv.contains(t) => (t.clone(), 0),
        T::Op(op, a) if *op == Op::Add => match (&a[0], &a[1]) {
            (x, T::Num(k)) | (T::Num(k), x) => (x.clone(), *k as u64 & w.mask),
            _ => (t.clone(), 0),
        },
        T::Op(op, a) if *op == Op::Sub => match &a[1] {
            T::Num(k) => (a[0].clone(), (*k as u64).wrapping_neg() & w.mask),
            _ => (t.clone(), 0),
        },
        _ => (t.clone(), 0),
    }
}

/// Largest table value in magnitude, then the sum of each group's largest.
pub(super) fn spread(groups: &[(Vec<u64>, u64)], w: &Ctx) -> (u64, u64) {
    let per_group = groups.iter().map(|(g, _)| g.iter().map(|&v| w.signed(v).unsigned_abs()).max().unwrap_or(0));
    (per_group.clone().max().unwrap_or(0), per_group.fold(0, u64::saturating_add))
}

/// `e(0)` and the bits of the semi-linear region `t` grouped by table, as
/// `(table, mask)`; `None` if `t` is not semi-linear.
fn bit_groups(t: &T, lv: &[T], w: &Ctx) -> Option<(u64, Vec<(Vec<u64>, u64)>)> {
    let prog = Prog::new(t, lv, w);
    let pts = 1usize << lv.len();
    let vals: Vec<u64> = (0..w.w).flat_map(|j| prog.run_many(pts, |i, q| ((q >> i & 1) as u64) << j, w)).collect();
    groups_from(&|j, q| vals[j as usize * pts + q], lv.len(), w)
}

/// `bit_groups` from `at(j, q)`, the value with leaf `i` set to bit `j` of `q >> i & 1`.
pub(super) fn groups_from(at: &dyn Fn(u32, usize) -> u64, n: usize, w: &Ctx) -> Option<(u64, Vec<(Vec<u64>, u64)>)> {
    let m = w.mask;
    let e0 = at(0, 0);
    let mut groups: Vec<(Vec<u64>, u64)> = Vec::new();
    for j in 0..w.w {
        let rest = w.w - j;
        let rest_mask = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
        let mut g = Vec::with_capacity(1 << n);
        for q in 0..1usize << n {
            let d = at(j, q).wrapping_sub(e0) & m;
            if d & ((1u64 << j) - 1) != 0 {
                return None;
            }
            let v = (d >> j) & rest_mask;
            let sign_fill = if v >> (rest - 1) & 1 == 1 { !rest_mask } else { 0 };
            g.push((v | sign_fill) & m);
        }
        let same = |rep: &[u64]| rep.iter().zip(&g).all(|(a, b)| (a ^ b) & rest_mask == 0);
        // A bit matching several groups starts its own; high_merges places it.
        let matching: Vec<usize> = (0..groups.len()).filter(|&i| same(&groups[i].0)).collect();
        match matching[..] {
            [i] => groups[i].1 |= 1 << j,
            _ => groups.push((g, 1 << j)),
        }
    }
    Some((e0, groups))
}

fn semi_linear_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
    let mut seen = crate::eval::FastSet::default();
    for groups in half_flips(groups, w) {
        for gs in high_merges(&groups, w) {
            let mut key: Vec<(Vec<u64>, u64)> = gs.clone();
            key.sort_unstable();
            if seen.insert(key) {
                grouped_candidates(&gs, lv, e0, w, cands);
            }
        }
    }
}

fn const_bits(t: &T) -> u32 {
    match t {
        T::Num(v) => 64 - v.unsigned_abs().leading_zeros(),
        T::Op(_, args) => args.iter().map(const_bits).sum(),
        _ => 0,
    }
}

/// The groups, plus variants with `-2^(r-1)` entries read as `+2^(r-1)`, for the
/// first `semi_half_flips` groups that have such entries (`r = w - j` for the group's lowest bit
/// `j`; both are the same value modulo `2^r`).
fn half_flips(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<Vec<(Vec<u64>, u64)>> {
    let mut out = vec![groups.to_vec()];
    let flippable = groups.iter().enumerate().filter_map(|(i, (g, mask))| {
        let rest = w.w - mask.trailing_zeros();
        let half = (1u64 << (rest - 1)).wrapping_neg() & w.mask;
        (rest > 1 && rest < w.w && g.contains(&half)).then_some((i, half))
    });
    for (i, half) in flippable.take(crate::rust_vars::limit(Limit::SemiHalfFlips)) {
        for v in out.clone() {
            let mut v = v;
            for x in v[i].0.iter_mut().filter(|x| **x == half) {
                *x = x.wrapping_neg() & w.mask;
            }
            out.push(v);
        }
    }
    out
}

/// The first smallest of `grouped_candidates_all`, memoized: callers only keep the first
/// smallest candidate, and semi-linear searches repeat the same groups.
fn grouped_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
    let key = (groups.to_vec(), lv.to_vec(), e0, w.w, crate::lang::vars::limits_key());
    let known = w.st.grouped.lock().unwrap().get(&key).cloned();
    if let Some(t) = known {
        cands.push(t);
        return;
    }
    let mut all = Vec::new();
    grouped_candidates_all(groups, lv, e0, w, &mut all);
    let Some(best) = all.into_iter().min_by_key(|c| (size(c), const_bits(c))) else { return };
    w.st.grouped.lock().unwrap().insert(key, best.clone());
    cands.push(best);
}

fn grouped_candidates_all(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
    let m = w.mask;
    let r = groups.len();
    cands.push(masked_groups(groups, lv, e0, w));
    single_leaf(groups, lv, e0, w, cands);
    let mut shifts = vec![vec![0; r]];
    for i in 0..r {
        if let Some(h) = solve_mul(groups[i].1, e0, w) {
            let mut hs = vec![0; r];
            hs[i] = h;
            shifts.push(hs);
        }
    }
    cands.extend(const_leaf_groups(groups, &shifts, lv, e0, w));
    // Bits with the same table can still differ in their share of the constant,
    // as in `(y | 0x36) ^ 0x627c`. For `e0 = s·E`, split the groups by the bits
    // of `E` and give the groups inside `E` the shift `s`.
    let mut scales: Vec<u64> = vec![1, m];
    for (g, _) in groups {
        scales.extend(g.iter().filter(|&&v| v != 0).flat_map(|&v| [v, v.wrapping_neg() & m]));
    }
    scales.sort_unstable();
    scales.dedup();
    for s in scales {
        let Some(e) = solve_mul(s, e0, w) else { continue };
        let refined: Vec<(Vec<u64>, u64)> = groups
            .iter()
            .flat_map(|(g, mask)| [(g.clone(), mask & e), (g.clone(), mask & !e)])
            .filter(|(_, mask)| *mask != 0)
            .collect();
        let hs: Vec<u64> = refined.iter().map(|(_, mask)| if mask & e != 0 { s } else { 0 }).collect();
        cands.extend(const_leaf_groups(&refined, &[hs], lv, e0, w));
    }
}

/// When every table depends on one leaf `y` only and takes the values 0 and ±c,
/// the region is `e0 + c·(y & P) - c·(y & N)`, which is `c·((y & M) ^ K) + r`
/// with `M = P | N`, `K = N | Z` for any `Z` outside `M`, and `r = e0 - c·K`.
fn single_leaf(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
    let m = w.mask;
    let Some(i) = (0..lv.len()).find(|&i| groups.iter().all(|(g, _)| g.iter().enumerate().all(|(q, &v)| v == g[q & 1 << i]))) else {
        return;
    };
    let vals: Vec<(u64, u64)> = groups.iter().map(|(g, mask)| (g[1 << i], *mask)).filter(|&(v, _)| v != 0).collect();
    let Some(&(c, _)) = vals.first() else { return };
    let neg_c = c.wrapping_neg() & m;
    if vals.iter().any(|&(v, _)| v != c && v != neg_c) {
        return;
    }
    let mask_of = |c: u64| vals.iter().filter(|&&(v, _)| v == c).fold(0u64, |acc, &(_, k)| acc | k);
    let (p, n) = (mask_of(c), mask_of(neg_c));
    let free = m & !(p | n);
    let y = &lv[i];
    // Bits where `c ≡ -c` in their width may count on either side.
    let hi = m & !((1u64 << (w.w - 1 - c.trailing_zeros().min(w.w - 1))) - 1) & (p | n);
    let sides = [(c, p, n), (neg_c, n, p)];
    for (c, p, n) in sides.into_iter().flat_map(|(c, p, n)| [(c, p, n), (c, p | hi, n & !hi), (c, p & !hi, n | hi)]) {
        let mask = p | n;
        let mut zs = vec![0, free];
        if let Some(h) = solve_mul(c, e0.wrapping_sub(c.wrapping_mul(n)) & m, w) {
            zs.extend([h, h & free]);
        }
        zs.sort_unstable();
        zs.dedup();
        for z in zs.into_iter().filter(|z| z & !free == 0) {
            let k = n | z;
            let mut inner = if mask == m { y.clone() } else { T::Op(Op::And, vec![y.clone(), T::Num(w.signed(mask))]) };
            if k != 0 {
                inner = T::Op(Op::Xor, vec![inner, T::Num(w.signed(k))]);
            }
            let rest = e0.wrapping_sub(c.wrapping_mul(k)) & m;
            cands.push(build_sum(&[(c, inner)], rest, w));
        }
    }
}

/// The ways to merge each group that agrees with several lower-starting groups into
/// one of them. A group whose lowest bit is `j` only matters modulo `2^(w-j)`, so
/// it can take the table of any such group; which one lets the constant fold in
/// depends on the constant, as for bit 7 of `3*(y ^ 0x61)` in u8.
fn high_merges(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<Vec<(Vec<u64>, u64)>> {
    let r = groups.len();
    let low = |i: usize| groups[i].1.trailing_zeros();
    let options: Vec<Vec<usize>> = (0..r)
        .map(|i| {
            let rest = w.w - low(i);
            let rest_mask = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
            (0..r)
                .filter(|&k| low(k) < low(i))
                .filter(|&k| groups[k].0.iter().zip(&groups[i].0).all(|(a, b)| (a ^ b) & rest_mask == 0))
                .collect()
        })
        .collect();
    let mut ambiguous: Vec<usize> = (0..r).filter(|&i| !options[i].is_empty()).collect();
    ambiguous.sort_by_key(|&i| low(i));
    // Enumerate at most `semi_max_merges` variants; the other groups join the group holding
    // the bit just below them.
    let most = crate::rust_vars::limit(Limit::SemiMaxMerges);
    let mut count = 1usize;
    let take = ambiguous
        .iter()
        .take_while(|&&i| {
            count = count.saturating_mul(options[i].len());
            count <= most
        })
        .count();
    let fixed = ambiguous.split_off(take);
    let mut base: Vec<usize> = (0..r).collect();
    for &i in &fixed {
        let below = options[i].iter().copied().find(|&k| groups[k].1 >> (low(i) - 1) & 1 == 1);
        base[i] = below.unwrap_or(options[i][0]);
    }
    let mut out = Vec::new();
    let mut choice = vec![0usize; ambiguous.len()];
    loop {
        let mut target = base.clone();
        for (a, &i) in ambiguous.iter().enumerate() {
            target[i] = options[i][choice[a]];
        }
        // Targets start strictly lower, so following them ends.
        let root = |mut i: usize| {
            while target[i] != i {
                i = target[i];
            }
            i
        };
        let gs = (0..r)
            .filter(|&i| target[i] == i)
            .map(|i| {
                let mask = (0..r).filter(|&k| root(k) == i).fold(0u64, |acc, k| acc | groups[k].1);
                (groups[i].0.clone(), mask)
            })
            .collect();
        out.push(gs);
        let mut a = 0;
        while a < choice.len() {
            choice[a] += 1;
            if choice[a] < options[ambiguous[a]].len() {
                break;
            }
            choice[a] = 0;
            a += 1;
        }
        if a == choice.len() {
            return out;
        }
    }
}

/// `e0 + Σ_group L_group(x & M)`, with `L_group` the linear MBA of the group's table.
fn masked_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx) -> T {
    let m = w.mask;
    let mut terms = Vec::new();
    let mut konst = e0;
    let zero_env: Vec<(T, u64)> = lv.iter().map(|l| (l.clone(), 0)).collect();
    for (g, mask) in groups.iter().filter(|(g, _)| g.iter().any(|&v| v != 0)) {
        let (ts, k) = rebuild_gp(g, lv, 0, w);
        konst = konst.wrapping_add(k) & m;
        for (c, b) in ts {
            if *mask == m {
                terms.push((c, b));
                continue;
            }
            if eval(&b, w, &zero_env) != 0 {
                konst = konst.wrapping_add(c.wrapping_mul(!mask)) & m;
            }
            terms.push((c, T::Op(Op::And, vec![b, T::Num(w.signed(*mask))])));
        }
    }
    build_sum(&terms, konst, w)
}

/// Give each group a binary code and add one constant leaf `k_b` per code bit,
/// holding the bits of the groups whose code has bit `b`. Then bit `j` of the
/// region is `table(bits_j(x), code of j's group)`, a linear MBA of `x` and the
/// constant leaves, so `(y & ~K) - (y & K) + K` can come back as `y ^ K`.
/// Tried for every code assignment of at most `semi_max_code_groups` groups. Part of the constant
/// `e0` can also move into the table: adding `shifts[i]` to group `i`'s table
/// adds `shifts[i]·M_i` to the region, so `-2*(x & ~K) - 2*K` can come back as
/// `-2*(x | K)`.
fn const_leaf_groups(groups: &[(Vec<u64>, u64)], shifts: &[Vec<u64>], lv: &[T], e0: u64, w: &Ctx) -> Vec<T> {
    let (n, r) = (lv.len(), groups.len());
    let p = (usize::BITS - (r - 1).leading_zeros()) as usize;
    if r < 2 || r > crate::rust_vars::limit(Limit::SemiMaxCodeGroups) || n + p > max_leaves() {
        return Vec::new();
    }
    let m = w.mask;
    let mut out = Vec::new();
    for codes in permutations(r) {
        let mut leaves = lv.to_vec();
        for b in 0..p {
            let mask = (0..r).filter(|&i| codes[i] >> b & 1 == 1).fold(0u64, |acc, i| acc | groups[i].1);
            leaves.push(T::Num(w.signed(mask)));
        }
        // The group with code 0 sits at table point 0, which must stay 0.
        for hs in shifts.iter().filter(|hs| (0..r).all(|i| codes[i] != 0 || hs[i] == 0)) {
            let mut table = vec![0u64; 1 << (n + p)];
            let mut k0 = e0;
            for (i, (g, mask)) in groups.iter().enumerate() {
                for (q, &v) in g.iter().enumerate() {
                    table[q | codes[i] << n] = v.wrapping_add(hs[i]) & m;
                }
                k0 = k0.wrapping_sub(hs[i].wrapping_mul(*mask)) & m;
            }
            let (terms, mut konst) = rebuild_gp(&table, &leaves, k0, w);
            let mut kept = Vec::new();
            for (c, t) in terms {
                match fold_consts(&t, w) {
                    T::Num(v) => konst = konst.wrapping_add(c.wrapping_mul(v as u64)) & m,
                    t => kept.push((c, t)),
                }
            }
            out.push(build_sum(&kept, konst, w));
        }
    }
    out
}

/// The `h` of smallest magnitude with `h·mask = e0` in the word, if any.
pub(super) fn solve_mul(mask: u64, e0: u64, w: &Ctx) -> Option<u64> {
    let tz = mask.trailing_zeros();
    if e0 == 0 || tz >= w.w || e0 & ((1u64 << tz) - 1) != 0 {
        return None;
    }
    let odd = mask >> tz;
    // Inverse of an odd number modulo 2^64 by Newton's iteration.
    let mut inv = odd;
    for _ in 0..6 {
        inv = inv.wrapping_mul(2u64.wrapping_sub(odd.wrapping_mul(inv)));
    }
    let rest = w.w - tz;
    let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
    let h = (e0 >> tz).wrapping_mul(inv) & low;
    // h + i·2^rest are all solutions; take the one closest to 0.
    let h = if rest < 64 && h >> (rest - 1) & 1 == 1 { h | !low } else { h };
    Some(h & w.mask)
}

fn permutations(r: usize) -> Vec<Vec<usize>> {
    if r == 0 {
        return vec![Vec::new()];
    }
    let mut out = Vec::new();
    for rest in permutations(r - 1) {
        for pos in 0..=rest.len() {
            let mut p = rest.clone();
            p.insert(pos, r - 1);
            out.push(p);
        }
    }
    out
}

/// Evaluate bitwise and additive operations whose operands are all constants.
pub(super) fn fold_consts(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if !matches!(op, Op::And | Op::Or | Op::Xor | Op::Not | Op::Add | Op::Sub | Op::Neg) {
        return t.clone();
    }
    let a: Vec<T> = a.iter().map(|x| fold_consts(x, w)).collect();
    let t = T::Op(*op, a);
    match &t {
        T::Op(_, a) if a.iter().all(|x| matches!(x, T::Num(_))) => T::Num(w.signed(eval(&t, w, &[]))),
        _ => t,
    }
}
