//! Rebuilding a linear region from its values on {0,1}^n.

use super::*;

/// `simba` memoized per thread, for the linear cofactors `poly_mba` rebuilds: the same
/// ones come back across its factoring choices and across regions.
pub(crate) fn simba_memo(t: &T, w: &Ctx) -> Option<T> {
    let key = (w.w, t.clone());
    let f = || crate::builtin_passes::run_alt(&crate::passes::current().simba, t, w, true);
    if let Some(r) = memo_get(&w.st.simba_memo, &key, w, "simba", f) {
        return r;
    }
    memo_compute(&w.st.simba_memo, key, w, f)
}

/// Smallest rebuilt form of the linear region `t` (`Passes::simba`).
pub(super) fn simba(t: &T, w: &Ctx) -> Option<T> {
    crate::builtin_passes::run_alt(&crate::passes::current().simba, t, w, false)
}

/// The leaves of the linear region `t` and, when asked for, its values on {0,1}^n, kept
/// for the last region asked about on this thread: the methods of `simba` each need them.
struct RegionValues {
    t: T,
    w: u32,
    lv: std::rc::Rc<Vec<T>>,
    vals: Option<std::rc::Rc<Vec<u64>>>,
}

thread_local! {
    static LAST_REGION: std::cell::RefCell<Option<RegionValues>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn region_leaves(t: &T, w: &Ctx) -> std::rc::Rc<Vec<T>> {
    LAST_REGION.with(|c| {
        let mut c = c.borrow_mut();
        match c.as_ref() {
            Some(r) if r.w == w.w && r.t == *t => r.lv.clone(),
            _ => {
                let mut lv = Vec::new();
                leaves(t, w, &mut lv);
                let lv = std::rc::Rc::new(lv);
                *c = Some(RegionValues { t: t.clone(), w: w.w, lv: lv.clone(), vals: None });
                lv
            }
        }
    })
}

fn region_values(t: &T, w: &Ctx) -> (std::rc::Rc<Vec<T>>, std::rc::Rc<Vec<u64>>) {
    let lv = region_leaves(t, w);
    if let Some(v) = LAST_REGION.with(|c| c.borrow().as_ref().and_then(|r| r.vals.clone())) {
        return (lv, v);
    }
    let prog = Prog::new(t, &lv, w);
    let vals = std::rc::Rc::new((0..1usize << lv.len()).map(|p| prog.at(p, w)).collect::<Vec<u64>>());
    LAST_REGION.with(|c| {
        if let Some(r) = c.borrow_mut().as_mut().filter(|r| r.w == w.w && r.t == *t) {
            r.vals = Some(vals.clone());
        }
    });
    (lv, vals)
}

/// The methods of `simba` on the region `t`, as passes (`TERM_PASSES`).
pub(super) fn drop_unused_pass(t: &T, w: &Ctx) -> Option<T> {
    drop_unused(t, &region_leaves(t, w), w)
}
pub(super) fn semi_linear_pass(t: &T, w: &Ctx) -> Option<T> {
    semi_linear(t, &region_leaves(t, w), w)
}
pub(super) fn rebuild_values_pass(t: &T, w: &Ctx) -> Option<T> {
    let (lv, vals) = region_values(t, w);
    Some(rebuild_values(&vals, &lv, w))
}
pub(super) fn common_multiple_pass(t: &T, w: &Ctx) -> Option<T> {
    let (lv, vals) = region_values(t, w);
    common_multiple(&vals, &lv, w)
}
pub(super) fn related_leaves_pass(t: &T, w: &Ctx) -> Option<T> {
    related_leaves(t, &region_leaves(t, w), w)
}
pub(super) fn one_wide_term_pass(t: &T, w: &Ctx) -> Option<T> {
    let (lv, vals) = region_values(t, w);
    one_wide_term(&vals, &lv, w)
}

/// `c·B + k` for values that take two values only, `B` split by `decompose` past the
/// `decompose_max_vars` leaves where `bool_expr` stops: `(g | b | a) & (c ^ f ^ (a | e))`.
fn one_wide_term(vals: &[u64], lv: &[T], w: &Ctx) -> Option<T> {
    let n = lv.len();
    let dec = Dec::read();
    if n <= dec.max_vars {
        return None;
    }
    let k = vals[0];
    let c = vals.iter().find(|&&v| v != k)?.wrapping_sub(k) & w.mask;
    if vals.iter().any(|&v| v != k && v.wrapping_sub(k) & w.mask != c) {
        return None;
    }
    let tt = (0..vals.len()).filter(|&p| vals[p] != k).fold(0u64, |t, p| t | 1 << p);
    let (_, b) = decompose(tt, n, usize::MAX, true, dec)?;
    Some(build_sum(&[(c, b_to_t(&b, lv))], k, w))
}

/// `c·(v_1 + ... + v_k) + L` for leaves whose own coefficients are within 1 of `c = ±2^k`
/// (a shifted sum), `L` rebuilt from the rest (`8*(y + z) + ((z ^ x) - x)` for `8*y + 9*z - 2*(z & x)`).
fn common_multiple(vals: &[u64], lv: &[T], w: &Ctx) -> Option<T> {
    let n = lv.len();
    let a: Vec<u64> = (0..n).map(|i| vals[1 << i].wrapping_sub(vals[0]) & w.mask).collect();
    let near = |x: u64, c: u64| w.signed(x.wrapping_sub(c) & w.mask).unsigned_abs() <= 1;
    let (min, tries) = (limit(Limit::CommonMultipleMin) as u64, limit(Limit::CommonMultipleTries));
    let mut tried = Vec::new();
    let mut best: Option<T> = None;
    for c in a.iter().flat_map(|&x| [x, x.wrapping_add(1), x.wrapping_sub(1)].map(|c| c & w.mask)) {
        if w.signed(c).unsigned_abs() < min || !w.signed(c).unsigned_abs().is_power_of_two() || tried.contains(&c) || tried.len() == tries {
            continue;
        }
        let s: Vec<usize> = (0..n).filter(|&j| near(a[j], c)).collect();
        if s.len() < 2 {
            continue;
        }
        tried.push(c);
        let smask = s.iter().fold(0usize, |m, &j| m | 1 << j);
        let rest: Vec<u64> = (0..vals.len()).map(|p| vals[p].wrapping_sub(c.wrapping_mul((p & smask).count_ones() as u64)) & w.mask).collect();
        let sum = s.iter().map(|&j| lv[j].clone()).reduce(|x, y| T::Op(Op::Add, vec![x, y])).unwrap();
        let prod = T::Op(Op::Mul, vec![T::Num(w.signed(c)), sum]);
        let cand = match rebuild_values(&rest, lv, w) {
            T::Num(0) => prod,
            r => T::Op(Op::Add, vec![prod, r]),
        };
        if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
            best = Some(cand);
        }
    }
    best
}

/// The linear MBA over `lv` with values `vals` on {0,1}^n. When every value is a
/// multiple of `2^k`, `±2^k·L` with `L` rebuilt from `±vals / 2^k` is also tried, as in
/// `2*x - 4*(x & y) = 2*((x ^ y) - y)`; `L` only matters modulo `2^(w-k)`.
pub(super) fn rebuild_values(vals: &[u64], lv: &[T], w: &Ctx) -> T {
    let plain = rebuild_values_plain(vals, lv, w);
    let k = vals.iter().map(|v| v.trailing_zeros()).min().unwrap_or(64);
    if k == 0 || k >= w.w {
        return plain;
    }
    let low: Vec<u64> = vals.iter().map(|&v| (w.signed(v) >> k) as u64 & w.mask).collect();
    let neg: Vec<u64> = low.iter().map(|v| v.wrapping_neg() & w.mask).collect();
    [(1i64 << k, &low), (-1i64 << k, &neg)]
        .into_iter()
        .map(|(c, l)| T::Op(Op::Mul, vec![T::Num(w.signed(c as u64 & w.mask)), rebuild_values_plain(l, lv, w)]))
        .fold(plain, |best, t| if size(&t) < size(&best) { t } else { best })
}

fn rebuild_values_plain(vals: &[u64], lv: &[T], w: &Ctx) -> T {
    let m = w.mask;
    // e(x) = Σ_j 2^j g(bit j of x), with g(p) = e(p) - 2e(0); k = g(0).
    let g: Vec<u64> = vals.iter().map(|v| v.wrapping_sub(vals[0].wrapping_mul(2)) & m).collect();
    let k = g[0];
    let gp: Vec<u64> = g.iter().map(|v| v.wrapping_sub(k) & m).collect();
    let (terms, konst) = rebuild_gp(&gp, lv, k.wrapping_neg() & m, w);
    build_sum(&terms, konst, w)
}

/// Shortest `(terms, konst')` with `konst + Σ_j 2^j gp(bit j of x) = Σ terms + konst'`,
/// where `gp(0) = 0` and table point `p` sets leaf `i` to bit `i` of `p`.
pub(super) fn rebuild_gp(gp: &[u64], lv: &[T], mut konst: u64, w: &Ctx) -> (Vec<(u64, T)>, u64) {
    let mut terms = Vec::new();
    for group in independent_groups(gp, lv.len(), w) {
        let sub: Vec<u64> = (0..1usize << group.len())
            .map(|q| gp[group.iter().enumerate().filter(|(j, _)| q >> j & 1 == 1).fold(0, |p, (_, &i)| p | 1 << i)])
            .collect();
        let sub_lv: Vec<T> = group.iter().map(|&i| lv[i].clone()).collect();
        let (ts, k) = rebuild_table(&sub, &sub_lv, konst, w);
        terms.extend(ts);
        konst = k;
    }
    (terms, konst)
}

/// Split the variables into groups with no interaction in `gp`, so that
/// `gp(p) = Σ_group gp(p ∩ group)`: a mixed difference
/// `gp(p+i+j) - gp(p+i) - gp(p+j) + gp(p)` that is non-zero anywhere joins `i` and `j`.
fn independent_groups(gp: &[u64], n: usize, w: &Ctx) -> Vec<Vec<usize>> {
    let mut root: Vec<usize> = (0..n).collect();
    fn find(root: &mut [usize], i: usize) -> usize {
        if root[i] != i {
            root[i] = find(root, root[i]);
        }
        root[i]
    }
    for i in 0..n {
        for j in i + 1..n {
            let (bi, bj) = (1usize << i, 1usize << j);
            let joined = (0..1usize << n).filter(|p| p & (bi | bj) == 0).any(|p| {
                gp[p | bi | bj].wrapping_sub(gp[p | bi]).wrapping_sub(gp[p | bj]).wrapping_add(gp[p]) & w.mask != 0
            });
            if joined {
                let (ri, rj) = (find(&mut root, i), find(&mut root, j));
                root[ri] = rj;
            }
        }
    }
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for i in 0..n {
        let r = find(&mut root, i);
        match groups.iter_mut().find(|g| find(&mut root, g[0]) == r) {
            Some(g) => g.push(i),
            None => groups.push(vec![i]),
        }
    }
    groups
}

/// Shortest `(terms, konst')` with `konst + Σ_j 2^j gp(bit j of x) = Σ terms + konst'`.
fn rebuild_table(gp: &[u64], lv: &[T], konst: u64, w: &Ctx) -> (Vec<(u64, T)>, u64) {
    // The result depends on a leaf only through its size and whether it is a `~`
    // (`build_sum` strips one), so the cache is keyed on those and the leaves become
    // one-node placeholders (`Op::LeafOperand` for the operand of a `~` leaf) whose sizes
    // `rebuild_table_uncached` takes from `shape`.
    let shape: Vec<(usize, bool)> = lv.iter().map(|l| (size(l), matches!(l, T::Op(op, _) if *op == Op::Not))).collect();
    let key = (gp.to_vec(), shape, konst, w.w, crate::lang::vars::limits_key());
    fn fill(t: &T, lv: &[T]) -> T {
        match t {
            T::Op(Op::Leaf(i), _) => lv[*i].clone(),
            T::Op(Op::LeafOperand(i), _) => match &lv[*i] {
                T::Op(_, a) => a[0].clone(),
                _ => unreachable!("only a `~` leaf has an operand placeholder"),
            },
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill(x, lv)).collect()),
            _ => t.clone(),
        }
    }
    let filled = |r: &(Vec<(u64, T)>, u64)| (r.0.iter().map(|(c, t)| (*c, fill(t, lv))).collect(), r.1);
    let known = w.st.rebuilt.lock().unwrap().get(&key).map(filled);
    if let Some(r) = known {
        return r;
    }
    let ph: Vec<T> = key
        .1
        .iter()
        .enumerate()
        .map(|(i, &(_, not))| match not {
            true => T::Op(Op::Not, vec![T::Op(Op::LeafOperand(i), Vec::new())]),
            false => T::Op(Op::Leaf(i), Vec::new()),
        })
        .collect();
    let r = rebuild_table_uncached(gp, &ph, &key.1, konst, w);
    let out = filled(&r);
    w.st.rebuilt.lock().unwrap().insert(key, r);
    out
}

fn rebuild_table_uncached(gp: &[u64], lv: &[T], shape: &[(usize, bool)], konst: u64, w: &Ctx) -> (Vec<(u64, T)>, u64) {
    fn ph_size(t: &T, shape: &[(usize, bool)]) -> usize {
        match t {
            T::Op(Op::Leaf(i), _) => shape[*i].0,
            T::Op(Op::LeafOperand(i), _) => shape[*i].0 - 1,
            T::Op(_, a) => 1 + a.iter().map(|x| ph_size(x, shape)).sum::<usize>(),
            _ => 1,
        }
    }
    let sum_size = |ts: &[(u64, T)], k: u64, w: &Ctx| {
        let terms: Vec<(u64, usize, bool)> = ts.iter().map(|(c, t)| (*c, ph_size(t, shape), matches!(t, T::Op(op, _) if *op == Op::Not))).collect();
        folded_sum_size(&terms, k, w)
    };
    let n = lv.len();
    let pts = 1usize << n;
    let m = w.mask;
    let dec = Dec::read();
    let mut cands: Vec<(Vec<(u64, T)>, u64)> = Vec::new();
    // Leaves with their own coefficient, then one term per remaining value. A leaf
    // with coefficient 0 would repeat the subset without it.
    for subset in (0..1usize << n).filter(|s| (0..n).all(|i| s >> i & 1 == 0 || gp[1 << i] != 0)) {
        let mut terms = Vec::new();
        let mut r = gp.to_vec();
        for i in (0..n).filter(|i| subset >> i & 1 == 1) {
            let c = gp[1 << i];
            terms.push((c, lv[i].clone()));
            for (p, rv) in r.iter_mut().enumerate() {
                if p >> i & 1 == 1 {
                    *rv = rv.wrapping_sub(c) & m;
                }
            }
        }
        let mut distinct: Vec<u64> = r.iter().copied().filter(|&u| u != 0).collect();
        distinct.sort_unstable();
        distinct.dedup();
        for u in distinct {
            let tt = (0..pts).filter(|&p| r[p] == u).fold(0u64, |acc, p| acc | 1 << p);
            let BE::E(_, b) = bool_expr_with(tt, n, dec) else {
                unreachable!("r[0] == 0, so the table is neither empty nor full")
            };
            terms.push((u, b_to_t(&b, lv)));
        }
        cands.push((terms, konst));
    }
    cands.extend(overlapping_terms(gp, lv, konst, w));
    cands
        .into_iter()
        .min_by_key(|(ts, k)| sum_size(ts, *k, w))
        .unwrap()
}

/// Up to `overlap_max_terms` bitwise terms whose supports may overlap (`11*(x^y) - x`), possibly
/// non-zero at 0 (`-23*~(x|y)`). Shifting the table by `d` gives
/// `h = gp + d = Σ c_j·b_j` per bit, and then `e = Σ c_j·b_j(x) + konst + d`,
/// since a per-bit constant `d` is the word `-d`. `d` is tried as 0 or `-v`
/// for a value `v` of `gp`, i.e. `h` is zero where `gp` is `v`.
pub(super) fn overlapping_terms(gp: &[u64], lv: &[T], konst: u64, w: &Ctx) -> Vec<(Vec<(u64, T)>, u64)> {
    let m = w.mask;
    let distinct = |t: &[u64]| {
        let mut v: Vec<u64> = t.iter().copied().filter(|&u| u != 0).collect();
        v.sort_unstable();
        v.dedup();
        v
    };
    let (most, choices, dec) = (limit(Limit::OverlapMaxValues), limit(Limit::OverlapMaxChoices), Dec::read());
    let max_terms = limit(Limit::OverlapMaxTerms);
    let vals = distinct(gp);
    if vals.len() > most {
        return Vec::new();
    }
    let mut out = Vec::new();
    let offsets = std::iter::once(0).chain(vals.iter().map(|&v| v.wrapping_neg() & m));
    for d in offsets {
        let h: Vec<u64> = gp.iter().map(|v| v.wrapping_add(d) & m).collect();
        let hv = distinct(&h);
        if hv.len() > most {
            continue;
        }
        let mut pool = hv.clone();
        for &a in &hv {
            for &b in &hv {
                pool.push(a.wrapping_sub(b) & m);
            }
        }
        pool.retain(|&c| c != 0);
        pool.sort_unstable();
        pool.dedup();
        for k in (1..=max_terms).filter(|k| hv.len() < 1 << k) {
            // Past k = 2 a repeated coefficient leaves ambiguous points (rejected) or two equal terms.
            combinations(&pool, k, k == 2, &mut Vec::new(), &mut |coefs| {
                if let Some(c) = split_by_sums(&h, &hv, coefs, lv, konst.wrapping_add(d) & m, (choices, dec), w) {
                    out.push(c);
                }
            });
        }
    }
    out
}

/// `f` on `prefix` followed by each `k`-element multiset of `pool` (sets unless `repeat`),
/// in pool order.
pub(super) fn combinations(pool: &[u64], k: usize, repeat: bool, prefix: &mut Vec<u64>, f: &mut dyn FnMut(&[u64])) {
    if k == 0 {
        return f(prefix);
    }
    for i in 0..pool.len() {
        prefix.push(pool[i]);
        combinations(&pool[i + usize::from(!repeat)..], k - 1, repeat, prefix, f);
        prefix.pop();
    }
}

/// Write `h` as `Σ coefs[j]·b_j`, where each point's value is the sum of the
/// coefficients of the `b_j` that are 1 there. With two terms a point can only
/// be ambiguous when `c1 + c2 = 0` (as in `(y ^ k) - k`); such points are
/// resolved in up to `choices` ways and the shortest result wins.
/// With three terms ambiguity is common and too costly to resolve, so it fails.
fn split_by_sums(h: &[u64], h_vals: &[u64], coefs: &[u64], lv: &[T], konst: u64, (choices, dec): (usize, Dec), w: &Ctx) -> Option<(Vec<(u64, T)>, u64)> {
    let m = w.mask;
    let k = coefs.len();
    let sums: Vec<u64> = (0..1usize << k)
        .map(|s| (0..k).filter(|j| s >> j & 1 == 1).fold(0u64, |acc, j| acc.wrapping_add(coefs[j])) & m)
        .collect();
    if !h_vals.iter().all(|v| sums.contains(v)) {
        return None;
    }
    let options: Vec<Vec<usize>> = h.iter().map(|&v| (0..sums.len()).filter(|&s| sums[s] == v).collect()).collect();
    if options.iter().any(|o| o.is_empty()) {
        return None;
    }
    let ambiguous: Vec<usize> = (0..h.len()).filter(|&p| options[p].len() > 1).collect();
    if k > 2 && !ambiguous.is_empty() {
        return None;
    }
    let ways = ambiguous.iter().try_fold(1usize, |acc, &p| acc.checked_mul(options[p].len())).unwrap_or(usize::MAX);
    let mut best: Option<(Vec<(u64, T)>, u64)> = None;
    'ways: for mut way in 0..ways.min(choices) {
        let mut choice: Vec<usize> = options.iter().map(|o| o[0]).collect();
        for &p in &ambiguous {
            choice[p] = options[p][way % options[p].len()];
            way /= options[p].len();
        }
        let mut tts = vec![0u64; k];
        for (p, &s) in choice.iter().enumerate() {
            for (j, tt) in tts.iter_mut().enumerate() {
                if s >> j & 1 == 1 {
                    *tt |= 1 << p;
                }
            }
        }
        let mut terms = Vec::new();
        let mut kk = konst;
        for (j, &tt) in tts.iter().enumerate() {
            match bool_expr_with(tt, lv.len(), dec) {
                BE::Zero => continue 'ways,
                // All ones in every bit is the word -1.
                BE::Ones => kk = kk.wrapping_sub(coefs[j]) & m,
                BE::E(_, b) => terms.push((coefs[j], b_to_t(&b, lv))),
            }
        }
        if best.as_ref().is_none_or(|(bt, bk)| sum_size(&terms, kk, w) < sum_size(bt, *bk, w)) {
            best = Some((terms, kk));
        }
    }
    best
}
