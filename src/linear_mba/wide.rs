//! Regions of more than `MAX_LEAVES` leaves: unused leaves, `peel`, `small_blocks`, `wide_blocks` and `clustered`.

use super::*;

/// Most leaves `drop_unused` evaluates a region on.
pub(super) const MAX_WIDE_LEAVES: usize = 16;
/// Most instructions times points `drop_unused` runs.
const WIDE_BUDGET: usize = 1 << 25;

/// A region with more than `MAX_LEAVES` leaves, rewritten with the leaves its values on
/// {0,1}^n do not depend on set to 0, as in opaque predicates over many variables.
pub(super) fn drop_unused(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
    if has_const_bitwise(t, w) {
        return None;
    }
    drop_leaves(t, lv, w)
}

/// `drop_unused` for any region; with constant masks only where `relate` has cancelled leaves,
/// since elsewhere the rebuilds of the operands do better.
pub(super) fn drop_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
    let n = lv.len();
    let (e0, used) = used_leaves(t, lv, w)?;
    let unused: Vec<T> = (0..n).filter(|&i| !used[i]).map(|i| lv[i].clone()).collect();
    if unused.is_empty() {
        return None;
    }
    if unused.len() == n {
        return Some(T::Num(w.signed(e0)));
    }
    // Leaves are found as `Prog` finds them: the first subterm equal to one, anywhere.
    fn zero(t: &T, lv: &[T], unused: &[T]) -> T {
        match t {
            _ if unused.contains(t) => T::Num(0),
            _ if lv.contains(t) => t.clone(),
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| zero(x, lv, unused)).collect()),
            _ => t.clone(),
        }
    }
    let z = zero(t, lv, &unused);
    if z == *t {
        return None;
    }
    Some(rewrite(&z, w)).filter(|r| size(r) < size(t))
}

/// `e(0)` and the leaves the region's value depends on, from its values on {0,1}^n,
/// or per bit position for a semi-linear region (see `semi_linear`); `None` past
/// `MAX_WIDE_LEAVES` leaves or `WIDE_BUDGET`.
pub(super) fn used_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<(u64, Vec<bool>)> {
    let n = lv.len();
    let (e0, _, tables) = bit_tables(t, lv, w)?;
    let used = (0..n).map(|i| tables.iter().any(|g| (0..g.len()).any(|q| g[q] != g[q & !(1 << i)]))).collect();
    Some((e0, used))
}

/// `e(0)`, the table index of each bit position, and the tables `g_j(q)` with
/// `e(q·2^j) = e(0) + 2^j·g_j(q)`, taken modulo `2^(w-j)` for every bit `j` that shares
/// table `g_b` with a lower `b`; `None` past `MAX_WIDE_LEAVES` leaves or `WIDE_BUDGET`.
fn bit_tables(t: &T, lv: &[T], w: &Ctx) -> Option<(u64, Vec<usize>, Vec<Vec<u64>>)> {
    let n = lv.len();
    if n > MAX_WIDE_LEAVES {
        return None;
    }
    // Bit `j`'s table agrees modulo `2^(w-j)` with that of any lower bit with the same bits
    // of every mask, so only the lowest bit of each such column is evaluated.
    fn masks(t: &T, lv: &[T], out: &mut Vec<u64>) {
        if let T::Op(op, a) = t
            && !lv.contains(t)
        {
            for x in a {
                match x {
                    T::Num(c) if matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) => out.push(*c as u64),
                    _ => masks(x, lv, out),
                }
            }
        }
    }
    let mut ks = Vec::new();
    masks(t, lv, &mut ks);
    let mut bits: Vec<u32> = Vec::new();
    let columns: Vec<Vec<bool>> = (0..w.w).map(|j| ks.iter().map(|k| k >> j & 1 == 1).collect()).collect();
    let column = |j: u32| &columns[j as usize];
    for j in 0..if ks.is_empty() { 1 } else { w.w } {
        if bits.iter().all(|&b| column(b) != column(j)) {
            bits.push(j);
        }
    }
    let prog = Prog::new(t, lv, w);
    if (prog.0.len() * bits.len()) << n > WIDE_BUDGET {
        return None;
    }
    let e0 = prog.at(0, w);
    let mut tables: Vec<Vec<u64>> = Vec::new();
    for &j in &bits {
        let mut g = Vec::with_capacity(1 << n);
        for q in 0..1usize << n {
            let d = prog.run(|i| ((q >> i & 1) as u64) << j, w).wrapping_sub(e0) & w.mask;
            if d & ((1u64 << j) - 1) != 0 {
                return None;
            }
            g.push(d >> j);
        }
        tables.push(g);
    }
    let col = (0..w.w).map(|j| bits.iter().position(|&b| column(b) == column(j)).unwrap_or(0)).collect();
    Some((e0, col, tables))
}

/// Least size per leaf of a region `peel` tries.
const MIN_PEEL_SIZE: usize = 16;

/// A region with more than `MAX_LEAVES` leaves whose value is a bitwise function of its
/// leaves, with one leaf `v` that is not arithmetic peeled off: `v | r`, `~v & r` or `v ^ r`
/// with `r` the region at `v = 0`, or `v & r`, `~v | r` with `r` at `v = -1`; `r` is
/// rebuilt by `simba`, which peels again until few enough leaves are left.
pub(super) fn peel(t: &T, w: &Ctx) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let n = lv.len();
    // Small regions seldom rebuild smaller, but the rest costs a full semi-linear search.
    if !(MAX_LEAVES + 1..=MAX_WIDE_LEAVES).contains(&n) || size(t) < MIN_PEEL_SIZE * n || w.st.peel_depth.load(Relaxed) >= MAX_WIDE_LEAVES - MAX_LEAVES {
        return None;
    }
    // Most regions fail; at points of 0s and 1s a bitwise value differs from e(0) in bit 0 only.
    let prog = Prog::new(t, &lv, w);
    let e0 = prog.at(0, w);
    let mut h = 0x9e37_79b9_7f4a_7c15u64;
    let spread = (0..16).map(|_| {
        h ^= h << 13;
        h ^= h >> 7;
        h ^= h << 17;
        h as usize & ((1 << n) - 1)
    });
    if !(0..n).map(|i| 1 << i).chain(spread).all(|q| prog.at(q, w) ^ e0 <= 1) {
        return None;
    }
    let (e0, col, tables) = bit_tables(t, &lv, w)?;
    // Bit j of the value is f_j(bits j of the leaves) when every f_j(q) is 0 or 1.
    let mut fs: Vec<Vec<bool>> = Vec::new();
    for j in 0..w.w {
        let m = w.mask >> j;
        let e0j = e0 >> j & 1;
        let mut f = Vec::with_capacity(1 << n);
        for &g in &tables[col[j as usize]] {
            match g.wrapping_add(e0j) & m {
                0 => f.push(false),
                1 => f.push(true),
                _ => return None,
            }
        }
        if !fs.contains(&f) {
            fs.push(f);
        }
    }
    // `p(f at v = 0, f at v = 1)` for every point and table.
    let all = |i: usize, p: &dyn Fn(bool, bool) -> bool| fs.iter().all(|f| (0..1usize << n).filter(|q| q >> i & 1 == 0).all(|q| p(f[q], f[q | 1 << i])));
    let not = |x: T| T::Op(Op::Not, vec![x]);
    // Arithmetic leaves are left to `relate`, which rebuilds them too. A leaf the tables do
    // not depend on can have no occurrence `Prog` sees (only inside an arithmetic leaf).
    for i in (0..n).filter(|&i| kind(&lv[i], w) != Kind::Lin && !all(i, &|lo, hi| lo == hi)) {
        // (operation, complement v, value substituted for v)
        let how = if all(i, &|_, hi| hi) {
            (Op::Or, false, 0)
        } else if all(i, &|_, hi| !hi) {
            (Op::And, true, 0)
        } else if all(i, &|lo, hi| lo != hi) {
            (Op::Xor, false, 0)
        } else if all(i, &|lo, _| !lo) {
            (Op::And, false, -1)
        } else if all(i, &|lo, _| lo) {
            (Op::Or, true, -1)
        } else {
            continue;
        };
        // Leaves are found as `Prog` finds them: the first subterm equal to one, anywhere.
        fn put(t: &T, lv: &[T], v: &T, k: i64) -> T {
            match t {
                _ if t == v => T::Num(k),
                _ if lv.contains(t) => t.clone(),
                T::Op(op, a) => T::Op(*op, a.iter().map(|x| put(x, lv, v, k)).collect()),
                _ => t.clone(),
            }
        }
        let rest = put(t, &lv, &lv[i], how.2);
        w.st.peel_depth.fetch_add(1, Relaxed);
        let rest = simba(&rest, w).unwrap_or(rest);
        w.st.peel_depth.fetch_sub(1, Relaxed);
        let v = if how.1 { not(lv[i].clone()) } else { lv[i].clone() };
        return Some(T::Op(how.0, vec![v, rest])).filter(|r| size(r) < size(t));
    }
    None
}

/// Most leaves `small_blocks` handles.
const MAX_BLOCK_LEAVES: usize = 12;

/// Upper bound on the degree of `t`'s conjunction-basis expansion: the most leaves
/// any bitwise subterm of the linear region has.
fn bit_degree(t: &T, w: &Ctx) -> usize {
    match t {
        T::Num(_) => 0,
        T::Op(_, a) if kind(t, w) == Kind::Lin => {
            a.iter().map(|x| bit_degree(x, w)).max().unwrap_or(0)
        }
        _ => {
            let mut lv = Vec::new();
            leaves(t, w, &mut lv);
            lv.len()
        }
    }
}

/// Most combinations of block choices `small_blocks` tries exhaustively.
const MAX_BLOCK_COMBOS: usize = 1 << 15;

/// Rebuild a linear region from its conjunction-basis expansion when every maximal
/// set of leaves with a non-zero coefficient (a block) has at most 3 leaves: one
/// term `c·f` per block, with `f` any bitwise function of the block's leaves and `c`
/// set by the block's top coefficient, plus the lower-degree monomials still left
/// over. The choice per block that gives the smallest sum wins, so `c·(x & y)` may
/// come back as `x + y - (x | y)` or `-(x ^ y)` when the single terms absorb the rest.
/// Not limited to `MAX_LEAVES`.
pub(super) fn small_blocks(t: &T, w: &Ctx) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let n = lv.len();
    if !(2..=MAX_BLOCK_LEAVES).contains(&n) || has_const_bitwise(t, w) {
        return None;
    }
    let m = w.mask;
    // Blocks of at most 3 leaves mean degree <= 3, so the coefficients come from the
    // points with at most 3 ones; the other points must then match the interpolation.
    let pts: Vec<usize> = (0..1usize << n).filter(|p| p.count_ones() <= 3).collect();
    let prog = Prog::new(t, &lv, w);
    let mut coef = vec![0u64; 1 << n];
    for &p in &pts {
        coef[p] = prog.at(p, w);
    }
    for i in 0..n {
        for &p in &pts {
            if p >> i & 1 == 1 {
                coef[p] = coef[p].wrapping_sub(coef[p ^ 1 << i]) & m;
            }
        }
    }
    let low: Vec<usize> = pts.iter().copied().filter(|&p| coef[p] != 0).collect();
    if bit_degree(t, w) > 3 {
        let fits = |p: usize| prog.at(p, w) == low.iter().filter(|&&q| q & p == q).fold(0u64, |a, &q| a.wrapping_add(coef[q])) & m;
        // Most regions fail; a few spread-out points reject them before the full check.
        let mut h = 0x9e37_79b9_7f4a_7c15u64;
        let spread = (0..8).map(|_| {
            h ^= h << 13;
            h ^= h >> 7;
            h ^= h << 17;
            h as usize & ((1 << n) - 1)
        });
        if !spread.chain(0..1 << n).filter(|p| p.count_ones() > 3).all(fits) {
            return None;
        }
    }
    let support: Vec<usize> = low.into_iter().filter(|&p| p != 0).collect();
    let blocks: Vec<usize> = support.iter().copied().filter(|&p| p.count_ones() >= 2 && !support.iter().any(|&q| q != p && q & p == p)).collect();
    if blocks.is_empty() || blocks.iter().any(|b| b.count_ones() > 3) {
        return None;
    }
    // Leaves can be large subterms, so sums are built over placeholder variables
    // and measured with each placeholder counting as its leaf's size.
    let ph: Vec<T> = (0..n).map(|i| T::Var(format!("\u{1}{i}"))).collect();
    let leaf_size: Vec<usize> = lv.iter().map(size).collect();
    let wsize = |t: &T| placeholder_size(t, &ph, &leaf_size);
    // Per block: (c, c·f, monomials f adds besides the block's own, c·f(0)).
    let candidates = |s: usize| {
        let vars: Vec<usize> = (0..n).filter(|i| s >> i & 1 == 1).collect();
        let (bits, full) = (vars.len(), (1usize << vars.len()) - 1);
        let global = |q: usize| (0..bits).filter(|j| q >> j & 1 == 1).fold(0, |acc, j| acc | 1 << vars[j]);
        let mut out = Vec::new();
        for tt in 1..(1u64 << (1 << bits)) - 1 {
            let mut a: Vec<u64> = (0..=full).map(|q| tt >> q & 1).collect();
            for j in 0..bits {
                for q in 0..=full {
                    if q >> j & 1 == 1 {
                        a[q] = a[q].wrapping_sub(a[q ^ 1 << j]);
                    }
                }
            }
            let Some(c) = solve_mul(a[full] & m, coef[s], w) else { continue };
            let BE::E(_, b) = bool_expr_canon(tt, vars.len()) else { continue };
            let adds: Vec<(usize, u64)> = (1..full).map(|q| (global(q), c.wrapping_mul(a[q]) & m)).filter(|&(_, v)| v != 0).collect();
            out.push((c, b_to_t_at(&b, &vars, &ph), adds, c.wrapping_mul(a[0]) & m));
        }
        out.sort_by_key(|o| wsize(&o.1));
        out
    };
    let opts: Vec<_> = blocks.iter().map(|&s| candidates(s)).collect();
    if opts.iter().any(|o| o.is_empty()) {
        return None;
    }
    let build = |choice: &[usize]| {
        let mut rest: std::collections::BTreeMap<usize, u64> = support.iter().filter(|p| !blocks.contains(p)).map(|&p| (p, coef[p])).collect();
        let mut terms = Vec::new();
        let mut konst = coef[0];
        for (o, &ci) in opts.iter().zip(choice) {
            let (c, term, adds, k0) = &o[ci];
            for &(q, v) in adds {
                let e = rest.entry(q).or_insert(0);
                *e = e.wrapping_sub(v) & m;
            }
            konst = konst.wrapping_add(*k0) & m;
            terms.push((*c, term.clone()));
        }
        for (q, c) in rest.into_iter().filter(|&(_, c)| c != 0) {
            let conj = (0..n).filter(|i| q >> i & 1 == 1).map(|i| ph[i].clone()).reduce(|a, b| T::Op(Op::And, vec![a, b])).unwrap();
            terms.push((c, conj));
        }
        build_sum(&terms, konst, w)
    };
    // `wsize(&build(choice))` from sizes alone: the leftover monomials in `build`'s key order.
    let mut keys: Vec<usize> = support.iter().copied().filter(|p| !blocks.contains(p)).collect();
    keys.extend(opts.iter().flatten().flat_map(|o| o.2.iter().map(|a| a.0)));
    keys.sort_unstable();
    keys.dedup();
    let base: Vec<u64> = keys.iter().map(|&q| if support.contains(&q) && !blocks.contains(&q) { coef[q] } else { 0 }).collect();
    let conj_size: Vec<usize> = keys.iter().map(|&q| (0..n).filter(|i| q >> i & 1 == 1).map(|i| leaf_size[i]).sum::<usize>() + q.count_ones() as usize - 1).collect();
    #[allow(clippy::type_complexity)]
    let sized: Vec<Vec<(u64, usize, bool, Vec<(usize, u64)>, u64)>> = opts
        .iter()
        .map(|o| {
            o.iter()
                .map(|(c, term, adds, k0)| {
                    let adds = adds.iter().map(|&(q, v)| (keys.binary_search(&q).unwrap(), v)).collect();
                    (*c, wsize(term), matches!(term, T::Op(Op::Not, _)), adds, *k0)
                })
                .collect()
        })
        .collect();
    let score = |choice: &[usize]| -> usize {
        let mut vals = base.clone();
        let mut konst = coef[0];
        let mut terms: Vec<(u64, usize, bool)> = Vec::with_capacity(choice.len() + keys.len());
        for (o, &ci) in sized.iter().zip(choice) {
            let (c, s, not, adds, k0) = &o[ci];
            for &(q, v) in adds {
                vals[q] = vals[q].wrapping_sub(v) & m;
            }
            konst = konst.wrapping_add(*k0) & m;
            terms.push((*c, *s, *not));
        }
        terms.extend(vals.iter().zip(&conj_size).filter(|(v, _)| **v != 0).map(|(&v, &s)| (v, s, false)));
        folded_sum_size(&terms, konst, w)
    };
    let mut choice = vec![0usize; blocks.len()];
    let mut best_choice = choice.clone();
    let mut best_size = score(&choice);
    // Blocks that share leaves can need to change together (`2*~(a|c) + 2*(e & (c|d))`),
    // so few enough combinations are all tried; otherwise coordinate descent.
    let combos = opts.iter().try_fold(1usize, |acc, o| acc.checked_mul(o.len())).unwrap_or(usize::MAX);
    if combos <= MAX_BLOCK_COMBOS {
        let mut c = vec![0usize; blocks.len()];
        'all: loop {
            let cs = score(&c);
            if cs < best_size {
                (best_choice, best_size) = (c.clone(), cs);
            }
            for (e, o) in opts.iter().enumerate() {
                c[e] += 1;
                if c[e] < o.len() {
                    continue 'all;
                }
                c[e] = 0;
            }
            break;
        }
    }
    for _ in 0..if combos <= MAX_BLOCK_COMBOS { 0 } else { 4 } {
        let mut improved = false;
        for e in 0..blocks.len() {
            for ci in 0..opts[e].len() {
                let mut c = choice.clone();
                c[e] = ci;
                let cs = score(&c);
                if cs < best_size {
                    (best_choice, best_size, improved) = (c.clone(), cs, true);
                    choice = c;
                }
            }
        }
        if !improved {
            break;
        }
    }
    let best = build(&best_choice);
    debug_assert_eq!(wsize(&best), best_size);
    (best_size < size(t)).then(|| fill_placeholders(&best, &ph, &lv))
}

/// Most leaves of one term `wide_blocks` expands, and of one block it rebuilds as one term.
const MAX_TERM_LEAVES: usize = 10;
const MAX_WIDE_BLOCK: usize = 10;
/// Search steps `wide_blocks` spends per block and multiplier, most tables it collects per
/// block, and most of the smallest it keeps for the search over blocks.
const BLOCK_STEPS: usize = 1 << 12;
const MAX_BLOCK_TABLES: usize = 4096;
const MAX_BLOCK_FUNCTIONS: usize = 64;
/// Most tables of a block of more than 6 leaves `wide_blocks` tries.
const MAX_WIDE_TABLES: usize = 16;
/// Most regions `wide_blocks` remembers.
const MAX_WIDE_CACHE: usize = 4096;

/// One choice for a block of `wide_blocks`: `c·term`, its size, whether `term` is a `Not`,
/// and what it adds at each leftover key.
#[derive(Clone)]
struct BlockTerm {
    c: u64,
    term: T,
    size: usize,
    not: bool,
    adds: Vec<(usize, u64)>,
}

/// A linear region of more than `MAX_LEAVES` leaves rebuilt from its conjunction-basis
/// expansion (summed over its terms, each expanded over its own leaves): one term `c·f` per
/// block (maximal leaf set with a non-zero coefficient), with `f` matching the coefficient
/// of every set of two or more leaves that no other block contains; what is left of the
/// coefficients shared with other blocks, of single leaves and of the constant becomes
/// conjunctions. The choice per block that gives the smallest sum wins, so blocks that
/// overlap (`-2·(((h ^ g) & a) ^ f) - 2·((g | j) & (a ^ h))`) split their shared part as
/// the smallest terms need. Memoized per thread, across runs: later rounds see the same regions.
pub(super) fn wide_blocks(t: &T, w: &Ctx) -> Option<T> {
    if has_const_bitwise(t, w) {
        return None;
    }
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    if !(MAX_LEAVES + 1..=64).contains(&lv.len()) {
        return None;
    }
    // Regions with products are left to `poly_mba`, which expands them across terms, and
    // those with arithmetic leaves to `relate` and the rewrite of the shrunk region.
    if lv.iter().any(|l| kind(l, w) == Kind::Lin || matches!(l, T::Op(Op::Mul, a) if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)))) {
        return None;
    }
    thread_local! {
        static CACHE: std::cell::RefCell<crate::eval::FastMap<(u32, T), Option<T>>> = Default::default();
    }
    let key = (w.w, t.clone());
    if let Some(r) = CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return r;
    }
    let r = wide_blocks_uncached(t, lv, w);
    CACHE.with(|c| {
        let mut c = c.borrow_mut();
        if c.len() >= MAX_WIDE_CACHE {
            c.clear();
        }
        c.insert(key, r.clone());
    });
    r
}

fn wide_blocks_uncached(t: &T, lv: Vec<T>, w: &Ctx) -> Option<T> {
    let n = lv.len();
    let m = w.mask;
    let (terms, konst) = region_terms(t, w);
    let mut coef: crate::eval::FastMap<u64, u64> = Default::default();
    coef.insert(0, konst);
    for (c, x) in &terms {
        let mut xl = Vec::new();
        leaves(x, w, &mut xl);
        let k = xl.len();
        if k > MAX_TERM_LEAVES {
            return None;
        }
        let idx: Vec<usize> = xl.iter().map(|l| lv.iter().position(|g| g == l)).collect::<Option<_>>()?;
        let prog = Prog::new(x, &xl, w);
        let mut a: Vec<u64> = (0..1usize << k).map(|p| prog.at(p, w)).collect();
        for i in 0..k {
            for p in 0..1usize << k {
                if p >> i & 1 == 1 {
                    a[p] = a[p].wrapping_sub(a[p ^ 1 << i]) & m;
                }
            }
        }
        for (q, v) in a.into_iter().enumerate().filter(|(_, v)| *v != 0) {
            let g = (0..k).filter(|j| q >> j & 1 == 1).fold(0u64, |acc, j| acc | 1 << idx[j]);
            let e = coef.entry(g).or_insert(0);
            *e = e.wrapping_add(c.wrapping_mul(v)) & m;
        }
    }
    coef.retain(|_, v| *v != 0);
    let mut support: Vec<u64> = coef.keys().copied().collect();
    support.sort_unstable();
    let blocks: Vec<u64> = support.iter().copied().filter(|&p| p.count_ones() >= 2 && !support.iter().any(|&q| q != p && q & p == p)).collect();
    if blocks.is_empty() || blocks.iter().any(|b| b.count_ones() as usize > MAX_WIDE_BLOCK) {
        return None;
    }
    let nb = blocks.len();
    let ph: Vec<T> = (0..n).map(|i| T::Var(format!("\u{1}{i}"))).collect();
    let leaf_size: Vec<usize> = lv.iter().map(size).collect();
    // A term over a block uses each of its leaves; a region not much larger than that
    // is mostly in block form already.
    let least: usize = blocks.iter().map(|&b| (0..n).filter(|i| b >> i & 1 == 1).map(|i| leaf_size[i] + 1).sum::<usize>()).sum();
    if 2 * size(t) < 4 * least {
        return None;
    }
    let private = |g: u64| g.count_ones() >= 2 && blocks.iter().filter(|&&b| b & g == g).count() == 1;
    // Per block: its leaves and the leaf set of each of its points.
    let points: Vec<(Vec<usize>, Vec<u64>)> = blocks
        .iter()
        .map(|&s| {
            let vars: Vec<usize> = (0..n).filter(|i| s >> i & 1 == 1).collect();
            let g = (0..1usize << vars.len()).map(|q| (0..vars.len()).filter(|j| q >> j & 1 == 1).fold(0u64, |acc, j| acc | 1 << vars[j])).collect();
            (vars, g)
        })
        .collect();
    let mut keys: Vec<u64> = support.iter().copied().chain(points.iter().flat_map(|p| p.1.iter().copied())).filter(|&g| !private(g)).collect();
    keys.sort_unstable();
    keys.dedup();
    let key = |g: u64| keys.binary_search(&g).unwrap();
    let base: Vec<u64> = keys.iter().map(|g| coef.get(g).copied().unwrap_or(0)).collect();
    let conj_size: Vec<usize> = keys.iter().map(|&g| (0..n).filter(|i| g >> i & 1 == 1).map(|i| leaf_size[i]).sum::<usize>() + (g.count_ones() as usize).saturating_sub(1)).collect();
    // The coefficient of each point of a block that only that block contains.
    let own: Vec<Vec<Option<u64>>> = points.iter().map(|(_, g)| g.iter().map(|&x| private(x).then(|| coef.get(&x).copied().unwrap_or(0))).collect()).collect();
    let mut opts: Vec<Vec<BlockTerm>> = Vec::new();
    for (e, (vars, g)) in points.iter().enumerate() {
        let k = vars.len();
        // Tables over more than 6 leaves are split by `wide_bool_expr`, which is slow.
        let limit = if k > MAX_LEAVES { MAX_WIDE_TABLES } else { MAX_BLOCK_TABLES };
        let mut found: Vec<(usize, u64, Vec<u64>, B)> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        // The top coefficient of a read-once function is ±2^(number of `^`).
        for mult in (0..k).flat_map(|j| [1i64 << j, -1 << j]).chain([3, -3]) {
            let Some(c) = solve_mul(mult as u64 & m, coef[&blocks[e]], w) else { continue };
            let mut fs = Vec::new();
            let mut f = vec![0u64; (1usize << k).div_ceil(64)];
            block_functions(0, &mut f, k, &own[e], c, w, &mut { BLOCK_STEPS }, limit.saturating_sub(seen.len()), &mut fs);
            for f in fs {
                if seen.insert((c, f.clone())) {
                    if let Some(b) = wide_bool_expr(&f, k) {
                        found.push((b_size(&b, vars, &leaf_size), c, f, b));
                    }
                }
            }
        }
        found.sort_by_key(|x| x.0);
        found.truncate(MAX_BLOCK_FUNCTIONS);
        let mut out = Vec::new();
        for (size, c, f, b) in found {
            let term = b_to_t_at(&b, vars, &ph);
            let mut mob: Vec<i64> = (0..1usize << k).map(|q| (f[q >> 6] >> (q & 63) & 1) as i64).collect();
            for i in 0..k {
                for q in 0..1usize << k {
                    if q >> i & 1 == 1 {
                        mob[q] -= mob[q ^ 1 << i];
                    }
                }
            }
            let adds = (0..1usize << k)
                .filter(|&q| own[e][q].is_none())
                .map(|q| (key(g[q]), (if q == 0 { c.wrapping_mul(f[0] & 1).wrapping_neg() } else { c.wrapping_mul(mob[q] as u64) }) & m))
                .filter(|&(_, v)| v != 0)
                .collect();
            out.push(BlockTerm { c, not: matches!(term, T::Op(Op::Not, _)), term, size, adds });
        }
        if out.is_empty() {
            return None;
        }
        opts.push(out);
    }
    let left = |chosen: &[&BlockTerm]| {
        let mut vals = base.clone();
        for o in chosen {
            for &(q, v) in &o.adds {
                vals[q] = vals[q].wrapping_sub(v) & m;
            }
        }
        vals
    };
    let score = |chosen: &[&BlockTerm], vals: &[u64]| -> usize {
        let mut terms: Vec<(u64, usize, bool)> = chosen.iter().map(|o| (o.c, o.size, o.not)).collect();
        terms.extend(keys.iter().zip(vals).zip(&conj_size).filter(|((g, v), _)| **g != 0 && **v != 0).map(|((_, &v), &s)| (v, s, false)));
        positive_first(&mut terms, |x| x.0, w);
        // `factored_sum` saves a multiplication and its constant per extra term of a coefficient.
        let mut cs: Vec<u64> = terms.iter().map(|x| if w.signed(x.0) < 0 { x.0.wrapping_neg() & m } else { x.0 }).filter(|&c| c != 1).collect();
        cs.sort_unstable();
        let shared = cs.len() - { cs.dedup(); cs.len() };
        folded_sum_size(&terms, if keys[0] == 0 { vals[0] } else { 0 }, w) - 2 * shared
    };
    let pick = |choice: &[usize]| -> Vec<&BlockTerm> { opts.iter().zip(choice).map(|(o, &ci)| &o[ci]).collect() };
    let mut best_choice = vec![0usize; nb];
    let mut best_size = score(&pick(&best_choice), &left(&pick(&best_choice)));
    for _ in 0..4 {
        let mut improved = false;
        for e in 0..nb {
            for ci in 0..opts[e].len() {
                let mut c = best_choice.clone();
                c[e] = ci;
                let cs = score(&pick(&c), &left(&pick(&c)));
                if cs < best_size {
                    (best_choice, best_size, improved) = (c, cs, true);
                }
            }
        }
        if !improved {
            break;
        }
    }
    // Each block's term costs at least its size and one `+`, a leftover conjunction its size
    // and one `+` once no later block adds to it; a `~` absorbing the constant saves one node
    // and the first term needs no `+`.
    let mut rest_min = vec![0usize; nb + 1];
    for e in (0..nb).rev() {
        rest_min[e] = rest_min[e + 1] + opts[e].iter().map(|o| o.size).min().unwrap() + 1;
    }
    let mut done: Vec<Vec<usize>> = vec![Vec::new(); nb + 1];
    for q in (0..keys.len()).filter(|&q| keys[q] != 0) {
        let last = (0..nb).rev().find(|&e| opts[e].iter().any(|o| o.adds.iter().any(|a| a.0 == q)));
        done[last.map_or(0, |e| e + 1)].push(q);
    }
    let mut search = Search { opts: &opts, rest_min, done, conj_size: &conj_size, score: &score, mask: m, best: (pick(&best_choice), best_size.min(size(t))), steps: MAX_BLOCK_COMBOS };
    search.run(0, 0, &mut Vec::new(), &mut base.clone());
    let (chosen, best_size) = search.best;
    if best_size >= size(t) {
        return None;
    }
    let vals = left(&chosen);
    let mut terms: Vec<(u64, T)> = chosen.iter().map(|o| (o.c, o.term.clone())).collect();
    for (&g, &v) in keys.iter().zip(&vals).filter(|(g, v)| **g != 0 && **v != 0) {
        terms.push((v, (0..n).filter(|i| g >> i & 1 == 1).map(|i| ph[i].clone()).reduce(|a, b| T::Op(Op::And, vec![a, b])).unwrap()));
    }
    positive_first(&mut terms, |x| x.0, w);
    let konst = if keys[0] == 0 { vals[0] } else { 0 };
    let r = [build_sum(&terms, konst, w), factored_sum(&terms, konst, w)].into_iter().min_by_key(|r| placeholder_size(r, &ph, &leaf_size)).unwrap();
    (placeholder_size(&r, &ph, &leaf_size) < size(t)).then(|| fill_placeholders(&r, &ph, &lv))
}

/// `build_sum` with the terms of each coefficient `±c` (`c` not 1) that has two or more
/// summed first, `c·(a + b - d)` for `c·a + c·b - c·d`.
pub(super) fn factored_sum(terms: &[(u64, T)], konst: u64, w: &Ctx) -> T {
    // `c·t + c` is `-c·~t` before grouping, as in `build_sum`.
    let mut terms = terms.to_vec();
    let mut konst = konst;
    if konst != 0 && (konst != 1 || terms.len() > 1) {
        if let Some(e) = terms.iter_mut().find(|(c, _)| *c == konst) {
            let not = match &e.1 {
                T::Op(Op::Not, a) => a[0].clone(),
                t => T::Op(Op::Not, vec![t.clone()]),
            };
            *e = (konst.wrapping_neg() & w.mask, not);
            konst = 0;
        }
    }
    let pos = |c: u64| if w.signed(c) < 0 { c.wrapping_neg() & w.mask } else { c };
    let mut outer: Vec<(u64, T)> = Vec::new();
    let mut done = vec![false; terms.len()];
    for i in 0..terms.len() {
        let a = pos(terms[i].0);
        if done[i] || a == 1 {
            continue;
        }
        let same: Vec<usize> = (i..terms.len()).filter(|&j| !done[j] && pos(terms[j].0) == a).collect();
        if same.len() < 2 {
            continue;
        }
        // With every coefficient `-c`, `-c·(a + b)` needs no `Neg` inside.
        let c = if same.iter().all(|&j| terms[j].0 != a) { a.wrapping_neg() & w.mask } else { a };
        let mut inner: Vec<(u64, T)> = same.iter().map(|&j| (if terms[j].0 == c { 1 } else { w.mask }, terms[j].1.clone())).collect();
        positive_first(&mut inner, |x| x.0, w);
        same.iter().for_each(|&j| done[j] = true);
        outer.push((c, build_sum(&inner, 0, w)));
    }
    outer.extend(terms.iter().zip(&done).filter(|(_, d)| !**d).map(|(t, _)| t.clone()));
    positive_first(&mut outer, |x| x.0, w);
    build_sum(&outer, konst, w)
}

type ScoreFn<'a> = &'a dyn Fn(&[&BlockTerm], &[u64]) -> usize;

/// Branch and bound over the choice of one term per block in `wide_blocks`.
struct Search<'a> {
    opts: &'a [Vec<BlockTerm>],
    rest_min: Vec<usize>,
    /// Leftover keys no block from this one on adds to.
    done: Vec<Vec<usize>>,
    conj_size: &'a [usize],
    score: ScoreFn<'a>,
    mask: u64,
    best: (Vec<&'a BlockTerm>, usize),
    steps: usize,
}

impl<'a> Search<'a> {
    fn run(&mut self, e: usize, mut partial: usize, chosen: &mut Vec<&'a BlockTerm>, vals: &mut [u64]) {
        partial += self.done[e].iter().filter(|&&q| vals[q] != 0).map(|&q| self.conj_size[q] + 1).sum::<usize>();
        if self.steps == 0 || (partial + self.rest_min[e]).saturating_sub(2) >= self.best.1 {
            return;
        }
        self.steps -= 1;
        if e == self.opts.len() {
            let sc = (self.score)(chosen, vals);
            if sc < self.best.1 {
                self.best = (chosen.clone(), sc);
            }
            return;
        }
        let opts = self.opts;
        for o in &opts[e] {
            apply(&o.adds, vals, self.mask, false);
            chosen.push(o);
            self.run(e + 1, partial + o.size + 1, chosen, vals);
            chosen.pop();
            apply(&o.adds, vals, self.mask, true);
        }
    }
}

/// `vals` less (or, undoing, plus) `adds`.
pub(super) fn apply(adds: &[(usize, u64)], vals: &mut [u64], mask: u64, undo: bool) {
    for &(q, v) in adds {
        vals[q] = if undo { vals[q].wrapping_add(v) } else { vals[q].wrapping_sub(v) } & mask;
    }
}

/// The tables `f` over `k` variables, from point `q` on with the points below fixed in `f`,
/// whose conjunction-basis coefficient times `c` is `target` at every point where that is given.
#[allow(clippy::too_many_arguments)]
fn block_functions(q: usize, f: &mut Vec<u64>, k: usize, target: &[Option<u64>], c: u64, w: &Ctx, steps: &mut usize, limit: usize, out: &mut Vec<Vec<u64>>) {
    if q == 1 << k {
        out.push(f.clone());
        return;
    }
    if *steps == 0 || out.len() >= limit {
        return;
    }
    let mut rest = 0i64;
    let mut p = q;
    while p != 0 {
        p = (p - 1) & q;
        let v = (f[p >> 6] >> (p & 63) & 1) as i64;
        rest += if (q.count_ones() - p.count_ones()) % 2 == 0 { v } else { -v };
    }
    let ok = |v: u64| target[q].is_none_or(|t| c.wrapping_mul(v.wrapping_add(rest as u64)) & w.mask == t);
    let ok = [ok(0), ok(1)];
    if ok[0] && ok[1] {
        *steps -= 1;
    }
    for v in (0..2u64).filter(|&v| ok[v as usize]) {
        f[q >> 6] |= v << (q & 63);
        block_functions(q + 1, f, k, target, c, w, steps, limit, out);
        f[q >> 6] &= !(1u64 << (q & 63));
    }
}

/// A short bitwise expression for the table `f` over `k` variables (bit `q` of word
/// `q / 64` is the value at point `q`): `bool_expr` up to 6 variables; above, the smallest
/// `g(A) op h(B)` over disjoint variable sets, `g` and `h` split again, which finds every
/// read-once function; `None` for other functions over more than 6 variables.
fn wide_bool_expr(f: &[u64], k: usize) -> Option<B> {
    let neg = if k > MAX_LEAVES {
        let g: Vec<u64> = f.iter().map(|x| !x).collect();
        wide_bool_cost(&g, k).map(|(c, b)| (c + 1, B::Not(Arc::new(b))))
    } else {
        None
    };
    [wide_bool_cost(f, k), neg].into_iter().flatten().min_by_key(|x| x.0).map(|x| x.1)
}

fn wide_bool_cost(f: &[u64], k: usize) -> Option<(usize, B)> {
    if k <= MAX_LEAVES {
        return match bool_expr_canon(f[0] & table_full(k), k) {
            BE::E(c, b) => Some((c, b)),
            _ => None,
        };
    }
    thread_local! {
        static CACHE: std::cell::RefCell<crate::eval::FastMap<(Vec<u64>, usize), Option<(usize, B)>>> = Default::default();
    }
    if let Some(r) = CACHE.with(|c| c.borrow().get(&(f.to_vec(), k)).cloned()) {
        return r;
    }
    let bit = |q: usize| f[q >> 6] >> (q & 63) & 1 == 1;
    let full = (1usize << k) - 1;
    // Index of `q`'s bits in `set` among the variables of `set`.
    let pext = |q: usize, set: usize| (0..k).filter(|i| set >> i & 1 == 1).enumerate().fold(0usize, |acc, (j, i)| acc | (q >> i & 1) << j);
    let pack = |v: &[bool]| {
        let mut t = vec![0u64; v.len().div_ceil(64)];
        v.iter().enumerate().filter(|x| *x.1).for_each(|(q, _)| t[q >> 6] |= 1 << (q & 63));
        t
    };
    let not = |b: B| B::Not(Arc::new(b));
    let vars = |set: usize| -> Vec<usize> { (0..k).filter(|i| set >> i & 1 == 1).collect() };
    // Cost of a side, negated or not, whichever is smaller.
    let side = |v: &[bool], set: usize| -> Option<(usize, B)> {
        let kk = set.count_ones() as usize;
        let direct = wide_bool_cost(&pack(v), kk);
        let neg: Vec<bool> = v.iter().map(|x| !x).collect();
        let negated = if kk > MAX_LEAVES { wide_bool_cost(&pack(&neg), kk).map(|(c, b)| (c + 1, not(b))) } else { None };
        let best = [direct, negated].into_iter().flatten().min_by_key(|x| x.0)?;
        Some((best.0, remap(&best.1, &vars(set))))
    };
    let f0 = bit(0);
    let mut best: Option<(usize, B)> = None;
    for a in (1..full).filter(|a| a & 1 == 1) {
        let b = full ^ a;
        let (na, nb) = (1usize << a.count_ones(), 1usize << b.count_ones());
        let (mut any_a, mut all_a, mut zero_a) = (vec![false; na], vec![true; na], vec![false; na]);
        let (mut any_b, mut all_b, mut zero_b) = (vec![false; nb], vec![true; nb], vec![false; nb]);
        let idx: Vec<(usize, usize)> = (0..=full).map(|q| (pext(q, a), pext(q, b))).collect();
        for (q, &(qa, qb)) in idx.iter().enumerate() {
            let v = bit(q);
            any_a[qa] |= v;
            all_a[qa] &= v;
            any_b[qb] |= v;
            all_b[qb] &= v;
            if qb == 0 {
                zero_a[qa] = v;
            }
            if qa == 0 {
                zero_b[qb] = v ^ f0;
            }
        }
        for (op, g, h) in [(Op::And, &any_a, &any_b), (Op::Or, &all_a, &all_b), (Op::Xor, &zero_a, &zero_b)] {
            let join = |x: bool, y: bool| match op {
                Op::And => x & y,
                Op::Or => x | y,
                _ => x ^ y,
            };
            if !idx.iter().enumerate().all(|(q, &(qa, qb))| join(g[qa], h[qb]) == bit(q)) {
                continue;
            }
            let Some((cg, eg)) = side(g, a) else { continue };
            let Some((ch, eh)) = side(h, b) else { continue };
            if best.as_ref().is_none_or(|(c, _)| cg + ch + 1 < *c) {
                best = Some((cg + ch + 1, B::Bin(op, Arc::new(eg), Arc::new(eh))));
            }
        }
    }
    CACHE.with(|c| c.borrow_mut().insert((f.to_vec(), k), best.clone()));
    best
}

/// `terms` with the first term of positive coefficient moved to the front, where it costs no `Neg`.
fn positive_first<X>(terms: &mut [X], coef: impl Fn(&X) -> u64, w: &Ctx) {
    if let Some(p) = terms.iter().position(|x| w.signed(coef(x)) > 0) {
        terms[..=p].rotate_right(1);
    }
}

/// Size of `b` with variable `i` standing for a leaf of `ls[vars[i]]` nodes.
pub(super) fn b_size(b: &B, vars: &[usize], ls: &[usize]) -> usize {
    match b {
        B::V(i) => ls[vars[*i]],
        B::Not(x) => 1 + b_size(x, vars, ls),
        B::Bin(_, x, y) => 1 + b_size(x, vars, ls) + b_size(y, vars, ls),
    }
}

/// Size of `t` with placeholder `ph[i]` counting as `ls[i]` nodes.
fn placeholder_size(t: &T, ph: &[T], ls: &[usize]) -> usize {
    match t {
        T::Var(_) => ph.iter().position(|p| p == t).map_or(1, |i| ls[i]),
        T::Num(_) => 1,
        T::Op(_, a) => 1 + a.iter().map(|x| placeholder_size(x, ph, ls)).sum::<usize>(),
    }
}

/// `t` with placeholder `ph[i]` replaced by `lv[i]`.
fn fill_placeholders(t: &T, ph: &[T], lv: &[T]) -> T {
    match t {
        T::Var(_) => ph.iter().position(|p| p == t).map_or_else(|| t.clone(), |i| lv[i].clone()),
        T::Num(_) => t.clone(),
        T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill_placeholders(x, ph, lv)).collect()),
    }
}

/// Most `clustered` calls nested inside each other.
const MAX_CLUSTER_DEPTH: usize = 2;

/// A region with more than `MAX_LEAVES` leaves rebuilt in parts: its terms grouped by the
/// leaves they use, a group whose leaves are a subset of another's joining the smallest
/// such, and each group of at most `MAX_LEAVES` leaves rewritten on its own, which is
/// exact since the parts add up to the region. Splits such as `7·(a & 0xffff) +
/// 7·(a & -0x10000)` and constants spread over the region then come together.
pub(super) fn clustered(t: &T, w: &Ctx) -> Option<T> {
    // Rewriting a group can reach regions whose groups lead back to new forms of the
    // enclosing ones.
    let nested = {
        let c = w.st.clustering.lock().unwrap();
        c.len() >= MAX_CLUSTER_DEPTH || c.contains(t)
    };
    if w.st.no_cluster.load(Relaxed) || nested {
        return None;
    }
    w.st.clustering.lock().unwrap().push(t.clone());
    let r = clustered_in(t, w);
    w.st.clustering.lock().unwrap().pop();
    r
}

fn clustered_in(t: &T, w: &Ctx) -> Option<T> {
    // Regions with products are left to `poly_mba`, which expands them across terms.
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    if lv.iter().any(|l| matches!(l, T::Op(Op::Mul, a) if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)))) {
        return None;
    }
    let (terms, konst) = region_terms(t, w);
    if terms.len() < 2 {
        return None;
    }
    let groups = leaf_groups(terms, w);
    if groups.len() < 2 {
        return None;
    }
    let mut parts = Vec::new();
    for (key, g) in &groups {
        let sum = build_sum(g, 0, w);
        let r = if key.len() <= MAX_LEAVES && g.len() > 1 { rewrite(&sum, w) } else { sum.clone() };
        if size(&r) < size(&sum) {
            parts.push((1, r));
        } else {
            parts.extend(g.iter().map(|(c, x)| (*c, rewrite(x, w))));
        }
    }
    let (mut whole, mut k0) = (Vec::new(), konst);
    for (c, x) in &parts {
        match x {
            T::Num(v) => k0 = k0.wrapping_add(c.wrapping_mul(*v as u64)) & w.mask,
            x => whole.push((*c, x.clone())),
        }
    }
    let whole = build_sum(&whole, k0, w);
    let (mut terms, mut k): (Vec<(u64, T)>, u64) = (Vec::new(), konst);
    for (c, x) in parts {
        let (ts, xk) = region_terms(&x, w);
        k = k.wrapping_add(c.wrapping_mul(xk)) & w.mask;
        for (d, y) in ts {
            let d = c.wrapping_mul(d) & w.mask;
            match terms.iter_mut().find(|(_, z)| *z == y) {
                Some(e) => e.0 = e.0.wrapping_add(d) & w.mask,
                None => terms.push((d, y)),
            }
        }
    }
    for (c, y) in terms.iter_mut() {
        *c = low_multiplier(*c, y, w);
    }
    terms.retain(|(c, _)| *c != 0);
    let (terms, k) = absorb_constant(terms, k, w);
    let flat = build_sum(&terms, k, w);
    Some(if size(&flat) <= size(&whole) { flat } else { whole }).filter(|r| size(r) < size(t))
}

/// The terms of a region grouped by the leaves they use, a group whose leaves are a subset
/// of another's (of at most `MAX_LEAVES` leaves) joining the smallest such; each group with
/// the hashes of its leaves, fewest leaves first.
pub(super) fn leaf_groups(terms: Vec<(u64, T)>, w: &Ctx) -> Vec<(Vec<u64>, Vec<(u64, T)>)> {
    let mut groups: Vec<(Vec<u64>, Vec<(u64, T)>)> = Vec::new();
    for (c, x) in terms {
        let mut lv = Vec::new();
        leaves(&x, w, &mut lv);
        let mut key: Vec<u64> = lv.iter().map(term_hash).collect();
        key.sort_unstable();
        key.dedup();
        match groups.iter_mut().find(|(k, _)| *k == key) {
            Some(g) => g.1.push((c, x)),
            None => groups.push((key, vec![(c, x)])),
        }
    }
    groups.sort_by_key(|(k, _)| k.len());
    let mut i = 0;
    while i < groups.len() {
        let sup = (i + 1..groups.len())
            .filter(|&j| groups[j].0.len() > groups[i].0.len() && groups[j].0.len() <= MAX_LEAVES && groups[i].0.iter().all(|h| groups[j].0.contains(h)))
            .min_by_key(|&j| groups[j].0.len());
        match sup {
            Some(j) => {
                let (_, g) = groups.remove(i);
                groups[j - 1].1.extend(g);
            }
            None => i += 1,
        }
    }
    groups
}

/// `terms` plus `k` with `k` moved into one term, `a·B + a` as `-a·~B`, where some term has
/// coefficient `k`, also after writing each `a·~B` as `-a·B - a` (`7·~(u ^ v)` for
/// `-7·(u ^ v) - 7`).
fn absorb_constant(terms: Vec<(u64, T)>, k: u64, w: &Ctx) -> (Vec<(u64, T)>, u64) {
    let not = |y: &T| match y {
        T::Op(Op::Not, a) => a[0].clone(),
        y => T::Op(Op::Not, vec![y.clone()]),
    };
    let absorb = |mut terms: Vec<(u64, T)>, k: u64| {
        let e = terms.iter_mut().find(|(c, y)| k != 0 && *c == k && !matches!(y, T::Num(_)))?;
        *e = (e.0.wrapping_neg() & w.mask, not(&e.1));
        Some((terms, 0))
    };
    let (mut plain, mut k2) = (terms.clone(), k);
    for (c, y) in plain.iter_mut() {
        if let T::Op(Op::Not, a) = y {
            k2 = k2.wrapping_sub(*c) & w.mask;
            *c = c.wrapping_neg() & w.mask;
            *y = a[0].clone();
        }
    }
    absorb(plain, k2).or_else(|| absorb(terms.clone(), k)).unwrap_or((terms, k))
}

/// The multiplier `c` of `y` cut to the bits that matter when `y` is `a & M` with `M` a
/// multiple of `2^k`: `c` modulo `2^(w-k)`, as the value of least magnitude.
fn low_multiplier(c: u64, y: &T, w: &Ctx) -> u64 {
    let tz = match y {
        T::Op(Op::And, a) => match (&a[0], &a[1]) {
            (T::Num(m), _) | (_, T::Num(m)) if *m as u64 & w.mask != 0 => (*m as u64 & w.mask).trailing_zeros(),
            _ => 0,
        },
        _ => 0,
    };
    if tz == 0 {
        return c;
    }
    let low = c & (w.mask >> tz);
    let high = low.wrapping_sub(1u64 << (w.w - tz)) & w.mask;
    if w.signed(low).unsigned_abs() <= w.signed(high).unsigned_abs() { low } else { high }
}
