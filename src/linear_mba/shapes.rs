//! Bitwise expressions with free constants (`Shapes`) and the candidates built from one or two of them.

use super::*;

/// Largest bitwise expression size `shape_candidates` searches.
const MAX_SHAPE: usize = 15;

#[derive(Clone, Copy)]
enum Shape {
    Leaf(u8),
    Const,
    Not(u32),
    Bin(u8, u32, u32),
}

const SHAPE_OPS: [Op; 3] = [Op::And, Op::Or, Op::Xor];

/// Bitwise expressions of `n` leaves and constants, one per set of truth tables
/// they can give at one bit position when every constant bit is free. Tables are
/// indexed by point `q` (leaf `i` = bit `i` of `q`); a set is a 256-bit mask.
struct Shapes {
    n: usize,
    sets: Vec<[u64; 4]>,
    elems: Vec<Vec<u8>>,
    how: Vec<Shape>,
    /// `levels[s]`: the entries of size `s`.
    levels: Vec<std::ops::Range<usize>>,
    seen: crate::eval::FastSet<[u64; 4]>,
}

pub(super) fn one(f: u8) -> [u64; 4] {
    let mut s = [0; 4];
    s[(f >> 6) as usize] |= 1 << (f & 63);
    s
}

impl Shapes {
    fn new(n: usize) -> Shapes {
        let mut sh = Shapes { n, sets: Vec::new(), elems: Vec::new(), how: Vec::new(), levels: vec![0..0], seen: Default::default() };
        let full = sh.full();
        let mut level = Vec::new();
        for i in 0..n {
            let f = (0..1usize << n).filter(|q| q >> i & 1 == 1).fold(0u8, |acc, q| acc | 1 << q);
            level.push((one(f), Shape::Leaf(i as u8)));
        }
        let mut c = one(0);
        c.iter_mut().zip(one(full)).for_each(|(a, b)| *a |= b);
        level.push((c, Shape::Const));
        sh.push_level(level);
        sh
    }

    fn full(&self) -> u8 {
        ((1u32 << (1 << self.n)) - 1) as u8
    }

    fn push_level(&mut self, level: Vec<([u64; 4], Shape)>) {
        let start = self.sets.len();
        for (s, how) in level {
            self.push(s, how, true);
        }
        self.levels.push(start..self.sets.len());
    }

    /// Entries of the last level are never operands, so they need no `elems`.
    fn push(&mut self, s: [u64; 4], how: Shape, operand: bool) {
        if self.seen.insert(s) {
            self.elems.push(if operand { (0..=255u8).filter(|&f| s[(f >> 6) as usize] >> (f & 63) & 1 == 1).collect() } else { Vec::new() });
            self.sets.push(s);
            self.how.push(how);
        }
    }

    fn grow(&mut self, size: usize) {
        let full = self.full();
        while self.levels.len() <= size {
            let s = self.levels.len();
            let operand = s < MAX_SHAPE;
            let start = self.sets.len();
            for i in self.levels[s - 1].clone() {
                let mut set = [0; 4];
                for &f in &self.elems[i] {
                    let g = !f & full;
                    set[(g >> 6) as usize] |= 1 << (g & 63);
                }
                self.push(set, Shape::Not(i as u32), operand);
            }
            for a in 1..=(s - 1) / 2 {
                for i in self.levels[a].clone() {
                    let js = self.levels[s - 1 - a].clone();
                    let js = if 2 * a == s - 1 { i..js.end } else { js };
                    for k in js {
                        let mut sets = [[0u64; 4]; 3];
                        for &x in &self.elems[i] {
                            for &y in &self.elems[k] {
                                for (set, r) in sets.iter_mut().zip([x & y, x | y, x ^ y]) {
                                    set[(r >> 6) as usize] |= 1 << (r & 63);
                                }
                            }
                        }
                        for (op, set) in sets.into_iter().enumerate() {
                            self.push(set, Shape::Bin(op as u8, i as u32, k as u32), operand);
                        }
                    }
                }
            }
            self.levels.push(start..self.sets.len());
        }
    }

    /// Set the bits `j` of the constants (numbered in visiting order) so that
    /// entry `i` gives table `f` there.
    fn solve(&self, i: usize, f: u8, j: u32, consts: &mut Vec<u64>, slot: &mut usize) {
        match self.how[i] {
            Shape::Leaf(_) => {}
            Shape::Const => {
                if consts.len() <= *slot {
                    consts.resize(*slot + 1, 0);
                }
                if f != 0 {
                    consts[*slot] |= 1 << j;
                }
                *slot += 1;
            }
            Shape::Not(a) => self.solve(a as usize, !f & self.full(), j, consts, slot),
            Shape::Bin(op, a, b) => {
                let (a, b) = (a as usize, b as usize);
                let apply = |x: u8, y: u8| match op {
                    0 => x & y,
                    1 => x | y,
                    _ => x ^ y,
                };
                let (x, y) = self.elems[a]
                    .iter()
                    .find_map(|&x| self.elems[b].iter().find(|&&y| apply(x, y) == f).map(|&y| (x, y)))
                    .expect("table in the entry's set");
                self.solve(a, x, j, consts, slot);
                self.solve(b, y, j, consts, slot);
            }
        }
    }

    /// Size of what `build` gives for entry `i`.
    fn size_of(&self, i: usize, leaf_sizes: &[usize]) -> usize {
        match self.how[i] {
            Shape::Leaf(k) => leaf_sizes[k as usize],
            Shape::Const => 1,
            Shape::Not(a) => 1 + self.size_of(a as usize, leaf_sizes),
            Shape::Bin(_, a, b) => 1 + self.size_of(a as usize, leaf_sizes) + self.size_of(b as usize, leaf_sizes),
        }
    }

    fn is_not(&self, i: usize) -> bool {
        matches!(self.how[i], Shape::Not(_))
    }

    fn build(&self, i: usize, lv: &[T], consts: &[u64], slot: &mut usize, w: &Ctx) -> T {
        match self.how[i] {
            Shape::Leaf(k) => lv[k as usize].clone(),
            Shape::Const => {
                *slot += 1;
                T::Num(w.signed(consts.get(*slot - 1).copied().unwrap_or(0) & w.mask))
            }
            Shape::Not(a) => T::Op(Op::Not, vec![self.build(a as usize, lv, consts, slot, w)]),
            Shape::Bin(op, a, b) => {
                let x = self.build(a as usize, lv, consts, slot, w);
                T::Op(SHAPE_OPS[op as usize], vec![x, self.build(b as usize, lv, consts, slot, w)])
            }
        }
    }
}

fn shapes(n: usize) -> &'static std::sync::Mutex<Shapes> {
    static SHAPES: [OnceLock<std::sync::Mutex<Shapes>>; 3] = [OnceLock::new(), OnceLock::new(), OnceLock::new()];
    SHAPES[n - 1].get_or_init(|| std::sync::Mutex::new(Shapes::new(n)))
}

/// Candidates `c·B + r` smaller than `limit`, with `B` a bitwise expression of
/// 2 or 3 leaves and constants. Bit `j` of `B` has a table `f_j`, and the region
/// needs `c·(f_j(q) - f_j(0)) = g_j(q)` modulo `2^(w-j)`; the smallest `B` whose
/// table set meets each bit's acceptable tables is found in `Shapes`.
pub(super) fn shape_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, mut limit: usize, cands: &mut Vec<T>) {
    let n = lv.len();
    if !(2..=3).contains(&n) {
        return;
    }
    let m = w.mask;
    let pts = 1usize << n;
    let mut bits: Vec<(&Vec<u64>, u64)> = vec![(&groups[0].0, 0); w.w as usize];
    for (g, mask) in groups {
        for j in 0..w.w {
            if mask >> j & 1 == 1 {
                let rest = w.w - j;
                bits[j as usize] = (g, if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 });
            }
        }
    }
    let mut scales: Vec<u64> = groups.iter().flat_map(|(g, _)| g.iter().filter(|&&v| v != 0).flat_map(|&v| [v, v.wrapping_neg() & m])).collect();
    scales.sort_unstable();
    scales.dedup();
    let zero_env: Vec<(T, u64)> = lv.iter().map(|l| (l.clone(), 0)).collect();
    let nf = 1usize << pts;
    for c in scales {
        let overhead = if c == 1 { 0 } else if c == m { 1 } else { 2 };
        // Table `f` fits when `c·(f(q) - f(0)) = g(q)` at every point: with `f(0) = 0`
        // the points where `g = c` and not 0 need 1, those where `g = 0` and not `c`
        // need 0; with `f(0) = 1` the same with `-c` and the complement.
        let mut memo = crate::eval::FastMap::default();
        let mut accept = |&(g, rest_mask): &(&Vec<u64>, u64)| {
            let is = |q: usize, v: u64| (v ^ g[q]) & rest_mask == 0;
            let key: Vec<(usize, usize)> = [c, c.wrapping_neg()]
                .iter()
                .map(|&v| {
                    let (mut ones, mut zeros) = (0usize, 0usize);
                    for q in 0..pts {
                        match (is(q, v), is(q, 0)) {
                            (true, false) => ones |= 1 << q,
                            (false, true) => zeros |= 1 << q,
                            (false, false) => ones |= usize::MAX,
                            _ => {}
                        }
                    }
                    (ones, zeros)
                })
                .collect();
            *memo.entry(key.clone()).or_insert_with(|| {
                let mut set = [0u64; 4];
                let (z, o) = (key[0], key[1]);
                for f in 0..nf {
                    let fits = if f & 1 == 0 { f & z.0 == z.0 && f & z.1 == 0 } else { !f & o.0 & (nf - 1) == o.0 && !f & o.1 == 0 };
                    if fits {
                        set[f >> 6] |= 1 << (f & 63);
                    }
                }
                set
            })
        };
        let acc: Vec<[u64; 4]> = bits.iter().map(&mut accept).collect();
        if acc.iter().any(|a| a == &[0; 4]) {
            continue;
        }
        // First ask for `B(0) = h` with `c·h = e0`, so that `r = 0`; only the low
        // `w - tz(c)` bits of `h` matter.
        let fixed = (if e0 == 0 { Some(0) } else { solve_mul(c, e0, w) }).map(|h| {
            let low = w.w - c.trailing_zeros();
            let mut acc = acc.clone();
            for (j, a) in acc.iter_mut().enumerate().filter(|&(j, _)| (j as u32) < low) {
                let at0 = if h >> j & 1 == 1 { !0x5555_5555_5555_5555u64 } else { 0x5555_5555_5555_5555 };
                a.iter_mut().for_each(|x| *x &= at0);
            }
            acc
        });
        for (acc, r_size) in fixed.into_iter().map(|a| (a, 0)).chain([(acc, 2)]) {
            if acc.iter().any(|a| a == &[0; 4]) {
                continue;
            }
            let Some(b) = smallest_shape(&acc, n, MAX_SHAPE.min(limit.saturating_sub(overhead + r_size + 1)), lv, w) else {
                continue;
            };
            let r = e0.wrapping_sub(c.wrapping_mul(eval(&b, w, &zero_env))) & m;
            let cand = build_sum(&[(c, b)], r, w);
            limit = limit.min(size(&cand));
            cands.push(cand);
        }
    }
}

/// Most groups `pair_candidates` handles, and most shape entries it checks.
const MAX_PAIR_GROUPS: usize = 8;
const PAIR_BUDGET: usize = 500_000;
/// Largest total size of the two shapes.
const MAX_PAIR_SIZE: usize = 12;

fn meets(a: &[u64; 4], b: &[u64; 4]) -> bool {
    a.iter().zip(b).any(|(x, y)| x & y != 0)
}

/// Candidates `c1·B1 + c2·B2 + r` for 2 or 3 leaves, with `B1`, `B2` from `Shapes`,
/// for terms that share leaves so `semi_split` cannot separate them:
/// `((y ^ 0x229c) | 0xa0) + ((z | 0xbe) | (y ^ 0x9a))`. Per group and table `f1`,
/// the tables `f2` that complete it are found as in `shape_candidates`; shape pairs
/// are tried by total size, and each group's `(f1(0), f2(0))` is chosen so that
/// `r = 0` when possible.
pub(super) fn pair_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize, cands: &mut Vec<T>) {
    let n = lv.len();
    // One group is a linear table, which `overlapping_terms` covers.
    if !(1..=3).contains(&n) || !(2..=MAX_PAIR_GROUPS).contains(&groups.len()) {
        return;
    }
    let key = (w.w, groups.to_vec(), e0, lv.to_vec(), limit);
    if let Some(r) = w.st.pairs.lock().unwrap().get(&key) {
        cands.extend(r.iter().cloned());
        return;
    }
    let mut found = Vec::new();
    pair_candidates_uncached(groups, lv, e0, w, limit, &mut found);
    cands.extend(found.iter().cloned());
    w.st.pairs.lock().unwrap().insert(key, found);
}

fn pair_candidates_uncached(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize, cands: &mut Vec<T>) {
    let n = lv.len();
    let m = w.mask;
    let pts = 1usize << n;
    let nf = 1usize << pts;
    // Each value is 0, ±c1, ±c2 or ±c1 ± c2, so a coefficient is a value or a difference.
    let mut scales: Vec<u64> = groups
        .iter()
        .flat_map(|(g, _)| g.iter().flat_map(|&a| g.iter().map(move |&b| a.wrapping_sub(b) & m)).chain(g.iter().copied()))
        .filter(|&v| v != 0)
        .flat_map(|v| [v, v.wrapping_neg() & m])
        .collect();
    scales.sort_unstable_by_key(|&v| (w.signed(v).unsigned_abs(), v));
    scales.dedup();
    scales.truncate(12);
    let coef = |c: u64| if c == 1 { 0 } else if c == m { 1 } else { 2 };
    let mut budget = PAIR_BUDGET;
    let mut best = limit;
    let leaf_sizes: Vec<usize> = lv.iter().map(size).collect();
    let group_of: Vec<usize> = (0..w.w).map(|j| groups.iter().position(|(_, mask)| mask >> j & 1 == 1).unwrap_or(0)).collect();
    // fits[id][s2]: the entries of size s2 that meet every group's acc2, with `fit_ids`
    // numbering the acc2; many shapes B1 and coefficient pairs give the same acc2.
    let mut fit_ids: crate::eval::FastMap<Vec<[u64; 4]>, usize> = Default::default();
    let mut fits: Vec<(Vec<[u64; 4]>, Vec<Option<Vec<usize>>>)> = Vec::new();
    for (a, &c1) in scales.iter().enumerate() {
        for &c2 in &scales[a..] {
            let overhead = coef(c1) + coef(c2) + 1;
            if overhead + 2 >= best {
                continue;
            }
            let sums = [0, c1, c2, c1.wrapping_add(c2), c1.wrapping_sub(c2)];
            let reachable = |(g, mask): &(Vec<u64>, u64)| {
                let rest = w.w - mask.trailing_zeros();
                let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
                g.iter().all(|&v| sums.iter().any(|&s| (v ^ s) & low == 0 || (v ^ s.wrapping_neg()) & low == 0))
            };
            if !groups.iter().all(reachable) {
                continue;
            }
            // comp[g][f1]: the tables f2 that make (f1, f2) fit group g.
            let mut comp: Vec<Vec<[u64; 4]>> = Vec::with_capacity(groups.len());
            let mut p1: Vec<[u64; 4]> = Vec::with_capacity(groups.len());
            for (g, mask) in groups {
                let rest = w.w - mask.trailing_zeros();
                let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
                let is = |v: u64, x: u64| (v ^ x) & low == 0;
                let mut row = vec![[0u64; 4]; nf];
                let mut p = [0u64; 4];
                for (f1, slot) in row.iter_mut().enumerate() {
                    let b0 = (f1 & 1) as u64;
                    let h: Vec<u64> = (0..pts).map(|q| g[q].wrapping_sub(c1.wrapping_mul(((f1 >> q & 1) as u64).wrapping_sub(b0)))).collect();
                    let mut set = [0u64; 4];
                    for d0 in 0..2u64 {
                        let (one, zero) = (c2.wrapping_mul(1 - d0), c2.wrapping_mul(d0).wrapping_neg());
                        let (mut ones, mut zeros) = (0usize, 0usize);
                        let mut ok = true;
                        for (q, &v) in h.iter().enumerate() {
                            match (is(v, one), is(v, zero)) {
                                (true, false) => ones |= 1 << q,
                                (false, true) => zeros |= 1 << q,
                                (false, false) => ok = false,
                                _ => {}
                            }
                        }
                        if !ok {
                            continue;
                        }
                        let free = (nf - 1) & !(ones | zeros);
                        let mut s = free;
                        loop {
                            let f2 = ones | s;
                            if (f2 & 1) as u64 == d0 {
                                set[f2 >> 6] |= 1 << (f2 & 63);
                            }
                            if s == 0 {
                                break;
                            }
                            s = (s - 1) & free;
                        }
                    }
                    if set != [0; 4] {
                        *slot = set;
                        p[f1 >> 6] |= 1 << (f1 & 63);
                    }
                }
                if p == [0; 4] {
                    break;
                }
                comp.push(row);
                p1.push(p);
            }
            if comp.len() < groups.len() {
                continue;
            }
            let mut sh = shapes(n).lock().unwrap();
            let top = (best - overhead - 1).min(MAX_PAIR_SIZE);
            let other = (2..).map(|v: u64| v & m).find(|&v| v != c1 && v != c2).unwrap();
            // Whether some choice of tables at 0 makes r = 0, per group's set of
            // reachable (f1(0), f2(0)); None when pick_bits gives up.
            let mut zero_r: crate::eval::FastMap<Vec<u8>, Option<bool>> = Default::default();
            // Per shape B1: its acc2's id in `fits`, None when it misses some group.
            let mut fit_of: Vec<Option<Option<usize>>> = Vec::new();
            'sizes: for s in 2..=top {
                if s + overhead >= best {
                    break;
                }
                for s1 in 1..s {
                    let s2 = s - s1;
                    if s1 >= MAX_SHAPE || s2 >= MAX_SHAPE {
                        continue;
                    }
                    sh.grow(s1.max(s2));
                    for i in sh.levels[s1].clone() {
                        if budget == 0 {
                            return;
                        }
                        budget -= 1;
                        if fit_of.len() <= i {
                            fit_of.resize(i + 1, None);
                        }
                        let id = *fit_of[i].get_or_insert_with(|| {
                            if !p1.iter().all(|p| meets(p, &sh.sets[i])) {
                                return None;
                            }
                            let acc2: Vec<[u64; 4]> = (0..groups.len())
                                .map(|gi| {
                                    let mut acc = [0u64; 4];
                                    for &f1 in sh.elems[i].iter().filter(|&&f1| p1[gi][(f1 >> 6) as usize] >> (f1 & 63) & 1 == 1) {
                                        acc.iter_mut().zip(&comp[gi][f1 as usize]).for_each(|(x, y)| *x |= y);
                                    }
                                    acc
                                })
                                .collect();
                            let next = fits.len();
                            let id = *fit_ids.entry(acc2.clone()).or_insert(next);
                            if id == next {
                                fits.push((acc2, Vec::new()));
                            }
                            Some(id)
                        });
                        let Some(id) = id else { continue };
                        let (acc2, row) = &mut fits[id];
                        if row.len() <= s2 {
                            row.resize(s2 + 1, None);
                        }
                        if row[s2].is_none() {
                            let level = sh.levels[s2].clone();
                            budget = budget.saturating_sub(level.len());
                            row[s2] = Some(level.filter(|&k| acc2.iter().all(|acc| meets(acc, &sh.sets[k]))).collect());
                        }
                        for &k in row[s2].as_ref().unwrap() {
                            // The candidate's size depends only on the shapes and on r, and
                            // r = 0 exactly when the carry DP finds a choice, so most
                            // candidates are ruled out without building them.
                            let terms = [(c1, sh.size_of(i, &leaf_sizes), sh.is_not(i)), (c2, sh.size_of(k, &leaf_sizes), sh.is_not(k))];
                            let size_with = |r: u64| folded_sum_size(&terms, r, w);
                            let (folded, unfolded) = (size_with(0), size_with(c1).min(size_with(c2)).min(size_with(other)));
                            if folded.min(unfolded) >= best {
                                continue;
                            }
                            let classes: Vec<u8> = (0..groups.len()).map(|gi| zero_classes(&sh, (i, k), &p1[gi], &comp[gi])).collect();
                            let folds = *zero_r.entry(classes).or_insert_with_key(|classes| {
                                let options: Vec<Vec<(u8, u8)>> = classes.iter().map(|&c| (0..4u8).filter(|t| c >> t & 1 == 1).map(|t| (t >> 1, t & 1)).collect()).collect();
                                match carry_layers(&group_of, &options, (c1, c2), e0, w) {
                                    Ok(_) => Some(true),
                                    Err(gave_up) => (!gave_up).then_some(false),
                                }
                            });
                            let low = match folds {
                                Some(true) => folded,
                                Some(false) => unfolded,
                                None => folded.min(unfolded),
                            };
                            if low >= best {
                                continue;
                            }
                            let cand = build_pair(&sh, (i, k), (c1, c2), groups, &comp, lv, e0, w);
                            if size(&cand) < best {
                                best = size(&cand);
                                cands.push(cand);
                            }
                            // Without a constant term nothing of this size can do better.
                            if s + overhead >= best {
                                break 'sizes;
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Per bit, an index into its group's options so that `Σ_j (c1·a_j + c2·b_j)·2^j = e0`,
/// with `(a_j, b_j)` the option's tables at 0; found from the low bit up with the
/// carry as state. All zeros when there is no such choice.
fn pick_bits(group_of: &[usize], options: &[Vec<(u8, u8)>], c: (u64, u64), e0: u64, w: &Ctx) -> Vec<usize> {
    let bits = w.w as usize;
    let Ok(layers) = carry_layers(group_of, options, c, e0, w) else {
        return vec![0; bits];
    };
    let mut out = vec![0; bits];
    let mut carry = *layers[bits].keys().next().unwrap();
    for j in (0..bits).rev() {
        let (prev, o) = layers[j + 1][&carry];
        out[j] = o;
        carry = prev;
    }
    out
}

/// The carry DP of `pick_bits`; `Err(true)` when it gives up past 4096 carries,
/// `Err(false)` when no choice exists.
#[allow(clippy::type_complexity)]
fn carry_layers(group_of: &[usize], options: &[Vec<(u8, u8)>], (c1, c2): (u64, u64), e0: u64, w: &Ctx) -> Result<Vec<std::collections::BTreeMap<i128, (i128, usize)>>, bool> {
    let bits = w.w as usize;
    let val = |o: (u8, u8)| (w.signed(c1) as i128) * (o.0 & 1) as i128 + (w.signed(c2) as i128) * (o.1 & 1) as i128;
    // layers[j]: carry into bit j -> (carry into bit j-1, option at bit j-1).
    let mut layers: Vec<std::collections::BTreeMap<i128, (i128, usize)>> = vec![std::collections::BTreeMap::from([(0, (0, 0))])];
    for j in 0..bits {
        let mut next = std::collections::BTreeMap::new();
        for &carry in layers[j].keys() {
            for (o, &opt) in options[group_of[j]].iter().enumerate() {
                let s = carry + val(opt);
                if s.rem_euclid(2) == (e0 >> j & 1) as i128 {
                    next.entry((s - (e0 >> j & 1) as i128).div_euclid(2)).or_insert((carry, o));
                }
            }
        }
        if next.is_empty() || next.len() > 4096 {
            return Err(!next.is_empty());
        }
        layers.push(next);
    }
    Ok(layers)
}

/// The reachable `(f1(0), f2(0))` of a group for the shapes `(i, k)`, as a mask
/// over `2·f1(0) + f2(0)`.
fn zero_classes(sh: &Shapes, (i, k): (usize, usize), p1: &[u64; 4], comp: &[[u64; 4]]) -> u8 {
    const EVEN: u64 = 0x5555_5555_5555_5555;
    let mut classes = 0u8;
    for &f1 in sh.elems[i].iter().filter(|&&f1| p1[(f1 >> 6) as usize] >> (f1 & 63) & 1 == 1) {
        let row = &comp[f1 as usize];
        let (even, odd) = (0..4).fold((false, false), |(e, o), t| {
            let x = row[t] & sh.sets[k][t];
            (e || x & EVEN != 0, o || x & !EVEN != 0)
        });
        let a = (f1 & 1) * 2;
        classes |= (even as u8) << a | (odd as u8) << (a + 1);
    }
    classes
}

/// `c1·B1 + c2·B2 + r` for the shapes `(i, k)`, with per bit a table pair whose
/// values at 0 make `r = 0` if there is one.
#[allow(clippy::too_many_arguments)]
fn build_pair(sh: &Shapes, (i, k): (usize, usize), (c1, c2): (u64, u64), groups: &[(Vec<u64>, u64)], comp: &[Vec<[u64; 4]>], lv: &[T], e0: u64, w: &Ctx) -> T {
    let m = w.mask;
    let has = |s: &[u64; 4], f: u8| s[(f >> 6) as usize] >> (f & 63) & 1 == 1;
    // For each group, one table pair per choice of (f1(0), f2(0)).
    let options: Vec<Vec<(u8, u8)>> = (0..groups.len())
        .map(|gi| {
            let mut opts: Vec<(u8, u8)> = Vec::new();
            for &f1 in &sh.elems[i] {
                for &f2 in sh.elems[k].iter().filter(|&&f2| has(&comp[gi][f1 as usize], f2)) {
                    if !opts.iter().any(|&(a, b)| a & 1 == f1 & 1 && b & 1 == f2 & 1) {
                        opts.push((f1, f2));
                    }
                }
            }
            opts
        })
        .collect();
    let group_of: Vec<usize> = (0..w.w).map(|j| groups.iter().position(|(_, mask)| mask >> j & 1 == 1).unwrap_or(0)).collect();
    let picked = pick_bits(&group_of, &options, (c1, c2), e0, w);
    let (mut k1, mut k2) = (Vec::new(), Vec::new());
    for j in 0..w.w {
        let (f1, f2) = options[group_of[j as usize]][picked[j as usize]];
        sh.solve(i, f1, j, &mut k1, &mut 0);
        sh.solve(k, f2, j, &mut k2, &mut 0);
    }
    let (b1, b2) = (sh.build(i, lv, &k1, &mut 0, w), sh.build(k, lv, &k2, &mut 0, w));
    let zero_env: Vec<(T, u64)> = lv.iter().map(|l| (l.clone(), 0)).collect();
    let r = e0.wrapping_sub(c1.wrapping_mul(eval(&b1, w, &zero_env))).wrapping_sub(c2.wrapping_mul(eval(&b2, w, &zero_env))) & m;
    build_sum(&[(c1, b1), (c2, b2)], r, w)
}

/// The smallest expression in `Shapes` of size at most `top` whose table set meets
/// `acc[j]` for every bit `j`, with its constants solved bit by bit.
fn smallest_shape(acc: &[[u64; 4]], n: usize, top: usize, lv: &[T], w: &Ctx) -> Option<T> {
    let mut distinct = acc.to_vec();
    distinct.sort_unstable();
    distinct.dedup();
    let mut sh = shapes(n).lock().unwrap();
    let fits = |set: &[u64; 4]| distinct.iter().all(|a| a.iter().zip(set).any(|(x, y)| x & y != 0));
    for s in 1..=top {
        sh.grow(s);
        let Some(i) = sh.levels[s].clone().find(|&i| fits(&sh.sets[i])) else { continue };
        let mut consts = Vec::new();
        let mut prev = None;
        for (j, a) in acc.iter().enumerate() {
            let meet: Vec<u8> = (0..4)
                .flat_map(|k| {
                    let b = a[k] & sh.sets[i][k];
                    (0..64).filter(move |t| b >> t & 1 == 1).map(move |t| (k * 64 + t) as u8)
                })
                .collect();
            let f = prev.filter(|p| meet.contains(p)).unwrap_or(meet[0]);
            prev = Some(f);
            sh.solve(i, f, j as u32, &mut consts, &mut 0);
        }
        return Some(sh.build(i, lv, &consts, &mut 0, w));
    }
    None
}
