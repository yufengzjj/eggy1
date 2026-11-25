//! Rebuilds that relate leaves of a region: `related_leaves`, `relate` and `unify_operands`.

use super::*;

/// An arithmetic leaf `L` that is itself a linear MBA `ℓ` of other leaves (`a - d`,
/// `(b ^ d) - b`) is treated as independent, but `L - ℓ = 0`, so the region can
/// add `μ·(L - ℓ)` for any `μ`: in `(P & ~b) - (Q & (b | P)) + (b ^ d)` with
/// `Q = (b ^ d) - b`, `μ = 1` removes `d` and leaves `b | P | Q`. Tries up to two
/// such leaves with small `μ`.
pub(super) fn related_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
    let own = |l: &T| {
        let mut sub = Vec::new();
        leaves(l, w, &mut sub);
        sub
    };
    let arith: Vec<&T> = lv
        .iter()
        .filter(|l| kind(l, w) == Kind::Lin && !has_const_bitwise(l, w) && own(l).iter().any(|s| lv.contains(s)))
        .take(4)
        .collect();
    if arith.is_empty() {
        return None;
    }
    let mut ext = lv.to_vec();
    for l in &arith {
        for s in own(l) {
            if !ext.contains(&s) {
                ext.push(s);
            }
        }
    }
    if ext.len() > MAX_LEAVES {
        return None;
    }
    let pts = 1usize << ext.len();
    let prog = Prog::new(t, &ext, w);
    let base: Vec<u64> = (0..pts).map(|p| prog.at(p, w)).collect();
    // `L - ℓ` at each point, with `ℓ` evaluated from `L`'s own leaves.
    let diffs: Vec<Vec<u64>> = arith
        .iter()
        .map(|l| {
            let i = ext.iter().position(|e| e == *l).unwrap();
            let mut own = ext.clone();
            own.remove(i);
            let prog = Prog::new(l, &own, w);
            (0..pts).map(|p| ((p >> i & 1) as u64).wrapping_sub(prog.run(|j| (p >> (j + (j >= i) as usize) & 1) as u64, w))).collect()
        })
        .collect();
    let mus = [1u64, 2, w.mask, w.mask - 1];
    let mut combos: Vec<Vec<(usize, u64)>> = Vec::new();
    for i in 0..arith.len() {
        for &a in &mus {
            combos.push(vec![(i, a)]);
            for k in i + 1..arith.len() {
                if a == 1 || a == w.mask {
                    combos.extend([1, w.mask].map(|b| vec![(i, a), (k, b)]));
                }
            }
        }
    }
    // Rebuilding is the slow part, so only the combinations whose values need the fewest
    // leaves and conjunctions are rebuilt.
    let n = ext.len();
    let mut cands: Vec<((u32, usize), Vec<u64>)> = combos
        .into_iter()
        .map(|combo| {
            let vals: Vec<u64> = (0..pts)
                .map(|p| combo.iter().fold(base[p], |v, &(i, mu)| v.wrapping_add(mu.wrapping_mul(diffs[i][p])) & w.mask))
                .collect();
            (conj_measure(&vals, n, w), vals)
        })
        .collect();
    cands.sort_by_key(|c| c.0);
    cands.into_iter().take(MAX_RELATED_REBUILDS).map(|(_, vals)| rebuild_values(&vals, &ext, w)).min_by_key(size)
}

const MAX_RELATED_REBUILDS: usize = 8;

/// Leaves used and non-zero coefficients of `vals` (on {0,1}^n) in the conjunction basis.
fn conj_measure(vals: &[u64], n: usize, w: &Ctx) -> (u32, usize) {
    let mut a = vals.to_vec();
    for i in 0..n {
        for p in 0..a.len() {
            if p >> i & 1 == 1 {
                a[p] = a[p].wrapping_sub(a[p ^ 1 << i]) & w.mask;
            }
        }
    }
    let used = a.iter().enumerate().filter(|&(_, &c)| c != 0).fold(0usize, |u, (p, _)| u | p);
    (used.count_ones(), a.iter().filter(|&&c| c != 0).count())
}

/// `t` with each region also rebuilt after an arithmetic leaf `L` of a bitwise
/// operation is replaced by a placeholder `v` and `μ·(v - L)` added, which
/// `rewrite` then expands, so products and constant masks cancel too, unlike in
/// `related_leaves`: with `L = y*z - (z ^ y)`, `(z ^ y) - B + 2*(L | B) - y*z` is
/// `L ^ B`. Other leaves equal to `L` or `~L` become `v` or `~v`.
pub(super) fn relate(t: &T, w: &Ctx) -> T {
    if !matches!(t, T::Op(..)) {
        return t.clone();
    }
    let key = (w.w, w.st.relate_leaves.load(Relaxed), w.st.semi_leaves.load(Relaxed), t.clone());
    if let Some(r) = memo_get(&w.st.related, &key, w) {
        return r;
    }
    let (r, used) = tracking_clusters(w, || relate_uncached(t, w));
    w.st.related.lock().unwrap().insert(key, (r.clone(), used));
    r
}

fn relate_uncached(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if kind(t, w) == Kind::Atom {
        return T::Op(*op, a.iter().map(|x| relate(x, w)).collect());
    }
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let inner: Vec<T> = lv.iter().map(|l| relate(l, w)).collect();
    let t = crate::lowbits::replace(t, &lv, &inner);
    relate_region(&t, w).filter(|r| size(r) < size(&t)).unwrap_or(t)
}

/// Most arithmetic leaves `relate_region` tries.
const MAX_RELATED: usize = 4;
/// Most further arithmetic leaves `relate_region` tries that the region also has written out.
const MAX_WRITTEN_OUT: usize = 2;
/// Largest product leaf `relate_region` tries when it is not an operand of a bitwise operation.
const MAX_FREE_PRODUCT: usize = 20;

pub(super) fn relate_region(t: &T, w: &Ctx) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    if lv.len() > w.st.relate_leaves.load(Relaxed) {
        return None;
    }
    fn bit_operands(t: &T, w: &Ctx, out: &mut Vec<T>) {
        let T::Op(op, a) = t else { return };
        if kind(t, w) == Kind::Atom {
            return;
        }
        for x in a {
            if matches!(op, Op::And | Op::Or | Op::Xor) {
                let mut x = x;
                while let T::Op(o, b) = x {
                    if *o != Op::Not {
                        break;
                    }
                    x = &b[0];
                }
                out.push(x.clone());
            }
            bit_operands(x, w, out);
        }
    }
    let mut operands = Vec::new();
    bit_operands(t, w, &mut operands);
    let vars: Vec<Vec<String>> = lv.iter().map(crate::eval::vars).collect();
    let candidates: Vec<usize> = (0..lv.len())
        .filter(|&i| matches!(&lv[i], T::Op(..)) && kind(&lv[i], w) != Kind::Bit && (operands.contains(&lv[i]) || size(&lv[i]) <= MAX_FREE_PRODUCT) && (0..lv.len()).any(|j| j != i && vars[j].iter().any(|v| vars[i].contains(v))))
        .collect();
    let mut arith: Vec<usize> = candidates.iter().copied().take(MAX_RELATED).collect();
    // Past those, leaves written out in the region as well, whose `μ·(v - L)` cancels terms.
    if candidates.len() > MAX_RELATED {
        let own = region_terms(t, w).0;
        let written_out = |l: &T| {
            let (lt, _) = region_terms(l, w);
            lt.len() > 1 && lt.iter().all(|(_, x)| own.iter().any(|(_, y)| x == y))
        };
        arith.extend(candidates[MAX_RELATED..].iter().copied().filter(|&i| kind(&lv[i], w) == Kind::Lin && written_out(&lv[i])).take(MAX_WRITTEN_OUT));
    }
    if arith.is_empty() {
        return None;
    }
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    let zero = |e: T| maybe_zero(&e, w) && rewrite(&e, w) == T::Num(0);
    // `same[k]`: the other leaves equal to `lv[arith[k]]` (false) or to its complement (true).
    let same: Vec<Vec<(usize, bool)>> = arith
        .iter()
        .map(|&i| {
            (0..lv.len())
                .filter(|&j| j != i && kind(&lv[j], w) != Kind::Bit)
                .filter_map(|j| {
                    if zero(op(Op::Sub, vec![lv[i].clone(), lv[j].clone()])) {
                        Some((j, false))
                    } else if zero(op(Op::Add, vec![op(Op::Add, vec![lv[i].clone(), lv[j].clone()]), T::Num(1)])) {
                        Some((j, true))
                    } else {
                        None
                    }
                })
                .collect()
        })
        .collect();
    let ph: Vec<T> = (0..arith.len()).map(|k| T::Var(format!("\u{2}{k}"))).collect();
    // `t` with leaf `k` replaced by its placeholder and `μ·(v - L)` added.
    let relate_one = |t: &T, k: usize, mu: i64| {
        let s = crate::lowbits::replace(t, std::slice::from_ref(&lv[arith[k]]), std::slice::from_ref(&ph[k]));
        op(Op::Add, vec![s, op(Op::Mul, vec![T::Num(mu), op(Op::Sub, vec![ph[k].clone(), lv[arith[k]].clone()])])])
    };
    // Besides small `μ`, those that cancel a leaf `ℓ` of `L` by itself in the region `reg`:
    // `ρ = μ·λ` for the coefficients of `ℓ` alone in `reg` and in `L`, with their counts.
    let derive_all = |reg: &T, l: &T| -> Vec<(i64, usize)> {
        let mut rl = Vec::new();
        leaves(reg, w, &mut rl);
        if rl.len() > MAX_WIDE_LEAVES {
            return Vec::new();
        }
        let region = Prog::new(reg, &rl, w);
        let r0 = region.at(0, w);
        let mut own = Vec::new();
        leaves(l, w, &mut own);
        let prog = Prog::new(l, &own, w);
        let l0 = prog.at(0, w);
        let mut found: Vec<(i64, usize)> = Vec::new();
        for (j, x) in own.iter().enumerate() {
            let Some(r) = rl.iter().position(|y| y == x) else { continue };
            let rho = region.at(1 << r, w).wrapping_sub(r0) & w.mask;
            let lambda = prog.at(1 << j, w).wrapping_sub(l0) & w.mask;
            let Some(mu) = solve_mul(lambda, rho, w).map(|m| w.signed(m)) else { continue };
            match found.iter_mut().find(|f| f.0 == mu) {
                Some(f) => f.1 += 1,
                None => found.push((mu, 1)),
            }
        }
        found.retain(|f| ![1, -1, 2, -2].contains(&f.0));
        found
    };
    let derive = |reg: &T, l: &T| derive_all(reg, l).into_iter().max_by_key(|f| f.1).map(|f| f.0);
    let derived: Vec<Option<i64>> = arith.iter().map(|&i| derive(t, &lv[i])).collect();
    // The `μ` that cancels `v` at bit 0, where a mask leaves the leaves of `L` a different
    // coefficient per bit: in `A·(L ^ (y | 0x7fffffff))`, `μ = A`.
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    let cancel: Vec<Option<i64>> = (0..arith.len())
        .map(|k| {
            let s = crate::lowbits::replace(t, std::slice::from_ref(&lv[arith[k]]), std::slice::from_ref(&ph[k]));
            let T::Var(name) = &ph[k] else { unreachable!("placeholders are variables") };
            let at = |x: u64| crate::eval::eval(&s, ty, &|v: &str| if v == name { x } else { 0 });
            let mu = w.signed(at(0)?.wrapping_sub(at(1)?) & w.mask);
            (![0, 1, -1, 2, -2].contains(&mu) && Some(mu) != derived[k]).then_some(mu)
        })
        .collect();
    let mut combos: Vec<Vec<(usize, i64)>> = Vec::new();
    for k in 0..arith.len() {
        if !same[k].is_empty() {
            combos.push(vec![(k, 0)]);
        }
        for mu in [1, -1, 2, -2].into_iter().chain(derived[k]).chain(cancel[k]) {
            combos.push(vec![(k, mu)]);
        }
        for k2 in k + 1..arith.len() {
            let firsts: Vec<i64> = [1, -1].into_iter().chain(derived[k]).collect();
            let seconds: Vec<i64> = [1, -1].into_iter().chain(derived[k2]).collect();
            for &a in &firsts {
                combos.extend(seconds.iter().map(|&b| vec![(k, a), (k2, b)]));
            }
        }
        // A second leaf's `μ` can exist only once the first is related: in
        // `7·(z + x) - 14·((2·x) & (z - x))`, `z - x` takes 7, then `2·x` cancels `x` with 7.
        for k2 in (0..arith.len()).filter(|&k2| k2 != k) {
            for (a, _) in derive_all(t, &lv[arith[k]]) {
                if let Some(b) = derive(&relate_one(t, k, a), &lv[arith[k2]]) {
                    let combo = if k < k2 { vec![(k, a), (k2, b)] } else { vec![(k2, b), (k, a)] };
                    if !combos.contains(&combo) {
                        combos.push(combo);
                    }
                }
            }
        }
    }
    // Rebuilds can be slow, so only the combinations that leave a semi-linear region the
    // fewest leaves (fewer than before), or another the fewest monomials (no more than
    // before), are rebuilt.
    let semi_used = |t: &T| -> Option<usize> {
        let t = &signed_products(t);
        let mut lv = Vec::new();
        leaves(t, w, &mut lv);
        Some(used_leaves(t, &lv, w)?.1.into_iter().filter(|&u| u).count())
    };
    // A region of more than `MAX_LEAVES` leaves is also scored by used leaves, since there
    // the cancelled ones are dropped before rebuilding.
    let (semi, wide) = (has_const_bitwise(t, w), lv.len() > MAX_LEAVES);
    let base_used = if semi || wide { Some(semi_used(t).unwrap_or(lv.len())) } else { None };
    let base_monos = if semi { None } else { crate::poly_mba::monomials(t, w) };
    // In a wide region, also those where `μ·L` cancels terms of the region, as in
    // `L + (~L & B)` with `L` written out there: no leaf goes, but the rebuild is smaller.
    let base_terms = wide.then(|| region_terms(t, w).0.len());
    let mut tried: Vec<(Option<usize>, Option<usize>, Option<usize>, Vec<(usize, i64)>, T)> = Vec::new();
    for combo in combos {
        let (mut from, mut to) = (Vec::new(), Vec::new());
        for &(k, _) in &combo {
            from.push(lv[arith[k]].clone());
            to.push(ph[k].clone());
            for &(j, comp) in &same[k] {
                if !from.contains(&lv[j]) {
                    from.push(lv[j].clone());
                    to.push(if comp { op(Op::Not, vec![ph[k].clone()]) } else { ph[k].clone() });
                }
            }
        }
        let mut s = crate::lowbits::replace(t, &from, &to);
        for &(k, mu) in combo.iter().filter(|c| c.1 != 0) {
            let rel = op(Op::Sub, vec![ph[k].clone(), lv[arith[k]].clone()]);
            s = op(Op::Add, vec![s, op(Op::Mul, vec![T::Num(mu), rel])]);
        }
        let by_used = base_used.and_then(|b| semi_used(&s).filter(|&u| u < b));
        let by_monos = match base_monos {
            _ if semi => None,
            Some(b) => crate::poly_mba::monomials(&s, w).filter(|&u| u <= b),
            None => (!wide).then_some(0),
        };
        let by_terms = base_terms.map(|_| region_terms(&s, w).0.len()).filter(|&n| base_terms.is_some_and(|b| n < b));
        if by_used.is_some() || by_monos.is_some() || by_terms.is_some() {
            tried.push((by_used, by_monos, by_terms, combo, s));
        }
    }
    let low_used = tried.iter().filter_map(|c| c.0).min();
    let low_monos = tried.iter().filter_map(|c| c.1).min();
    let low_terms = tried.iter().filter_map(|c| c.2).min();
    if low_used.is_none() && low_monos.is_none() && low_terms.is_none() {
        return None;
    }
    let mut best: Option<T> = None;
    let lowest = |c: &(Option<usize>, Option<usize>, Option<usize>, Vec<(usize, i64)>, T)| (c.0.is_some() && c.0 == low_used) || (c.1.is_some() && c.1 == low_monos) || (c.2.is_some() && c.2 == low_terms);
    for (_, _, by_terms, combo, s) in tried.into_iter().filter(lowest) {
        let mut slv = Vec::new();
        leaves(&s, w, &mut slv);
        let dropped = if wide && slv.len() > MAX_LEAVES { drop_leaves(&s, &slv, w) } else { None };
        let r = dropped.unwrap_or_else(|| rewrite(&s, w));
        let back: Vec<T> = combo.iter().map(|&(k, _)| lv[arith[k]].clone()).collect();
        let used: Vec<T> = combo.iter().map(|&(k, _)| ph[k].clone()).collect();
        let r = crate::lowbits::replace(&r, &used, &back);
        let mut rlv = Vec::new();
        leaves(&r, w, &mut rlv);
        // Arithmetic leaves that cancelled join the enclosing region, which is then rebuilt whole.
        let opaque = |lv: &[T]| lv.iter().filter(|l| matches!(l, T::Op(..)) && kind(l, w) != Kind::Bit).count();
        let (fewer, r) = if rlv.len() < lv.len() {
            (true, r)
        } else if wide && opaque(&rlv) < opaque(&lv) {
            let again = rewrite(&r, w);
            (size(&again) < size(t), again)
        } else {
            (false, r)
        };
        // In a wide region only results where leaves or terms cancelled: others shift extraction for little gain.
        if (!wide || fewer || (by_terms.is_some() && size(&r) < size(t))) && best.as_ref().is_none_or(|b| size(&r) < size(b)) {
            best = Some(r);
        }
    }
    best
}

/// Whether `t` is 0 at a few fixed points, a quick check before a proof.
pub(super) fn maybe_zero(t: &T, w: &Ctx) -> bool {
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    (1..=3u64).all(|k| {
        let env = |v: &str| v.bytes().fold(k.wrapping_mul(0x9e37_79b9_7f4a_7c15), |h, b| (h ^ b as u64).wrapping_mul(0x0100_0000_01b3).rotate_left(29));
        crate::eval::eval(t, ty, &env).is_none_or(|v| v & w.mask == 0)
    })
}

/// `t` with each product of non-constant factors written as `c·(f1 * f2 * ...)`,
/// its factors sorted and their negations and constant factors moved into `c`.
fn signed_products(t: &T) -> T {
    fn factors(t: &T, c: &mut i64, out: &mut Vec<T>) {
        match t {
            T::Op(op, a) if *op == Op::Mul => a.iter().for_each(|x| factors(x, c, out)),
            T::Op(op, a) if *op == Op::Neg => {
                *c = c.wrapping_neg();
                factors(&a[0], c, out);
            }
            T::Num(k) => *c = c.wrapping_mul(*k),
            _ => out.push(signed_products(t)),
        }
    }
    match t {
        T::Op(op, a) if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) => {
            let (mut c, mut fs) = (1i64, Vec::new());
            factors(t, &mut c, &mut fs);
            fs.sort_by_key(show);
            let p = fs.into_iter().reduce(|a, b| T::Op(Op::Mul, vec![a, b])).unwrap_or(T::Num(1));
            if c == 1 { p } else { T::Op(Op::Mul, vec![T::Num(c), p]) }
        }
        T::Op(op, a) => T::Op(*op, a.iter().map(signed_products).collect()),
        _ => t.clone(),
    }
}

/// Most leaves of an arithmetic operand that `unify_operands` compares by its values.
const MAX_UNIFY_LEAVES: usize = 8;

#[derive(PartialEq, Eq, Hash)]
enum OperandKey {
    /// The leaves, sorted, and the values on {0,1}^n (or their complements, whichever is smaller).
    Linear(Vec<T>, Vec<u64>),
    Exact(T),
}

struct Unifier<'a> {
    w: &'a Ctx,
    classes: crate::eval::FastMap<OperandKey, usize>,
    /// Per class: the smallest member and whether it is the complement of the class key.
    best: Vec<(usize, T, bool)>,
    of: crate::eval::FastMap<T, (usize, bool)>,
    built: Vec<Option<T>>,
    /// The first member of each class in each region, regions of products joined.
    first: crate::eval::FastMap<(usize, usize), (T, bool)>,
    regions: usize,
    /// Whether two members of a class written differently share a region.
    shared: bool,
}

impl Unifier<'_> {
    fn is_operand(&self, t: &T, in_bit: bool) -> bool {
        in_bit && !matches!(t, T::Op(Op::Not, _)) && matches!(t, T::Op(..)) && kind(t, self.w) == Kind::Lin
    }

    fn inner(&self, t: &T, in_bit: bool) -> bool {
        match t {
            T::Op(op, _) => kind(t, self.w) != Kind::Atom && (in_bit || matches!(op, Op::And | Op::Or | Op::Xor)),
            _ => false,
        }
    }

    /// `t` with each arithmetic operand of a bitwise operation replaced by `#c<class>`, or
    /// `~#c<class>` for the complement of the class key.
    fn classify(&mut self, t: &T, in_bit: bool, region: usize) -> T {
        let T::Op(op, a) = t else { return t.clone() };
        let inner = self.inner(t, in_bit);
        let operand = self.is_operand(t, in_bit);
        let product = matches!(op, Op::Mul) && !a.iter().any(|x| matches!(x, T::Num(_)));
        let sub = if operand || (kind(t, self.w) == Kind::Atom && !product) {
            self.regions += 1;
            self.regions
        } else {
            region
        };
        let abs = T::Op(*op, a.iter().map(|x| self.classify(x, inner && !operand, sub)).collect());
        if !operand {
            return abs;
        }
        let w = self.w;
        let mut lv = Vec::new();
        leaves(&abs, w, &mut lv);
        let (key, flip) = if lv.len() <= MAX_UNIFY_LEAVES && !has_const_bitwise(&abs, w) {
            lv.sort_by_key(term_hash);
            let prog = Prog::new(&abs, &lv, w);
            let vals: Vec<u64> = (0..1usize << lv.len()).map(|p| prog.at(p, w)).collect();
            let comp: Vec<u64> = vals.iter().map(|v| !v & w.mask).collect();
            if comp < vals { (OperandKey::Linear(lv, comp), true) } else { (OperandKey::Linear(lv, vals), false) }
        } else {
            (OperandKey::Exact(abs), false)
        };
        let n = self.classes.len();
        let id = *self.classes.entry(key).or_insert(n);
        let s = size(t);
        if id == self.best.len() {
            self.best.push((s, t.clone(), flip));
            self.built.push(None);
        } else {
            let b = &mut self.best[id];
            if (b.1 != *t || b.2 != flip) && s < b.0 {
                *b = (s, t.clone(), flip);
            }
        }
        match self.first.entry((id, region)) {
            std::collections::hash_map::Entry::Occupied(e) => self.shared |= *e.get() != (t.clone(), flip),
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert((t.clone(), flip));
            }
        }
        self.of.insert(t.clone(), (id, flip));
        let p = T::Var(format!("#c{id}"));
        if flip { T::Op(Op::Not, vec![p]) } else { p }
    }

    fn replace(&mut self, t: &T, in_bit: bool) -> T {
        let T::Op(op, a) = t else { return t.clone() };
        if self.is_operand(t, in_bit) {
            let (id, flip) = self.of[t];
            let r = match &self.built[id] {
                Some(r) => r.clone(),
                None => {
                    let T::Op(op, a) = self.best[id].1.clone() else { unreachable!() };
                    let r = T::Op(op, a.iter().map(|x| self.replace(x, false)).collect());
                    self.built[id] = Some(r.clone());
                    r
                }
            };
            return if flip != self.best[id].2 { T::Op(Op::Not, vec![r]) } else { r };
        }
        let inner = self.inner(t, in_bit);
        let a: Vec<T> = a.iter().map(|x| self.replace(x, inner)).collect();
        match (op, a.as_slice()) {
            (Op::Not, [T::Op(Op::Not, b)]) => b[0].clone(),
            _ => T::Op(*op, a),
        }
    }
}

/// `t` with the arithmetic operands of bitwise operations that are equal or complements
/// of each other as linear MBAs (equal values on {0,1}^n over the same leaves, which
/// proves it) written as the smallest of them or its `~`, so that the regions around
/// them share the leaf: `(a & (~x - z)) + ((~y - w) & (x + z))` with `a = y + w`.
pub(super) fn unify_operands(t: &T, w: &Ctx) -> T {
    let mut u = Unifier { w, classes: Default::default(), best: Vec::new(), of: Default::default(), built: Vec::new(), first: Default::default(), regions: 0, shared: false };
    u.classify(t, false, 0);
    if !u.shared {
        return t.clone();
    }
    u.replace(t, false)
}
