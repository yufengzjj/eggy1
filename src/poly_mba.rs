//! Polynomial MBA simplification (GAMBA-style). Each bitwise subterm `f` over
//! leaves `x` is written in the conjunction basis `f(x) = Σ_S a_S·AND_S(x)`,
//! which is exact at every width (`AND_∅` is all ones, i.e. -1). Products are
//! then multiplied out and like terms merged. Conjunctions are treated as
//! independent variables, so equal normal forms imply equal values but not the
//! reverse.

use crate::eval::{Term as T, size};
use crate::linear_mba::{Kind, MAX_LEAVES, Width, build_sum, Prog, const_shift, kind, leaves, rewrite, simba_memo};
use std::collections::BTreeMap;

/// Conjunction of leaves, as a set of leaf indices.
type Conj = u64;
/// Product of conjunctions, sorted; empty is the constant 1.
type Mono = Vec<Conj>;
type Poly = BTreeMap<Mono, u64>;

const MAX_MONOS: usize = 4096;
/// Candidate factors tried at the top level of `build`; one below it.
const FACTOR_TRIES: usize = 3;
/// Most products `build` tries with every choice before it keeps to the first.
const MAX_BUILDS: usize = 512;

struct Ctx<'a> {
    w: &'a Width,
    leaves: Vec<T>,
    built: std::cell::RefCell<std::collections::HashMap<(Poly, usize), T>>,
    builds: std::cell::Cell<usize>,
}

impl Ctx<'_> {
    fn leaf(&mut self, t: &T) -> Option<usize> {
        let t = rewrite(t, self.w);
        if let Some(i) = self.leaves.iter().position(|l| *l == t) {
            return Some(i);
        }
        if self.leaves.len() == Conj::BITS as usize {
            return None;
        }
        self.leaves.push(t);
        Some(self.leaves.len() - 1)
    }

    fn add_to(&self, p: &mut Poly, m: Mono, c: u64) {
        let e = p.entry(m.clone()).or_insert(0);
        *e = e.wrapping_add(c) & self.w.mask;
        if *e == 0 {
            p.remove(&m);
        }
    }

    fn constant(&self, c: u64) -> Poly {
        let mut p = Poly::new();
        self.add_to(&mut p, vec![], c);
        p
    }

    fn scale(&self, p: Poly, c: u64) -> Poly {
        let mut r = Poly::new();
        for (m, v) in p {
            self.add_to(&mut r, m, v.wrapping_mul(c));
        }
        r
    }

    fn sum(&self, mut a: Poly, b: Poly) -> Poly {
        for (m, v) in b {
            self.add_to(&mut a, m, v);
        }
        a
    }

    fn product(&self, a: &Poly, b: &Poly) -> Option<Poly> {
        if a.len() * b.len() > MAX_MONOS {
            return None;
        }
        let mut r = Poly::new();
        for (ma, ca) in a {
            for (mb, cb) in b {
                let mut m = ma.clone();
                m.extend(mb);
                m.sort_unstable();
                self.add_to(&mut r, m, ca.wrapping_mul(*cb));
            }
        }
        Some(r)
    }

    fn leaf_poly(&mut self, t: &T) -> Option<Poly> {
        let i = self.leaf(t)?;
        let mut p = Poly::new();
        self.add_to(&mut p, vec![1 << i], 1);
        Some(p)
    }

    fn poly(&mut self, t: &T) -> Option<Poly> {
        let neg1 = self.w.mask;
        let T::Op(op, a) = t else {
            return match t {
                T::Num(c) => Some(self.constant(*c as u64)),
                _ => self.leaf_poly(t),
            };
        };
        Some(match op.as_str() {
            "Add" => {
                let (x, y) = (self.poly(&a[0])?, self.poly(&a[1])?);
                self.sum(x, y)
            }
            "Sub" => {
                let (x, y) = (self.poly(&a[0])?, self.poly(&a[1])?);
                self.sum(x, self.scale(y, neg1))
            }
            "Neg" => {
                let x = self.poly(&a[0])?;
                self.scale(x, neg1)
            }
            "Not" => {
                let x = self.poly(&a[0])?;
                self.sum(self.scale(x, neg1), self.constant(neg1))
            }
            // Semi-linear factors expand into many independent leaves (`x | K`, ...);
            // rebuilt first, `(x + K) - (x | K)` is the single leaf `x & K`. Other factors
            // stay as they are: rebuilt, `~(y - 1)` becomes `-y`, a leaf unrelated to `y - 1`.
            "Mul" => {
                let f = |t: &T| if has_const_bit(t, self.w) { rewrite(t, self.w) } else { t.clone() };
                let (x, y) = (self.poly(&f(&a[0]))?, self.poly(&f(&a[1]))?);
                self.product(&x, &y)?
            }
            "Shl" if const_shift(&a[1], self.w).is_some() => {
                let k = const_shift(&a[1], self.w).unwrap();
                let x = self.poly(&a[0])?;
                self.scale(x, 1 << k)
            }
            "And" | "Or" | "Xor" if kind(t, self.w) == Kind::Bit => self.bitwise(t)?,
            _ => self.leaf_poly(t)?,
        })
    }

    /// Conjunction-basis expansion of a bitwise term from its truth table.
    fn bitwise(&mut self, t: &T) -> Option<Poly> {
        let mut lv = Vec::new();
        leaves(t, self.w, &mut lv);
        let n = lv.len();
        if n > MAX_LEAVES {
            return self.leaf_poly(t);
        }
        let prog = Prog::new(t, &lv, self.w);
        let mut a: Vec<u64> = (0..1usize << n).map(|p| prog.at(p, self.w) & 1).collect();
        // Möbius transform: a[S] = Σ_{R ⊆ S} (-1)^{|S|-|R|} f(R).
        for i in 0..n {
            for p in 0..1usize << n {
                if p >> i & 1 == 1 {
                    a[p] = a[p].wrapping_sub(a[p ^ 1 << i]);
                }
            }
        }
        let ids: Vec<usize> = lv.iter().map(|l| self.leaf(l)).collect::<Option<_>>()?;
        let mut r = self.constant(a[0].wrapping_neg());
        for (s, &c) in a.iter().enumerate().skip(1) {
            let conj = (0..n).filter(|i| s >> i & 1 == 1).fold(0, |acc, i| acc | 1 << ids[i]);
            self.add_to(&mut r, vec![conj], c);
        }
        Some(r)
    }

    /// `p` modulo the polynomials that vanish everywhere: in the falling-factorial
    /// basis, `c·Π x_i^(k_i)` vanishes iff `2^w` divides `c·Π k_i!`, so each such
    /// coefficient is reduced modulo `2^(w - Σ v2(k_i!))` (to its smallest signed value).
    fn reduce_null(&self, p: &Poly) -> Poly {
        let w = self.w.w;
        let top = p.keys().flat_map(|m| m.chunk_by(|a, b| a == b).map(|r| r.len())).max().unwrap_or(0);
        let (mut s1, mut s2) = (vec![vec![1u64]], vec![vec![1u64]]);
        for k in 0..top {
            let (a, b) = (&s1[k], &s2[k]);
            let at = |v: &Vec<u64>, j: usize| v.get(j).copied().unwrap_or(0);
            s1.push((0..=k + 1).map(|j| (if j > 0 { at(a, j - 1) } else { 0 }).wrapping_sub((k as u64).wrapping_mul(at(a, j)))).collect());
            s2.push((0..=k + 1).map(|j| (if j > 0 { at(b, j - 1) } else { 0 }).wrapping_add((j as u64).wrapping_mul(at(b, j)))).collect());
        }
        let ff = self.change_basis(p, &s2);
        let mut red = Poly::new();
        for (m, c) in ff {
            let e: u32 = m.chunk_by(|a, b| a == b).map(|r| r.len() as u32 - r.len().count_ones()).sum();
            if e >= w {
                continue;
            }
            let sh = 64 - (w - e);
            self.add_to(&mut red, m, ((c << sh) as i64 >> sh) as u64);
        }
        self.change_basis(&red, &s1)
    }

    /// Replaces each power `x^k` (a run of `k` equal conjunctions) by `Σ_j table[k][j]·x^j`.
    fn change_basis(&self, p: &Poly, table: &[Vec<u64>]) -> Poly {
        let mut r = Poly::new();
        for (m, &c) in p {
            let mut terms: Vec<(Mono, u64)> = vec![(vec![], c)];
            for run in m.chunk_by(|a, b| a == b) {
                let row = &table[run.len()];
                terms = terms
                    .iter()
                    .flat_map(|(t, tc)| {
                        (1..row.len()).filter(|&j| row[j] != 0).map(move |j| {
                            let mut t = t.clone();
                            t.extend(std::iter::repeat_n(run[0], j));
                            (t, tc.wrapping_mul(row[j]))
                        })
                    })
                    .collect();
            }
            for (t, tc) in terms {
                self.add_to(&mut r, t, tc);
            }
        }
        r
    }

    fn conj_term(&self, c: Conj) -> T {
        (0..Conj::BITS as usize)
            .filter(|i| c >> i & 1 == 1)
            .map(|i| self.leaves[i].clone())
            .reduce(|acc, l| T::Op("And".into(), vec![acc, l]))
            .unwrap()
    }

    /// Rebuilds each part of the linear `p` whose conjunctions share leaves on
    /// its own, so that `simba` sees few leaves even when `p` has many.
    fn build_linear(&self, p: &Poly) -> T {
        let mut parts: Vec<(Conj, Vec<(u64, Conj)>)> = Vec::new();
        for (m, &c) in p.iter().filter(|(m, _)| m.len() == 1) {
            let mut part = (m[0], vec![(c, m[0])]);
            parts.retain(|q| {
                let joined = q.0 & part.0 != 0;
                if joined {
                    part.0 |= q.0;
                    part.1.extend(&q.1);
                }
                !joined
            });
            parts.push(part);
        }
        let mut konst = p.get(&vec![]).copied().unwrap_or(0);
        let mut built = Vec::new();
        for (_, ms) in &parts {
            let terms: Vec<(u64, T)> = ms.iter().map(|&(c, m)| (c, self.conj_term(m))).collect();
            let t = build_sum(&terms, konst, self.w);
            konst = 0;
            built.push(simba_memo(&t, self.w).unwrap_or(t));
        }
        built.into_iter().reduce(|a, b| T::Op("Add".into(), vec![a, b])).unwrap_or_else(|| build_sum(&[], konst, self.w))
    }

    /// Short term for `p`: pull out a common conjunction `f` (`p = f·q + r`)
    /// so that `q` gets rebuilt as a linear MBA, recursively.
    fn build(&self, p: &Poly, tries: usize) -> T {
        let key = (p.clone(), tries);
        if let Some(t) = self.built.borrow().get(&key) {
            return t.clone();
        }
        let t = self.build_uncached(p, tries);
        self.built.borrow_mut().insert(key, t.clone());
        t
    }

    fn build_uncached(&self, p: &Poly, tries: usize) -> T {
        if p.keys().all(|m| m.len() <= 1) {
            return self.build_linear(p);
        }
        let mut counts: BTreeMap<Conj, usize> = BTreeMap::new();
        for m in p.keys().filter(|m| m.len() >= 2) {
            let mut seen = m.clone();
            seen.dedup();
            seen.into_iter().for_each(|c| *counts.entry(c).or_default() += 1);
        }
        let mut cands: Vec<(Conj, usize)> = counts.into_iter().collect();
        cands.sort_by_key(|&(c, n)| (std::cmp::Reverse(n), c.count_ones()));
        let mut best: Option<T> = None;
        // Pulling `f` out of its degree-1 monomial too (`x*y - 7*x` → `x*(y - 7)`)
        // can block a shorter linear rebuild of the rest, so try both, while the
        // budget lasts: the choices multiply at every level.
        self.builds.set(self.builds.get() + 1);
        let (tries, both) = if self.builds.get() > MAX_BUILDS { (1, 1) } else { (tries, 2) };
        let choices = cands.iter().take(tries).flat_map(|&(f, _)| [(f, false), (f, true)].into_iter().take(both));
        for (f, with_linear) in choices {
            let (mut q, mut r) = (Poly::new(), Poly::new());
            for (m, &c) in p {
                match m.iter().position(|&x| x == f).filter(|_| with_linear || m.len() >= 2) {
                    Some(k) => {
                        let mut rest = m.clone();
                        rest.remove(k);
                        q.insert(rest, c);
                    }
                    None => {
                        r.insert(m.clone(), c);
                    }
                }
            }
            let ft = self.conj_term(f);
            let prod = match self.build(&q, 1) {
                T::Num(1) => ft,
                T::Num(-1) => T::Op("Neg".into(), vec![ft]),
                qt => T::Op("Mul".into(), vec![ft, qt]),
            };
            let cand = if r.is_empty() { prod } else { T::Op("Add".into(), vec![prod, self.build(&r, 1)]) };
            if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
                best = Some(cand);
            }
        }
        best.unwrap()
    }
}

fn has_const_bit(t: &T, w: &Width) -> bool {
    match t {
        T::Op(_, a) => kind(t, w) == Kind::ConstBit || a.iter().any(|x| has_const_bit(x, w)),
        _ => false,
    }
}

/// Must only descend where `poly` expands structurally: `poly` turns other nodes
/// into leaves via `rewrite`, which would recurse back here on the same term.
fn has_product(t: &T, w: &Width) -> bool {
    let T::Op(op, a) = t else { return false };
    match op.as_str() {
        "Mul" if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)) => true,
        "Shl" if const_shift(&a[1], w).is_none() => false,
        "Add" | "Sub" | "Neg" | "Not" | "Mul" | "Shl" => a.iter().any(|x| has_product(x, w)),
        _ => false,
    }
}

/// Rebuilt form of the polynomial region rooted at `t`, if it has a product of
/// non-constant terms or is a linear region with more than `MAX_LEAVES` leaves,
/// and the rebuilt form is smaller.
/// Number of monomials in the expansion of `t`, after the null polynomials are reduced
/// if that leaves fewer.
pub(crate) fn monomials(t: &T, w: &Width) -> Option<usize> {
    let mut ctx = Ctx { w, leaves: Vec::new(), built: Default::default(), builds: Default::default() };
    let p = ctx.poly(t)?;
    Some(p.len().min(ctx.reduce_null(&p).len()))
}

pub(crate) fn simplify_poly(t: &T, w: &Width) -> Option<T> {
    // A bitwise root would be its own leaf, and `leaf` rewrites leaves.
    let wide = kind(t, w) == Kind::Lin && {
        let mut lv = Vec::new();
        leaves(t, w, &mut lv);
        lv.len() > MAX_LEAVES
    };
    if !wide && !has_product(t, w) {
        return None;
    }
    let mut ctx = Ctx { w, leaves: Vec::new(), built: Default::default(), builds: Default::default() };
    let p = ctx.poly(t)?;
    let q = ctx.reduce_null(&p);
    // Far more monomials than nodes (products of bitwise terms over many leaves)
    // rarely rebuild smaller, and building them is slow.
    if p.len().min(q.len()) > 4 * size(t) {
        return None;
    }
    let r = ctx.build(if q.len() < p.len() { &q } else { &p }, FACTOR_TRIES);
    (size(&r) < size(t)).then_some(r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{NumType, eval};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    fn op(name: &str, args: Vec<T>) -> T {
        T::Op(name.into(), args)
    }

    fn bitwise(r: &mut Rng, depth: u32) -> T {
        if depth == 0 {
            return T::Var(["x", "y", "z"][(r.next() % 3) as usize].into());
        }
        match r.next() % 4 {
            0 => op("Not", vec![bitwise(r, depth - 1)]),
            1 => op("And", vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
            2 => op("Or", vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
            _ => op("Xor", vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
        }
    }

    fn linear(r: &mut Rng) -> T {
        let terms = 1 + r.next() % 3;
        (0..terms)
            .map(|_| op("Mul", vec![T::Num((r.next() % 11) as i64 - 5), bitwise(r, 2)]))
            .reduce(|a, b| op("Add", vec![a, b]))
            .unwrap()
    }

    /// The same value written differently: operands of `Add`/`Mul` swapped.
    fn swapped(t: &T) -> T {
        match t {
            T::Op(o, a) if o == "Add" || o == "Mul" => op(o, vec![swapped(&a[1]), swapped(&a[0])]),
            T::Op(o, a) => op(o, a.iter().map(swapped).collect()),
            _ => t.clone(),
        }
    }

    #[test]
    fn products_of_linear_mbas() {
        let mut r = Rng(0x7f4a7c15_9e3779b9);
        for bits in [8u32, 64] {
            let w = Width::new(bits);
            let ty = NumType { bits, signed: false };
            for _ in 0..300 {
                let t = op("Add", vec![op("Mul", vec![linear(&mut r), linear(&mut r)]), linear(&mut r)]);
                let alt = rewrite(&t, &w);
                for _ in 0..32 {
                    let (x, y, z) = (r.next(), r.next(), r.next());
                    let env = |v: &str| match v {
                        "x" => x,
                        "y" => y,
                        _ => z,
                    };
                    assert_eq!(eval(&t, ty, &env), eval(&alt, ty, &env), "w={bits}\n  {t:?}\n  {alt:?}");
                }
                let zero = op("Sub", vec![t.clone(), swapped(&t)]);
                assert_eq!(rewrite(&zero, &w), T::Num(0), "w={bits}: {t:?}");
            }
        }
    }
}
