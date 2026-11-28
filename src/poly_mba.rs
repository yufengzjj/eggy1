//! Polynomial MBA simplification (GAMBA-style). Each bitwise subterm `f` over
//! leaves `x` is written in the conjunction basis `f(x) = Σ_S a_S·AND_S(x)`,
//! which is exact at every width (`AND_∅` is all ones, i.e. -1). Products are
//! then multiplied out and like terms merged. Conjunctions are treated as
//! independent variables, so equal normal forms imply equal values but not the
//! reverse.

use crate::eval::{Op, Term as T, size};
use crate::builtin_passes::Sub;
use crate::linear_mba::{Kind, max_leaves, Ctx, build_sum, Prog, const_shift, kind, leaves, simba_memo};
use crate::rust_vars::{Limit, limit};
use std::collections::BTreeMap;

/// Conjunction of leaves, as a set of leaf indices.
type Conj = u64;
/// Product of conjunctions, sorted; empty is the constant 1.
type Mono = Vec<Conj>;
type Poly = BTreeMap<Mono, u64>;

/// Constants `build` shifts the factors of a product by.
const SHIFTS: [i64; 3] = [-1, 0, 1];

struct Lims {
    max_monos: usize,
    factor_tries: usize,
    max_factor_monos: usize,
    max_factor_vars: usize,
    max_pivots: usize,
    max_roots: usize,
    max_factor_steps: usize,
    max_solutions: usize,
    max_shifted: usize,
    max_shifted_monos: usize,
    shifted_rest_ratio: usize,
    builds: usize,
}

impl Lims {
    fn read() -> Lims {
        Lims {
            max_monos: limit(Limit::PolyMaxMonos),
            factor_tries: limit(Limit::PolyFactorTries),
            max_factor_monos: limit(Limit::PolyMaxFactorMonos),
            max_factor_vars: limit(Limit::PolyMaxFactorVars),
            max_pivots: limit(Limit::PolyMaxPivots),
            max_roots: limit(Limit::PolyMaxRoots),
            max_factor_steps: limit(Limit::PolyMaxFactorSteps),
            max_solutions: limit(Limit::PolyMaxSolutions),
            max_shifted: limit(Limit::PolyMaxShifted),
            max_shifted_monos: limit(Limit::PolyMaxShiftedMonos),
            shifted_rest_ratio: limit(Limit::PolyShiftedRestRatio),
            builds: limit(Limit::PolyBuilds),
        }
    }
}

struct Expansion<'a, 's, 'r> {
    w: &'a Ctx,
    /// Rebuilds the leaves and the factors with a constant bitwise operation.
    sub: &'a Sub<'s>,
    /// Rebuilds the linear cofactors; `None` where nothing is built.
    region: Option<&'a Sub<'r>>,
    leaves: Vec<T>,
    lim: Lims,
    built: std::cell::RefCell<crate::eval::FastMap<(Poly, bool), T>>,
    builds: std::cell::Cell<usize>,
    linear: std::cell::RefCell<crate::eval::FastMap<Poly, T>>,
    /// When not empty, the bit sets on which every constant of a bitwise operation is
    /// constant; bitwise terms with constants then expand per set (`masked`).
    atoms: Vec<u64>,
    /// Per leaf, the leaves it is built from (itself, or the conjunction a masked leaf masks).
    base: Vec<Conj>,
}

impl<'a, 's, 'r> Expansion<'a, 's, 'r> {
    fn new(w: &'a Ctx, atoms: Vec<u64>, sub: &'a Sub<'s>, region: Option<&'a Sub<'r>>) -> Self {
        Expansion { w, sub, region, lim: Lims::read(), leaves: Vec::new(), built: Default::default(), builds: Default::default(), linear: Default::default(), atoms, base: Vec::new() }
    }

    fn leaf(&mut self, t: &T) -> Option<usize> {
        let t = self.sub.term(t, self.w);
        self.push_leaf(t, None)
    }

    fn push_leaf(&mut self, t: T, base: Option<Conj>) -> Option<usize> {
        if let Some(i) = self.leaves.iter().position(|l| *l == t) {
            return Some(i);
        }
        if self.leaves.len() == Conj::BITS as usize {
            return None;
        }
        self.leaves.push(t);
        let i = self.leaves.len() - 1;
        self.base.push(base.unwrap_or(1 << i));
        Some(i)
    }

    fn base_of(&self, c: Conj) -> Conj {
        (0..Conj::BITS as usize).filter(|i| c >> i & 1 == 1).fold(0, |acc, i| acc | self.base[i])
    }

    /// A bitwise term with constants as `Σ_M Σ_S a_S·(AND_S & M)` over the atoms `M`, from
    /// its truth table on each (`AND_∅ & M` is the constant `M`); exact at every width.
    fn masked(&mut self, t: &T) -> Option<Poly> {
        let mut lv = Vec::new();
        leaves(t, self.w, &mut lv);
        let n = lv.len();
        if n > max_leaves() {
            return self.leaf_poly(t);
        }
        let prog = Prog::new(t, &lv, self.w);
        let mask = self.w.mask;
        let vals: Vec<u64> = (0..1usize << n).map(|p| prog.run(|i| if p >> i & 1 == 1 { mask } else { 0 }, self.w)).collect();
        let ids: Vec<usize> = lv.iter().map(|l| self.leaf(l)).collect::<Option<_>>()?;
        let mut r = Poly::new();
        for m in self.atoms.clone() {
            let j = m.trailing_zeros();
            let mut a: Vec<u64> = vals.iter().map(|v| v >> j & 1).collect();
            for i in 0..n {
                for p in 0..1usize << n {
                    if p >> i & 1 == 1 {
                        a[p] = a[p].wrapping_sub(a[p ^ 1 << i]);
                    }
                }
            }
            for (s, &c) in a.iter().enumerate().filter(|(_, c)| **c != 0) {
                if s == 0 {
                    self.add_to(&mut r, vec![], c.wrapping_mul(m));
                    continue;
                }
                let conj = (0..n).filter(|i| s >> i & 1 == 1).fold(0, |acc, i| acc | 1 << ids[i]);
                let term = T::Op(Op::And, vec![self.conj_term(conj), T::Num(self.w.signed(m))]);
                let base = self.base_of(conj);
                let k = self.push_leaf(term, Some(base))?;
                self.add_to(&mut r, vec![1 << k], c);
            }
        }
        Some(r)
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
        if a.len() * b.len() > self.lim.max_monos {
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
        Some(match op {
            Op::Add => {
                let (x, y) = (self.poly(&a[0])?, self.poly(&a[1])?);
                self.sum(x, y)
            }
            Op::Sub => {
                let (x, y) = (self.poly(&a[0])?, self.poly(&a[1])?);
                self.sum(x, self.scale(y, neg1))
            }
            Op::Neg => {
                let x = self.poly(&a[0])?;
                self.scale(x, neg1)
            }
            Op::Not => {
                let x = self.poly(&a[0])?;
                self.sum(self.scale(x, neg1), self.constant(neg1))
            }
            Op::Mul if !self.atoms.is_empty() => {
                let (x, y) = (self.poly(&a[0])?, self.poly(&a[1])?);
                self.product(&x, &y)?
            }
            // Semi-linear factors expand into many independent leaves (`x | K`, ...);
            // rebuilt first, `(x + K) - (x | K)` is the single leaf `x & K`. Other factors
            // stay as they are: rebuilt, `~(y - 1)` becomes `-y`, a leaf unrelated to `y - 1`.
            Op::Mul => {
                let f = |t: &T| if has_const_bit(t, self.w) { self.sub.term(t, self.w) } else { t.clone() };
                let (x, y) = (self.poly(&f(&a[0]))?, self.poly(&f(&a[1]))?);
                self.product(&x, &y)?
            }
            Op::Shl if const_shift(&a[1], self.w).is_some() => {
                let k = const_shift(&a[1], self.w).unwrap();
                let x = self.poly(&a[0])?;
                self.scale(x, 1 << k)
            }
            Op::And | Op::Or | Op::Xor if kind(t, self.w) == Kind::Bit => self.bitwise(t)?,
            Op::And | Op::Or | Op::Xor if !self.atoms.is_empty() && kind(t, self.w) == Kind::ConstBit => self.masked(t)?,
            _ => self.leaf_poly(t)?,
        })
    }

    /// Conjunction-basis expansion of a bitwise term from its truth table.
    fn bitwise(&mut self, t: &T) -> Option<Poly> {
        let mut lv = Vec::new();
        leaves(t, self.w, &mut lv);
        let n = lv.len();
        if n > max_leaves() {
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
            .reduce(|acc, l| T::Op(Op::And, vec![acc, l]))
            .unwrap()
    }

    /// Rebuilds each part of the linear `p` whose conjunctions share leaves on
    /// its own, so that `simba` sees few leaves even when `p` has many.
    fn build_parts(&self, p: &Poly) -> T {
        let mut parts: Vec<(Conj, Vec<(u64, Conj)>)> = Vec::new();
        for (m, &c) in p.iter().filter(|(m, _)| m.len() == 1) {
            let mut part = (self.base_of(m[0]), vec![(c, m[0])]);
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
            built.push(simba_memo(&t, self.w, self.region.expect("an expansion that builds has a rebuild of cofactors")).unwrap_or(t));
        }
        built.into_iter().reduce(|a, b| T::Op(Op::Add, vec![a, b])).unwrap_or_else(|| build_sum(&[], konst, self.w))
    }

    /// `build_parts`, memoized.
    fn build_linear(&self, p: &Poly) -> T {
        if let Some(t) = self.linear.borrow().get(p) {
            return t.clone();
        }
        let b = self.build_parts(p);
        self.linear.borrow_mut().insert(p.clone(), b.clone());
        b
    }

    /// `p` of degree 2 as `(v + r)·(a·v + s)` with `r`, `s` affine in the other conjunctions,
    /// solved coefficient by coefficient: each `r_j` is a root of `a·r² - b_j·r + c_jj`,
    /// and every pair must give `c_jk = r_j·b_k + r_k·b_j - 2a·r_j·r_k`.
    fn factor2(&self, p: &Poly) -> Vec<(Poly, Poly)> {
        let mut out = Vec::new();
        if p.len() > self.lim.max_factor_monos || p.keys().any(|m| m.len() > 2) {
            return out;
        }
        let mut vars: Vec<Conj> = p.keys().flatten().copied().collect();
        vars.sort_unstable();
        vars.dedup();
        if vars.len() > self.lim.max_factor_vars {
            return out;
        }
        let coef = |m: &[Option<Conj>]| {
            let mut m: Mono = m.iter().flatten().copied().collect();
            m.sort_unstable();
            p.get(&m).copied().unwrap_or(0)
        };
        let mut pivots: Vec<(bool, Conj)> =
            vars.iter().filter(|&&v| p.keys().any(|m| m.len() == 2 && m.contains(&v))).map(|&v| (coef(&[Some(v), Some(v)]) & 1 == 0, v)).collect();
        pivots.sort_unstable();
        let mask = self.w.mask;
        for &(_, v) in pivots.iter().take(self.lim.max_pivots) {
            let a = coef(&[Some(v), Some(v)]);
            let us: Vec<Option<Conj>> = vars.iter().filter(|&&u| u != v).map(|&u| Some(u)).chain([None]).collect();
            let b: Vec<u64> = us.iter().map(|&u| coef(&[Some(v), u])).collect();
            let roots: Vec<Vec<u64>> = us.iter().zip(&b).map(|(&u, &bj)| self.quad_roots(a, bj, coef(&[u, u]))).collect();
            if roots.iter().any(|r| r.is_empty()) {
                continue;
            }
            let (mut r, mut sols, mut steps) = (vec![0u64; us.len()], Vec::new(), 0);
            let fits = |r: &[u64], k: usize| {
                (0..k).all(|j| {
                    let c = r[j].wrapping_mul(b[k]).wrapping_add(r[k].wrapping_mul(b[j])).wrapping_sub(a.wrapping_mul(2).wrapping_mul(r[j]).wrapping_mul(r[k]));
                    c & mask == coef(&[us[j], us[k]])
                })
            };
            self.assign(&roots, &mut r, 0, &fits, &mut steps, &mut sols);
            for r in sols {
                let (mut l1, mut l2) = (Poly::new(), Poly::new());
                self.add_to(&mut l1, vec![v], 1);
                self.add_to(&mut l2, vec![v], a);
                for (j, u) in us.iter().enumerate() {
                    let m: Mono = u.iter().copied().collect();
                    self.add_to(&mut l1, m.clone(), r[j]);
                    self.add_to(&mut l2, m, b[j].wrapping_sub(a.wrapping_mul(r[j])));
                }
                out.push((l1, l2));
            }
        }
        out
    }

    /// `p` of degree 3 as `(v + r)·Q` with `r` affine in the other conjunctions and `Q` the
    /// quotient: each `r_j` is a root of `-A·r³ + B_j·r² - C_jj·r + D_jjj` (`A` the `v³`
    /// coefficient), and the division by `v + r` must leave no remainder.
    fn factor3(&self, p: &Poly) -> Vec<(Poly, Poly)> {
        let mut out = Vec::new();
        if p.len() > self.lim.max_factor_monos || p.keys().any(|m| m.len() > 3) || !p.keys().any(|m| m.len() == 3) {
            return out;
        }
        let mut vars: Vec<Conj> = p.keys().flatten().copied().collect();
        vars.sort_unstable();
        vars.dedup();
        if vars.len() > self.lim.max_factor_vars {
            return out;
        }
        let coef = |m: &[Option<Conj>]| {
            let mut m: Mono = m.iter().flatten().copied().collect();
            m.sort_unstable();
            p.get(&m).copied().unwrap_or(0)
        };
        let mut pivots: Vec<(bool, Conj)> = vars.iter().filter(|&&v| coef(&[Some(v); 3]) != 0).map(|&v| (coef(&[Some(v); 3]) & 1 == 0, v)).collect();
        pivots.sort_unstable();
        let neg1 = self.w.mask;
        for &(_, v) in pivots.iter().take(self.lim.max_pivots) {
            let a = coef(&[Some(v); 3]);
            let us: Vec<Option<Conj>> = vars.iter().filter(|&&u| u != v).map(|&u| Some(u)).chain([None]).collect();
            let roots: Vec<Vec<u64>> = us.iter().map(|&u| self.cubic_roots(a, coef(&[Some(v), Some(v), u]), coef(&[Some(v), u, u]), coef(&[u, u, u]))).collect();
            if roots.iter().any(|r| r.is_empty()) {
                continue;
            }
            let mut parts = vec![Poly::new(); 4];
            for (m, &c) in p {
                let k = m.iter().filter(|&&x| x == v).count();
                self.add_to(&mut parts[k], m.iter().copied().filter(|&x| x != v).collect(), c);
            }
            let mut pick = vec![0usize; us.len()];
            // Fixed points where `p(-r, u)` must vanish, checked before dividing.
            let points: Vec<Vec<u64>> = (1..=2u64).map(|k| (0..us.len()).map(|j| k.wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(7 * j as u32 + 3) | 1).collect()).collect();
            for _ in 0..self.lim.max_factor_steps {
                let r: Vec<u64> = pick.iter().zip(&roots).map(|(&i, rs)| rs[i]).collect();
                let vanishes = points.iter().all(|pt| {
                    let val = |x: Conj| us.iter().position(|&u| u == Some(x)).map_or(0, |j| pt[j]);
                    let rv = us.iter().zip(&r).fold(0u64, |acc, (u, &c)| acc.wrapping_add(c.wrapping_mul(u.map_or(1, val))));
                    let at = |x: Conj| if x == v { rv.wrapping_neg() } else { val(x) };
                    p.iter().fold(0u64, |acc, (m, &c)| acc.wrapping_add(m.iter().fold(c, |f, &x| f.wrapping_mul(at(x))))) & neg1 == 0
                });
                if let Some(f) = vanishes.then(|| self.divide_cubic(&r, &us, v, a, &parts)).flatten() {
                    out.push(f);
                    if out.len() >= self.lim.max_solutions {
                        return out;
                    }
                }
                let Some(j) = (0..pick.len()).find(|&j| pick[j] + 1 < roots[j].len()) else { break };
                pick[j] += 1;
                pick[..j].iter_mut().for_each(|i| *i = 0);
            }
        }
        if out.is_empty() {
            self.factor3_by_coefficient(p, &vars, &mut out);
        }
        out
    }

    /// Factorings `L·Q` of a cubic `p` found from a conjunction `u` of degree 1 in every
    /// monomial: `L` divides `∂p/∂u`, so it is among the factors `factor2` finds there
    /// (`(x + z)·(z·y + z + y)`, which has no cube term).
    fn factor3_by_coefficient(&self, p: &Poly, vars: &[Conj], out: &mut Vec<(Poly, Poly)>) {
        let mut tried: Vec<Poly> = Vec::new();
        let once = |u: Conj| p.keys().all(|m| m.iter().filter(|&&x| x == u).count() <= 1) && p.keys().any(|m| m.len() == 3 && m.contains(&u));
        for &u in vars.iter().filter(|&&u| once(u)).take(self.lim.max_pivots) {
            let mut pu = Poly::new();
            for (m, &c) in p.iter().filter(|(m, _)| m.contains(&u)) {
                let mut rest = m.clone();
                rest.retain(|&x| x != u);
                self.add_to(&mut pu, rest, c);
            }
            for (l1, l2) in self.factor2(&pu).into_iter().take(self.lim.max_pivots) {
                for l in [l1, l2] {
                    let Some((&v, &c)) = l.iter().find_map(|(m, c)| (m.len() == 1 && c & 1 == 1).then(|| (&m[0], c))) else { continue };
                    let mut inv = c;
                    for _ in 0..6 {
                        inv = inv.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(inv)));
                    }
                    let l = self.scale(l, inv);
                    if tried.contains(&l) {
                        continue;
                    }
                    tried.push(l.clone());
                    if let Some(q) = self.divide(p, &l, v) {
                        out.push((l, q));
                        if out.len() >= self.lim.max_solutions {
                            return;
                        }
                    }
                }
            }
        }
    }

    /// `Q` with `p = l·Q`, for `l` linear with coefficient 1 on `v` and `p` of degree at most 3 in `v`.
    fn divide(&self, p: &Poly, l: &Poly, v: Conj) -> Option<Poly> {
        let neg1 = self.w.mask;
        let mut parts = vec![Poly::new(); 4];
        for (m, &c) in p {
            let k = m.iter().filter(|&&x| x == v).count();
            self.add_to(parts.get_mut(k)?, m.iter().copied().filter(|&x| x != v).collect(), c);
        }
        let mut rp = l.clone();
        rp.remove(&vec![v]);
        let div = |acc: &Poly, part: &Poly| self.product(&rp, acc).map(|x| self.sum(part.clone(), self.scale(x, neg1)));
        let q2 = parts[3].clone();
        let q1 = div(&q2, &parts[2])?;
        let q0 = div(&q1, &parts[1])?;
        if !div(&q0, &parts[0])?.is_empty() {
            return None;
        }
        let mut q = q0;
        for (k, qk) in [(1, q1), (2, q2)] {
            for (mut m, c) in qk {
                m.extend(std::iter::repeat_n(v, k));
                m.sort_unstable();
                self.add_to(&mut q, m, c);
            }
        }
        Some(q)
    }

    /// `(v + r, Q)` when `v + r` divides `Σ v^k·parts[k]` exactly (synthetic division), `Q` the quotient.
    fn divide_cubic(&self, r: &[u64], us: &[Option<Conj>], v: Conj, a: u64, parts: &[Poly]) -> Option<(Poly, Poly)> {
        let neg1 = self.w.mask;
        let mut rp = Poly::new();
        for (u, &c) in us.iter().zip(r) {
            self.add_to(&mut rp, u.iter().copied().collect(), c);
        }
        let div = |acc: &Poly, part: &Poly| self.product(&rp, acc).map(|x| self.sum(part.clone(), self.scale(x, neg1)));
        let q1 = div(&self.constant(a), &parts[2])?;
        let q0 = div(&q1, &parts[1])?;
        if !div(&q0, &parts[0])?.is_empty() {
            return None;
        }
        let mut l0 = rp.clone();
        self.add_to(&mut l0, vec![v], 1);
        let mut q = q0;
        for (mut m, c) in q1 {
            m.push(v);
            m.sort_unstable();
            self.add_to(&mut q, m, c);
        }
        self.add_to(&mut q, vec![v, v], a);
        Some((l0, q))
    }

    /// Roots of `-a·r³ + b·r² - c·r + d`, found by lifting bit by bit; when there are too
    /// many (a repeated root), the roots of its derivative and `b/3a` (odd `a`) that are roots.
    fn cubic_roots(&self, a: u64, b: u64, c: u64, d: u64) -> Vec<u64> {
        let f = |r: u64| d.wrapping_sub(c.wrapping_mul(r)).wrapping_add(b.wrapping_mul(r).wrapping_mul(r)).wrapping_sub(a.wrapping_mul(r).wrapping_mul(r).wrapping_mul(r));
        let mut rs = vec![0u64];
        for k in 0..self.w.w {
            let m = if k + 1 == 64 { u64::MAX } else { (1u64 << (k + 1)) - 1 };
            rs = rs.iter().flat_map(|&r| [r, r | 1 << k]).filter(|&r| f(r) & m == 0).collect();
            if rs.len() > self.lim.max_roots {
                let mut cands = self.quad_roots(a.wrapping_mul(3), b.wrapping_mul(2), c);
                if a & 1 == 1 {
                    let a3 = a.wrapping_mul(3);
                    let mut inv = a3;
                    for _ in 0..6 {
                        inv = inv.wrapping_mul(2u64.wrapping_sub(a3.wrapping_mul(inv)));
                    }
                    cands.push(b.wrapping_mul(inv) & self.w.mask);
                }
                rs = cands.into_iter().filter(|&r| f(r) & self.w.mask == 0).collect();
                break;
            }
        }
        rs.sort_by_key(|&r| self.w.signed(r).unsigned_abs());
        rs.dedup();
        rs
    }

    fn assign(&self, roots: &[Vec<u64>], r: &mut [u64], k: usize, fits: &dyn Fn(&[u64], usize) -> bool, steps: &mut usize, sols: &mut Vec<Vec<u64>>) {
        if k == roots.len() {
            sols.push(r.to_vec());
            return;
        }
        for &x in &roots[k] {
            *steps += 1;
            if *steps > self.lim.max_factor_steps || sols.len() >= self.lim.max_solutions {
                return;
            }
            r[k] = x;
            if fits(r, k) {
                self.assign(roots, r, k + 1, fits, steps, sols);
            }
        }
    }

    /// Roots of `a·r² - b·r + c`, smallest signed value first, found by lifting bit by bit;
    /// when there are too many, only `0`, `b/a` and `b/2a` (odd `a`) are kept, if they are roots.
    fn quad_roots(&self, a: u64, b: u64, c: u64) -> Vec<u64> {
        let f = |r: u64| a.wrapping_mul(r).wrapping_mul(r).wrapping_sub(b.wrapping_mul(r)).wrapping_add(c);
        let mut rs = vec![0u64];
        for k in 0..self.w.w {
            let m = if k + 1 == 64 { u64::MAX } else { (1u64 << (k + 1)) - 1 };
            rs = rs.iter().flat_map(|&r| [r, r | 1 << k]).filter(|&r| f(r) & m == 0).collect();
            if rs.len() > self.lim.max_roots {
                let mut inv = a;
                for _ in 0..6 {
                    inv = inv.wrapping_mul(2u64.wrapping_sub(a.wrapping_mul(inv)));
                }
                let odd = a & 1 == 1;
                let q = if odd { b.wrapping_mul(inv) & self.w.mask } else { 0 };
                let h = if odd && b & 1 == 0 { ((self.w.signed(b) >> 1) as u64).wrapping_mul(inv) & self.w.mask } else { 0 };
                rs = [0, q, h].into_iter().filter(|&r| f(r) & self.w.mask == 0).collect();
                rs.sort_by_key(|&r| self.w.signed(r).unsigned_abs());
                rs.dedup();
                return rs;
            }
        }
        rs.sort_by_key(|&r| self.w.signed(r).unsigned_abs());
        rs
    }

    /// Short term for `p`: pull out a common conjunction `f` (`p = f·q + r`)
    /// so that `q` gets rebuilt as a linear MBA, recursively; `top` for the whole polynomial.
    fn build(&self, p: &Poly, top: bool) -> T {
        let key = (p.clone(), top);
        if let Some(t) = self.built.borrow().get(&key) {
            return t.clone();
        }
        let t = self.build_uncached(p, top);
        self.built.borrow_mut().insert(key, t.clone());
        t
    }

    fn build_uncached(&self, p: &Poly, top: bool) -> T {
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
        let neg1 = self.w.mask;
        let side = |l: &Poly, neg: bool| match (neg, self.build_linear(&if neg { self.scale(l.clone(), neg1) } else { l.clone() })) {
            (true, T::Op(Op::Add, mut a)) if matches!(&a[0], T::Op(Op::Neg, _)) => {
                let T::Op(_, mut n) = a.remove(0) else { unreachable!() };
                T::Op(Op::Sub, vec![a.remove(0), n.remove(0)])
            }
            (_, t) => t,
        };
        let mul = |a: T, b: T| T::Op(Op::Mul, vec![a, b]);
        let factored = |target: &Poly, two: bool, three: bool| {
            let mut cands = Vec::new();
            if two {
                for (l1, l2) in self.factor2(target) {
                    cands.extend([false, true].map(|n| mul(side(&l1, n), side(&l2, n))));
                }
            }
            for (l0, q) in if three { self.factor3(target) } else { Vec::new() } {
                let quads = self.factor2(&q);
                if quads.is_empty() {
                    cands.push(mul(side(&l0, false), self.build(&q, false)));
                    cands.push(mul(side(&l0, true), self.build(&self.scale(q.clone(), neg1), false)));
                }
                for (l1, l2) in quads {
                    for (n0, n1, n2) in [(false, false, false), (true, true, false), (true, false, true), (false, true, true)] {
                        cands.push(mul(mul(side(&l0, n0), side(&l1, n1)), side(&l2, n2)));
                    }
                }
            }
            cands
        };
        let keep = |best: &mut Option<T>, cands: Vec<T>| {
            for cand in cands {
                if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
                    *best = Some(cand);
                }
            }
        };
        keep(&mut best, factored(p, true, false));
        // Pulling `f` out of its degree-1 monomial too (`x*y - 7*x` → `x*(y - 7)`)
        // can block a shorter linear rebuild of the rest, so try both, while the
        // budget lasts: the choices multiply at every level.
        self.builds.set(self.builds.get() + 1);
        let (tries, both) = if self.builds.get() > self.lim.builds { (1, 1) } else if top { (self.lim.factor_tries, 2) } else { (1, 2) };
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
            let prod = match self.build(&q, false) {
                T::Num(1) => ft,
                T::Num(-1) => T::Op(Op::Neg, vec![ft]),
                qt => T::Op(Op::Mul, vec![ft, qt]),
            };
            let cand = if r.is_empty() { prod } else { T::Op(Op::Add, vec![prod, self.build(&r, false)]) };
            if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
                best = Some(cand);
            }
        }
        // Tried last, so that they replace the forms above only when strictly smaller: a cubic
        // factoring, and both factorings of the part of degree 2 and up beside a linear rest
        // (`(x + y)·(x + y) + ~(w | y)`).
        if top {
            keep(&mut best, factored(p, false, true));
            let low: Poly = p.iter().filter(|(m, _)| m.len() <= 1).map(|(m, &c)| (m.clone(), c)).collect();
            if !low.is_empty() && low.len() < p.len() {
                let high: Poly = p.iter().filter(|(m, _)| m.len() >= 2).map(|(m, &c)| (m.clone(), c)).collect();
                let cands = factored(&high, true, true);
                if !cands.is_empty() {
                    let rest = self.build_linear(&low);
                    keep(&mut best, cands.into_iter().map(|c| T::Op(Op::Add, vec![c, rest.clone()])).collect());
                }
                // `(A + d)·(B + e)` with `e·A + d·B + d·e` moved into the linear rest
                // (`(z + 1)·(z + 1) + (z | x)` for `z·z + 3z + 1 + (x & ~z)`); the quotient of a
                // cubic factoring is shifted alone and rebuilt, as shifting its linear factor
                // would leave a rest of degree 2.
                let plus = |l: &Poly, c: u64| self.sum(l.clone(), self.constant(c));
                let with_rest = |prod: T, rest: Poly| if rest.is_empty() { prod } else { T::Op(Op::Add, vec![prod, self.build_linear(&rest)]) };
                let mut shifted = Vec::new();
                let small = |l: &Poly| l.len() <= self.lim.max_shifted_monos;
                let tries = if low.len() > self.lim.max_shifted_monos.saturating_mul(self.lim.shifted_rest_ratio) { 0 } else { self.lim.max_shifted };
                for (l1, l2) in self.factor2(&high).into_iter().filter(|(a, b)| small(a) && small(b)).take(tries) {
                    // Only shifts that leave the rest fewer monomials are built.
                    let mut cache: Vec<Option<[T; 2]>> = vec![None; 2 * SHIFTS.len()];
                    let mut side_of = |k: usize, l: &Poly, d: i64| cache[k].get_or_insert_with(|| [false, true].map(|n| side(&plus(l, d as u64 & neg1), n))).clone();
                    for (i, &d) in SHIFTS.iter().enumerate() {
                        for (j, &e) in SHIFTS.iter().enumerate().filter(|&(_, &e)| d != 0 || e != 0) {
                            let (du, eu) = (d as u64 & neg1, e as u64 & neg1);
                            let moved = self.sum(self.sum(self.scale(l1.clone(), eu), self.scale(l2.clone(), du)), self.constant(du.wrapping_mul(eu)));
                            let rest = self.sum(low.clone(), self.scale(moved, neg1));
                            if rest.len() >= low.len() {
                                continue;
                            }
                            let (a, b) = (side_of(i, &l1, d), side_of(SHIFTS.len() + j, &l2, e));
                            for n in 0..2 {
                                shifted.push(with_rest(mul(a[n].clone(), b[n].clone()), rest.clone()));
                            }
                        }
                    }
                }
                for (l0, q) in self.factor3(&high).into_iter().filter(|(a, _)| small(a)).take(tries) {
                    for e in SHIFTS.iter().filter(|&&e| e != 0) {
                        let e = *e as u64 & neg1;
                        let rest = self.sum(low.clone(), self.scale(l0.clone(), e.wrapping_neg()));
                        let q = plus(&q, e);
                        shifted.push(with_rest(mul(side(&l0, false), self.build(&q, false)), rest.clone()));
                        shifted.push(with_rest(mul(side(&l0, true), self.build(&self.scale(q, neg1), false)), rest));
                    }
                }
                keep(&mut best, shifted);
            }
        }
        best.unwrap()
    }
}

fn has_const_bit(t: &T, w: &Ctx) -> bool {
    match t {
        T::Op(_, a) => kind(t, w) == Kind::ConstBit || a.iter().any(|x| has_const_bit(x, w)),
        _ => false,
    }
}

/// Must only descend where `poly` expands structurally: `poly` turns other nodes
/// into leaves via `rewrite`, which would recurse back here on the same term.
fn has_product(t: &T, w: &Ctx) -> bool {
    let T::Op(op, a) = t else { return false };
    match op {
        Op::Mul if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)) => true,
        Op::Shl if const_shift(&a[1], w).is_none() => false,
        Op::Add | Op::Sub | Op::Neg | Op::Not | Op::Mul | Op::Shl => a.iter().any(|x| has_product(x, w)),
        _ => false,
    }
}

/// Number of monomials in the expansion of `t`, after the null polynomials are reduced
/// if that leaves fewer.
pub(crate) fn monomials(t: &T, w: &Ctx, sub: &Sub) -> Option<usize> {
    let mut ctx = Expansion::new(w, Vec::new(), sub, None);
    let p = ctx.poly(t)?;
    Some(p.len().min(ctx.reduce_null(&p).len()))
}

/// Rebuilt form of the polynomial region rooted at `t`, if it has a product of
/// non-constant terms or is a linear region with more than `max_leaves` leaves,
/// and the rebuilt form is smaller; the leaves rebuilt by `sub`, the linear cofactors by
/// `region`.
pub(crate) fn simplify_poly(t: &T, w: &Ctx, sub: &Sub, region: &Sub) -> Option<T> {
    // A bitwise root would be its own leaf, and `leaf` rewrites leaves.
    let wide = kind(t, w) == Kind::Lin && {
        let mut lv = Vec::new();
        leaves(t, w, &mut lv);
        lv.len() > max_leaves()
    };
    if !wide && !has_product(t, w) {
        return None;
    }
    use crate::stats;
    let mut ctx = Expansion::new(w, Vec::new(), sub, Some(region));
    let (p, q) = stats::time("poly_expand", || {
        let p = ctx.poly(t)?;
        let q = ctx.reduce_null(&p);
        Some((p, q))
    })?;
    // Far more monomials than nodes (products of bitwise terms over many leaves)
    // rarely rebuild smaller, and building them is slow.
    if p.len().min(q.len()) > limit(Limit::PolyMonosPerNode).saturating_mul(size(t)) {
        return None;
    }
    if p.len().min(q.len()) > limit(Limit::PolyBranchMonos) {
        ctx.builds.set(ctx.lim.builds);
    }
    let r = stats::time("poly_build", || ctx.build(if q.len() < p.len() { &q } else { &p }, true));
    // As many monomials, but a null polynomial can have made coefficients huge (`2^63·y` beside
    // a factor that keeps the rest even).
    let huge = |p: &Poly| p.values().any(|&c| w.signed(c).unsigned_abs() >= 1 << (w.w - 2));
    let r = if q.len() == p.len() && p.len() <= ctx.lim.max_factor_monos && huge(&p) && !huge(&q) {
        let s = ctx.build(&q, true);
        if size(&s) < size(&r) { s } else { r }
    } else {
        r
    };
    let r = match stats::try_pass("poly_masked", t, || masked_poly(t, p.len().min(q.len()), w, sub, region)) {
        Some(m) if size(&m) < size(&r) => {
            stats::won_among("poly_masked", &[("poly_masked", size(&m)), ("poly_build", size(&r))], size(t), &m);
            m
        }
        _ => r,
    };
    (size(&r) < size(t)).then_some(r)
}

/// `t` rebuilt with its bitwise terms with constants expanded per atom, so that products
/// selecting bits cancel (`(a | 2)·(a & 2) + (a & ~2)·(~a & 2)` is `2a`, `a = q | t`).
fn masked_poly(t: &T, monos: usize, w: &Ctx, sub: &Sub, region: &Sub) -> Option<T> {
    // One product is enough in a small term; in large ones that is most regions of
    // semi-linear inputs, at several times the run time.
    let (any, both) = masked_products(t, w);
    if any < 2 && (both == 0 || size(t) > limit(Limit::PolyMaxMaskedSize)) {
        return None;
    }
    let mut consts = Vec::new();
    collect_masks(t, &mut consts);
    let max_atoms = limit(Limit::PolyMaxAtoms);
    let mut atoms: Vec<u64> = Vec::new();
    let mut sigs: Vec<Vec<bool>> = Vec::new();
    for j in 0..w.w {
        let sig: Vec<bool> = consts.iter().map(|c| c >> j & 1 == 1).collect();
        match sigs.iter().position(|s| *s == sig) {
            Some(k) => atoms[k] |= 1 << j,
            None => {
                if atoms.len() == max_atoms {
                    return None;
                }
                sigs.push(sig);
                atoms.push(1 << j);
            }
        }
    }
    if atoms.len() < 2 {
        return None;
    }
    let mut ctx = Expansion::new(w, atoms, sub, Some(region));
    let p = ctx.poly(t)?;
    if p.len() > limit(Limit::PolyMaxMaskedMonos).max(limit(Limit::PolyMaskedMonosRatio).saturating_mul(monos)) {
        return None;
    }
    let q = ctx.reduce_null(&p);
    Some(ctx.build(if q.len() < p.len() { &q } else { &p }, true))
}

/// Products of non-constant factors where `poly` expands `t` structurally, with a bitwise
/// operation with a constant in one factor, and in both.
fn masked_products(t: &T, w: &Ctx) -> (usize, usize) {
    let T::Op(op, a) = t else { return (0, 0) };
    let inner = || a.iter().map(|x| masked_products(x, w)).fold((0, 0), |s, x| (s.0 + x.0, s.1 + x.1));
    match op {
        Op::Mul if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)) => {
            let (any, both) = inner();
            (any + usize::from(a.iter().any(|x| has_const_bit(x, w))), both + usize::from(a.iter().all(|x| has_const_bit(x, w))))
        }
        Op::Add | Op::Sub | Op::Neg | Op::Not | Op::Mul => inner(),
        _ => (0, 0),
    }
}

/// Constant operands of bitwise operations in `t`.
fn collect_masks(t: &T, out: &mut Vec<u64>) {
    let T::Op(op, a) = t else { return };
    for x in a {
        if let (Op::And | Op::Or | Op::Xor, T::Num(c)) = (op, x) {
            if !out.contains(&(*c as u64)) {
                out.push(*c as u64);
            }
        }
        collect_masks(x, out);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{NumType, eval};

    fn with_defaults<R>(f: impl FnOnce(&Sub, &Sub) -> R) -> R {
        crate::rust_vars::in_default_run(|| crate::builtin_passes::with_fns(&["rewrite", "simba_steps"], |s| f(&s[0], &s[1])))
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
    }

    fn op(name: Op, args: Vec<T>) -> T {
        T::Op(name, args)
    }

    fn bitwise(r: &mut Rng, depth: u32) -> T {
        if depth == 0 {
            return T::Var(["x", "y", "z"][(r.next() % 3) as usize].into());
        }
        match r.next() % 4 {
            0 => op(Op::Not, vec![bitwise(r, depth - 1)]),
            1 => op(Op::And, vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
            2 => op(Op::Or, vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
            _ => op(Op::Xor, vec![bitwise(r, depth - 1), bitwise(r, depth - 1)]),
        }
    }

    fn linear(r: &mut Rng) -> T {
        let terms = 1 + r.next() % 3;
        (0..terms)
            .map(|_| op(Op::Mul, vec![T::Num((r.next() % 11) as i64 - 5), bitwise(r, 2)]))
            .reduce(|a, b| op(Op::Add, vec![a, b]))
            .unwrap()
    }

    /// The same value written differently: operands of `Add`/`Mul` swapped.
    fn swapped(t: &T) -> T {
        match t {
            T::Op(o, a) if *o == Op::Add || *o == Op::Mul => op(*o, vec![swapped(&a[1]), swapped(&a[0])]),
            T::Op(o, a) => op(*o, a.iter().map(swapped).collect()),
            _ => t.clone(),
        }
    }

    #[test]
    fn products_of_linear_mbas() {
        with_defaults(|rw, _| {
            let mut r = Rng(0x7f4a7c15_9e3779b9);
            for bits in [8u32, 64] {
                let w = Ctx::new(bits);
                let ty = NumType { bits, signed: false };
                for _ in 0..300 {
                    let t = op(Op::Add, vec![op(Op::Mul, vec![linear(&mut r), linear(&mut r)]), linear(&mut r)]);
                    let alt = rw.term(&t, &w);
                    for _ in 0..32 {
                        let (x, y, z) = (r.next(), r.next(), r.next());
                        let env = |v: &str| match v {
                            "x" => x,
                            "y" => y,
                            _ => z,
                        };
                        assert_eq!(eval(&t, ty, &env), eval(&alt, ty, &env), "w={bits}\n  {t:?}\n  {alt:?}");
                    }
                    let zero = op(Op::Sub, vec![t.clone(), swapped(&t)]);
                    assert_eq!(rw.term(&zero, &w), T::Num(0), "w={bits}: {t:?}");
                }
            }
        })
    }

    #[test]
    fn cubes_of_linear_mbas() {
        with_defaults(|rw, region| {
            let mut r = Rng(0x2545_f491_4f6c_dd1d);
            let mut factored = 0;
            for bits in [8u32, 64] {
                let w = Ctx::new(bits);
                let ty = NumType { bits, signed: false };
                for k in 0..200 {
                    let (a, b) = (linear(&mut r), linear(&mut r));
                    let c = if k % 2 == 0 { a.clone() } else { linear(&mut r) };
                    let t = op(Op::Mul, vec![op(Op::Mul, vec![a.clone(), b]), c]);
                    let mut ctx = Expansion::new(&w, Vec::new(), rw, Some(region));
                    let Some(p) = ctx.poly(&t) else { continue };
                    let built = ctx.build(&p, true);
                    factored += (size(&built) <= size(&t)) as u32;
                    for _ in 0..32 {
                        let (x, y, z) = (r.next(), r.next(), r.next());
                        let env = |v: &str| match v {
                            "x" => x,
                            "y" => y,
                            _ => z,
                        };
                        assert_eq!(eval(&t, ty, &env), eval(&built, ty, &env), "w={bits}\n  {t:?}\n  {built:?}");
                    }
                }
            }
            assert!(factored > 50, "factored {factored}");
        })
    }

    /// Products of bitwise terms with constants over one or two leaves, rebuilt with the
    /// masked expansion, keep their value.
    #[test]
    fn masked_products_keep_value() {
        with_defaults(|rw, region| {
            let mut r = Rng(0x94d0_49bb_1331_11eb);
            let mut built = 0;
            for bits in [8u32, 64] {
                let w = Ctx::new(bits);
                let ty = NumType { bits, signed: false };
                let masks = [1i64, 2, 3, -3, -4, 0x30];
                for _ in 0..300 {
                    let factor = |r: &mut Rng| {
                        let v = bitwise(r, 1);
                        let k = T::Num(masks[(r.next() % masks.len() as u64) as usize]);
                        let f = op([Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize], vec![v, k]);
                        if r.next() % 3 == 0 { op(Op::Not, vec![f]) } else { f }
                    };
                    let p1 = op(Op::Mul, vec![factor(&mut r), factor(&mut r)]);
                    let p2 = op(Op::Mul, vec![factor(&mut r), factor(&mut r)]);
                    let t = op(Op::Add, vec![p1, p2]);
                    let Some(m) = masked_poly(&t, 0, &w, rw, region) else { continue };
                    built += 1;
                    for _ in 0..32 {
                        let (x, y, z) = (r.next(), r.next(), r.next());
                        let env = |v: &str| match v {
                            "x" => x,
                            "y" => y,
                            _ => z,
                        };
                        assert_eq!(eval(&t, ty, &env), eval(&m, ty, &env), "w={bits}\n  {t:?}\n  {m:?}");
                    }
                }
            }
            assert!(built > 100, "built {built}");
        })
    }
}
