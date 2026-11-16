//! Linear MBA simplification (SiMBA-style). A linear MBA, i.e. a sum of
//! constant multiples of bitwise functions, is fully determined by its values
//! on {0,1}^n, so it can be rebuilt from those values in a minimal form.
//! Subterms that are not linear (`x*y`, `x >> 3`, ...) are treated as opaque
//! variables; the identity holds for any value they take. Bitwise operations
//! with constant operands (`x & 0xff`) make the region semi-linear: each bit
//! position then has its own bitwise function, see `semi_linear`.

use crate::eval::{Term as T, parse, show, size};
use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Kind {
    /// Bitwise function of the leaves.
    Bit,
    /// Bitwise function of the leaves and constants other than 0 and -1.
    ConstBit,
    /// Linear combination of bitwise functions.
    Lin,
    /// Not linear: an opaque leaf for the enclosing region.
    Atom,
}

pub(crate) struct Width {
    pub(crate) w: u32,
    pub(crate) mask: u64,
}

impl Width {
    pub(crate) fn new(w: u32) -> Width {
        Width { w, mask: if w == 64 { u64::MAX } else { (1u64 << w) - 1 } }
    }
    fn signed(&self, v: u64) -> i64 {
        let sh = 64 - self.w;
        ((v << sh) as i64) >> sh
    }
}

pub(crate) fn const_shift(t: &T, w: &Width) -> Option<u32> {
    match t {
        T::Num(k) if (0..w.w as i64).contains(k) => Some(*k as u32),
        _ => None,
    }
}

pub(crate) fn kind(t: &T, w: &Width) -> Kind {
    let bit = |k: Kind| if k == Kind::Atom { Kind::Bit } else { k };
    match t {
        T::Var(_) => Kind::Bit,
        T::Num(c) => {
            let c = *c as u64 & w.mask;
            if c == 0 || c == w.mask { Kind::Bit } else { Kind::Lin }
        }
        T::Op(op, a) => match op.as_str() {
            "Not" => bit(kind(&a[0], w)),
            "Neg" | "Add" | "Sub" => Kind::Lin,
            "And" | "Or" | "Xor" => {
                let operand = |x: &T| match (x, kind(x, w)) {
                    (T::Num(_), Kind::Lin) => Kind::ConstBit,
                    (_, k) => bit(k),
                };
                match (operand(&a[0]), operand(&a[1])) {
                    (Kind::Bit, Kind::Bit) => Kind::Bit,
                    (Kind::Bit | Kind::ConstBit, Kind::Bit | Kind::ConstBit) => Kind::ConstBit,
                    _ => Kind::Atom,
                }
            }
            "Mul" if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => Kind::Lin,
            "Shl" if const_shift(&a[1], w).is_some() => Kind::Lin,
            _ => Kind::Atom,
        },
    }
}

/// Leaves of the linear region rooted at `t`: variables and atom subterms.
pub(crate) fn leaves(t: &T, w: &Width, out: &mut Vec<T>) {
    match t {
        T::Num(_) => {}
        T::Var(_) => {
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
        T::Op(_, a) => {
            if kind(t, w) == Kind::Atom {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            } else {
                a.iter().for_each(|x| leaves(x, w, out));
            }
        }
    }
}

pub(crate) fn eval(t: &T, w: &Width, leaf_vals: &[(T, u64)]) -> u64 {
    if let Some((_, v)) = leaf_vals.iter().find(|(l, _)| l == t) {
        return *v;
    }
    let m = w.mask;
    let e = |x: &T| eval(x, w, leaf_vals);
    match t {
        T::Num(c) => *c as u64 & m,
        T::Var(_) => unreachable!("variable missing from leaves"),
        T::Op(op, a) => {
            let r = match op.as_str() {
                "Not" => !e(&a[0]),
                "Neg" => e(&a[0]).wrapping_neg(),
                "Add" => e(&a[0]).wrapping_add(e(&a[1])),
                "Sub" => e(&a[0]).wrapping_sub(e(&a[1])),
                "Mul" => e(&a[0]).wrapping_mul(e(&a[1])),
                "And" => e(&a[0]) & e(&a[1]),
                "Or" => e(&a[0]) | e(&a[1]),
                "Xor" => e(&a[0]) ^ e(&a[1]),
                "Shl" => e(&a[0]) << const_shift(&a[1], w).unwrap(),
                _ => unreachable!("non-linear op {op} inside a linear region"),
            };
            r & m
        }
    }
}

#[derive(Clone)]
enum B {
    V(usize),
    Not(Box<B>),
    Bin(&'static str, Box<B>, Box<B>),
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
            let known: Vec<(usize, usize, B)> = best
                .iter()
                .enumerate()
                .filter_map(|(tt, e)| e.as_ref().map(|(c, b)| (tt, *c, b.clone())))
                .collect();
            let mut changed = false;
            let mut offer = |best: &mut Vec<Option<(usize, B)>>, tt: usize, c: usize, b: B| {
                if best[tt].as_ref().is_none_or(|(old, _)| c < *old) {
                    best[tt] = Some((c, b));
                    changed = true;
                }
            };
            for (ta, ca, ba) in &known {
                offer(&mut best, !ta & full, ca + 1, B::Not(Box::new(ba.clone())));
                for (tb, cb, bb) in &known {
                    if ta > tb {
                        continue;
                    }
                    let c = ca + cb + 1;
                    for (op, tt) in [("And", ta & tb), ("Or", ta | tb), ("Xor", ta ^ tb)] {
                        offer(&mut best, tt, c, B::Bin(op, Box::new(ba.clone()), Box::new(bb.clone())));
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
enum BE {
    Zero,
    Ones,
    E(usize, B),
}

/// Largest region (in leaves) that gets rebuilt; truth tables are `u64`.
pub(crate) const MAX_LEAVES: usize = 6;

fn remap(b: &B, vars: &[usize]) -> B {
    match b {
        B::V(i) => B::V(vars[*i]),
        B::Not(x) => B::Not(Box::new(remap(x, vars))),
        B::Bin(op, x, y) => B::Bin(op, Box::new(remap(x, vars)), Box::new(remap(y, vars))),
    }
}

/// Short bitwise expression for truth table `tt` over `vars` (table bit `p`
/// is the value where bit `j` of `p` is `vars[j]`). Exact table lookup up to 3
/// variables; above that, Shannon expansion on the best variable.
fn bool_expr(tt: u64, vars: &[usize]) -> BE {
    match bool_expr_canon(tt, vars.len()) {
        BE::E(c, b) => BE::E(c, remap(&b, vars)),
        other => other,
    }
}

fn table_full(n: usize) -> u64 {
    if n >= 6 { u64::MAX } else { (1u64 << (1 << n)) - 1 }
}

/// `bool_expr` over variables `0..n`, cached.
fn bool_expr_canon(tt: u64, n: usize) -> BE {
    thread_local! {
        static CACHE: std::cell::RefCell<std::collections::HashMap<(u64, usize), BE>> = Default::default();
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
    let not = |b: B| B::Not(Box::new(b));
    let bin = |op, x: B, y: B| B::Bin(op, Box::new(x), Box::new(y));
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
        let cand = match (bool_expr(f0, &rest), bool_expr(f1, &rest)) {
            (BE::Zero, BE::Ones) => (1, x),
            (BE::Ones, BE::Zero) => (2, not(x)),
            (BE::Zero, BE::E(c, e)) => (c + 2, bin("And", x, e)),
            (BE::E(c, e), BE::Zero) => (c + 3, bin("And", not(x), e)),
            (BE::Ones, BE::E(c, e)) => (c + 3, bin("Or", not(x), e)),
            (BE::E(c, e), BE::Ones) => (c + 2, bin("Or", x, e)),
            (BE::E(c, e), _) if f0 == f1 => (c, e),
            (BE::E(c, e), _) if f1 == !f0 & sub_full => (c + 2, bin("Xor", x, e)),
            (BE::E(c0, e0), BE::E(c1, e1)) => {
                let mux = (c0 + c1 + 6, bin("Or", bin("And", x.clone(), e1), bin("And", not(x.clone()), e0.clone())));
                match bool_expr(f0 ^ f1, &rest) {
                    BE::E(cd, d) if c0 + cd + 3 < mux.0 => (c0 + cd + 3, bin("Xor", e0, bin("And", x, d))),
                    _ => mux,
                }
            }
            (BE::Zero, BE::Zero) | (BE::Ones, BE::Ones) => unreachable!("tt is not constant"),
        };
        if best.as_ref().is_none_or(|(c, _)| cand.0 < *c) {
            best = Some(cand);
        }
    }
    let (c, b) = best.unwrap();
    BE::E(c, b)
}

fn b_to_t(b: &B, leaves: &[T]) -> T {
    match b {
        B::V(i) => leaves[*i].clone(),
        B::Not(x) => T::Op("Not".into(), vec![b_to_t(x, leaves)]),
        B::Bin(op, x, y) => T::Op(op.to_string(), vec![b_to_t(x, leaves), b_to_t(y, leaves)]),
    }
}

/// `Σ coef·term + konst`, using Sub/Neg for negative coefficients.
pub(crate) fn build_sum(terms: &[(u64, T)], konst: u64, w: &Width) -> T {
    let num = |v: u64| T::Num(w.signed(v));
    let scaled = |c: u64, t: &T| if c == 1 { t.clone() } else { T::Op("Mul".into(), vec![num(c), t.clone()]) };
    let mut acc: Option<T> = None;
    for (c, t) in terms {
        let neg = w.signed(*c) < 0 && *c != 1u64 << (w.w - 1);
        acc = Some(match acc {
            None if neg => T::Op("Neg".into(), vec![scaled(c.wrapping_neg() & w.mask, t)]),
            None => scaled(*c, t),
            Some(a) if neg => T::Op("Sub".into(), vec![a, scaled(c.wrapping_neg() & w.mask, t)]),
            Some(a) => T::Op("Add".into(), vec![a, scaled(*c, t)]),
        });
    }
    match acc {
        None => num(konst),
        Some(a) if konst == 0 => a,
        Some(a) if w.signed(konst) < 0 => T::Op("Sub".into(), vec![a, num(konst.wrapping_neg() & w.mask)]),
        Some(a) => T::Op("Add".into(), vec![a, num(konst)]),
    }
}

/// Smallest rebuilt form of the linear region `t`, if it has 1..=MAX_LEAVES leaves.
pub(crate) fn simba(t: &T, w: &Width) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let n = lv.len();
    if n == 0 || n > MAX_LEAVES {
        return None;
    }
    let rebuilt = if has_const_bitwise(t, w) {
        semi_linear(t, &lv, w)?
    } else {
        let pts = 1usize << n;
        let m = w.mask;
        let vals: Vec<u64> = (0..pts)
            .map(|p| {
                let env: Vec<(T, u64)> = lv.iter().enumerate().map(|(i, l)| (l.clone(), (p >> i & 1) as u64)).collect();
                eval(t, w, &env)
            })
            .collect();
        // e(x) = Σ_j 2^j g(bit j of x), with g(p) = e(p) - 2e(0); k = g(0).
        let g: Vec<u64> = vals.iter().map(|v| v.wrapping_sub(vals[0].wrapping_mul(2)) & m).collect();
        let k = g[0];
        let gp: Vec<u64> = g.iter().map(|v| v.wrapping_sub(k) & m).collect();
        let (terms, konst) = rebuild_gp(&gp, &lv, k.wrapping_neg() & m, w);
        build_sum(&terms, konst, w)
    };
    Some(rebuilt).filter(|b| size(b) < size(t))
}

/// Whether the linear region `t` has a bitwise operation with a constant operand.
fn has_const_bitwise(t: &T, w: &Width) -> bool {
    match (t, kind(t, w)) {
        (_, Kind::ConstBit) => true,
        (T::Op(_, a), Kind::Lin) => a.iter().any(|x| has_const_bitwise(x, w)),
        _ => false,
    }
}

/// Shortest `(terms, konst')` with `konst + Σ_j 2^j gp(bit j of x) = Σ terms + konst'`,
/// where `gp(0) = 0` and table point `p` sets leaf `i` to bit `i` of `p`.
fn rebuild_gp(gp: &[u64], lv: &[T], mut konst: u64, w: &Width) -> (Vec<(u64, T)>, u64) {
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

/// Semi-linear region: `e(x) = e(0) + Σ_j D_j(bit j of x)` with
/// `D_j(q) = e(q << j) - e(0)`, a multiple of `2^j`. `g_j = D_j >> j` only
/// matters modulo `2^(w-j)`, so bit `j` joins a group (found from the low bits
/// up) whose table agrees with `g_j` in its low `w-j` bits. Each group has mask `M`;
/// each group is rebuilt as a linear MBA `L` of the leaves and contributes
/// `L(x & M)`, i.e. `c·(b(x) & M)` per term `c·b`, plus `c·~M` when `b(0) = -1`.
fn semi_linear(t: &T, lv: &[T], w: &Width) -> Option<T> {
    let n = lv.len();
    let m = w.mask;
    let at = |j: u32, q: usize| {
        let env: Vec<(T, u64)> = lv.iter().enumerate().map(|(i, l)| (l.clone(), ((q >> i & 1) as u64) << j)).collect();
        eval(t, w, &env)
    };
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
        // High bits match several groups; prefer bit j-1's, which keeps the
        // masks of small constants short.
        let below = groups.iter().position(|(_, mask)| j > 0 && mask >> (j - 1) & 1 == 1);
        match below.filter(|&i| same(&groups[i].0)).or_else(|| groups.iter().position(|(rep, _)| same(rep))) {
            Some(i) => groups[i].1 |= 1 << j,
            None => groups.push((g, 1 << j)),
        }
    }
    let mut cands = vec![masked_groups(&groups, lv, e0, w)];
    cands.extend(const_leaf_groups(&groups, lv, e0, w));
    cands.into_iter().min_by_key(|c| size(c))
}

/// `e0 + Σ_group L_group(x & M)`, with `L_group` the linear MBA of the group's table.
fn masked_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width) -> T {
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
            terms.push((c, T::Op("And".into(), vec![b, T::Num(w.signed(*mask))])));
        }
    }
    build_sum(&terms, konst, w)
}

/// Give each group a binary code and add one constant leaf `k_b` per code bit,
/// holding the bits of the groups whose code has bit `b`. Then bit `j` of the
/// region is `table(bits_j(x), code of j's group)`, a linear MBA of `x` and the
/// constant leaves, so `(y & ~K) - (y & K) + K` can come back as `y ^ K`.
/// Tried for every code assignment of at most 4 groups.
fn const_leaf_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width) -> Vec<T> {
    let (n, r) = (lv.len(), groups.len());
    let p = (usize::BITS - (r - 1).leading_zeros()) as usize;
    if r < 2 || r > 4 || n + p > MAX_LEAVES {
        return Vec::new();
    }
    let mut out = Vec::new();
    for codes in permutations(r) {
        let mut leaves = lv.to_vec();
        for b in 0..p {
            let mask = (0..r).filter(|&i| codes[i] >> b & 1 == 1).fold(0u64, |acc, i| acc | groups[i].1);
            leaves.push(T::Num(w.signed(mask)));
        }
        let mut table = vec![0u64; 1 << (n + p)];
        for (i, (g, _)) in groups.iter().enumerate() {
            for (q, &v) in g.iter().enumerate() {
                table[q | codes[i] << n] = v;
            }
        }
        let (terms, mut konst) = rebuild_gp(&table, &leaves, e0, w);
        let mut kept = Vec::new();
        for (c, t) in terms {
            match fold_consts(&t, w) {
                T::Num(v) => konst = konst.wrapping_add(c.wrapping_mul(v as u64)) & w.mask,
                t => kept.push((c, t)),
            }
        }
        out.push(build_sum(&kept, konst, w));
    }
    out
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
fn fold_consts(t: &T, w: &Width) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if !matches!(op.as_str(), "And" | "Or" | "Xor" | "Not" | "Add" | "Sub" | "Neg") {
        return t.clone();
    }
    let a: Vec<T> = a.iter().map(|x| fold_consts(x, w)).collect();
    let t = T::Op(op.clone(), a);
    match &t {
        T::Op(_, a) if a.iter().all(|x| matches!(x, T::Num(_))) => T::Num(w.signed(eval(&t, w, &[]))),
        _ => t,
    }
}

/// Split the variables into groups with no interaction in `gp`, so that
/// `gp(p) = Σ_group gp(p ∩ group)`: a mixed difference
/// `gp(p+i+j) - gp(p+i) - gp(p+j) + gp(p)` that is non-zero anywhere joins `i` and `j`.
fn independent_groups(gp: &[u64], n: usize, w: &Width) -> Vec<Vec<usize>> {
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
fn rebuild_table(gp: &[u64], lv: &[T], konst: u64, w: &Width) -> (Vec<(u64, T)>, u64) {
    let n = lv.len();
    let pts = 1usize << n;
    let m = w.mask;
    let all_vars: Vec<usize> = (0..n).collect();
    let mut cands: Vec<(Vec<(u64, T)>, u64)> = Vec::new();
    // Leaves with their own coefficient, then one term per remaining value.
    for subset in 0..(1usize << n) {
        let mut terms = Vec::new();
        let mut r = gp.to_vec();
        for i in (0..n).filter(|i| subset >> i & 1 == 1) {
            let c = gp[1 << i];
            if c == 0 {
                continue;
            }
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
            let BE::E(_, b) = bool_expr(tt, &all_vars) else {
                unreachable!("r[0] == 0, so the table is neither empty nor full")
            };
            terms.push((u, b_to_t(&b, lv)));
        }
        cands.push((terms, konst));
    }
    cands.extend(overlapping_terms(gp, lv, konst, w));
    cands
        .into_iter()
        .min_by_key(|(ts, k)| size(&build_sum(ts, *k, w)))
        .unwrap()
}

/// Most distinct non-zero values for which `overlapping_terms` searches.
const OVERLAP_MAX_VALUES: usize = 4;

/// Up to 3 bitwise terms whose supports may overlap (`11*(x^y) - x`), possibly
/// non-zero at 0 (`-23*~(x|y)`). Shifting the table by `d` gives
/// `h = gp + d = Σ c_j·b_j` per bit, and then `e = Σ c_j·b_j(x) + konst + d`,
/// since a per-bit constant `d` is the word `-d`. `d` is tried as 0 or `-v`
/// for a value `v` of `gp`, i.e. `h` is zero where `gp` is `v`.
fn overlapping_terms(gp: &[u64], lv: &[T], konst: u64, w: &Width) -> Vec<(Vec<(u64, T)>, u64)> {
    let m = w.mask;
    let all_vars: Vec<usize> = (0..lv.len()).collect();
    let distinct = |t: &[u64]| {
        let mut v: Vec<u64> = t.iter().copied().filter(|&u| u != 0).collect();
        v.sort_unstable();
        v.dedup();
        v
    };
    let vals = distinct(gp);
    if vals.len() > OVERLAP_MAX_VALUES {
        return Vec::new();
    }
    let mut out = Vec::new();
    let offsets = std::iter::once(0).chain(vals.iter().map(|&v| v.wrapping_neg() & m));
    for d in offsets {
        let h: Vec<u64> = gp.iter().map(|v| v.wrapping_add(d) & m).collect();
        let hv = distinct(&h);
        if hv.len() > OVERLAP_MAX_VALUES {
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
        for k in (1..=3usize).filter(|k| hv.len() < 1 << k) {
            for coefs in combinations(&pool, k) {
                if let Some(c) = split_by_sums(&h, &hv, &coefs, &all_vars, lv, konst.wrapping_add(d) & m, w) {
                    out.push(c);
                }
            }
        }
    }
    out
}

fn combinations(pool: &[u64], k: usize) -> Vec<Vec<u64>> {
    if k == 0 {
        return vec![Vec::new()];
    }
    (0..pool.len())
        .flat_map(|i| {
            combinations(&pool[i + 1..], k - 1).into_iter().map(move |mut rest| {
                rest.insert(0, pool[i]);
                rest
            })
        })
        .collect()
}

/// Most ways tried to resolve points whose value is the sum of several subsets of `coefs`.
const MAX_SUBSET_CHOICES: usize = 16;

/// Write `h` as `Σ coefs[j]·b_j`, where each point's value is the sum of the
/// coefficients of the `b_j` that are 1 there. With two terms a point can only
/// be ambiguous when `c1 + c2 = 0` (as in `(y ^ k) - k`); such points are
/// resolved in up to `MAX_SUBSET_CHOICES` ways and the shortest result wins.
/// With three terms ambiguity is common and too costly to resolve, so it fails.
fn split_by_sums(h: &[u64], h_vals: &[u64], coefs: &[u64], vars: &[usize], lv: &[T], konst: u64, w: &Width) -> Option<(Vec<(u64, T)>, u64)> {
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
    'ways: for mut way in 0..ways.min(MAX_SUBSET_CHOICES) {
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
            match bool_expr(tt, vars) {
                BE::Zero => continue 'ways,
                // All ones in every bit is the word -1.
                BE::Ones => kk = kk.wrapping_sub(coefs[j]) & m,
                BE::E(_, b) => terms.push((coefs[j], b_to_t(&b, lv))),
            }
        }
        if best.as_ref().is_none_or(|(bt, bk)| size(&build_sum(&terms, kk, w)) < size(&build_sum(bt, *bk, w))) {
            best = Some((terms, kk));
        }
    }
    best
}

thread_local! {
    static REWRITTEN: std::cell::RefCell<std::collections::HashMap<(u32, T), T>> = Default::default();
}

/// Replace every linear or polynomial region (and, recursively, regions inside
/// atoms) by its rebuilt form when that is smaller. Memoized per thread.
pub(crate) fn rewrite(t: &T, w: &Width) -> T {
    if !matches!(t, T::Op(..)) {
        return t.clone();
    }
    let key = (w.w, t.clone());
    if let Some(r) = REWRITTEN.with(|c| c.borrow().get(&key).cloned()) {
        return r;
    }
    let lin = rewrite_linear(t, w);
    let r = match crate::poly_mba::simplify_poly(t, w) {
        Some(p) if size(&p) < size(&lin) => p,
        _ => lin,
    };
    REWRITTEN.with(|c| c.borrow_mut().insert(key, r.clone()));
    r
}

fn rewrite_linear(t: &T, w: &Width) -> T {
    let T::Op(op, args) = t else { return t.clone() };
    if kind(t, w) != Kind::Atom {
        if let Some(best) = simba(t, w) {
            return substitute_atoms(&best, w);
        }
    }
    T::Op(op.clone(), args.iter().map(|a| rewrite(a, w)).collect())
}

/// Rewrite inside the atom leaves of a rebuilt region.
fn substitute_atoms(t: &T, w: &Width) -> T {
    match t {
        T::Op(op, args) => {
            if kind(t, w) == Kind::Atom {
                rewrite(t, w)
            } else {
                T::Op(op.clone(), args.iter().map(|a| substitute_atoms(a, w)).collect())
            }
        }
        _ => t.clone(),
    }
}

/// Rewrite the egglog term `egg` (W-bit wrapping semantics) with every linear
/// MBA region of at most `MAX_LEAVES` leaves, and every polynomial MBA region,
/// rebuilt in a smaller form. Returns `egg` unchanged when nothing gets smaller.
pub fn simplify_linear(egg: &str, w: u32) -> String {
    let w = Width::new(w);
    let t = parse(egg);
    let r = rewrite(&t, &w);
    REWRITTEN.with(|c| c.borrow_mut().clear());
    if r == t { egg.to_string() } else { show(&r) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{NumType, eval};
    use std::collections::HashMap;

    fn full_eval(t: &T, w: &Width, env: &HashMap<String, u64>) -> u64 {
        let ty = NumType { bits: w.w, signed: false };
        eval(t, ty, &|v: &str| env[v]).expect("no division in generated terms")
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

    const VARS: [&str; 6] = ["x", "y", "z", "u", "v", "w"];

    fn random_term(r: &mut Rng, depth: u32) -> T {
        let var = |r: &mut Rng| T::Var(VARS[(r.next() % VARS.len() as u64) as usize].into());
        if depth == 0 {
            return match r.next() % 6 {
                0 => T::Num((r.next() % 7) as i64 - 3),
                _ => var(r),
            };
        }
        let sub = |r: &mut Rng| random_term(r, depth - 1);
        match r.next() % 12 {
            0 => T::Op("Not".into(), vec![sub(r)]),
            1 => T::Op("Neg".into(), vec![sub(r)]),
            2 | 3 => T::Op("Add".into(), vec![sub(r), sub(r)]),
            4 => T::Op("Sub".into(), vec![sub(r), sub(r)]),
            5 => T::Op("Mul".into(), vec![T::Num((r.next() % 9) as i64 - 4), sub(r)]),
            6 => T::Op("And".into(), vec![sub(r), sub(r)]),
            7 => T::Op("Or".into(), vec![sub(r), sub(r)]),
            8 => T::Op("Xor".into(), vec![sub(r), sub(r)]),
            9 => T::Op("Mul".into(), vec![sub(r), sub(r)]),
            10 => T::Op("Shl".into(), vec![sub(r), T::Num((r.next() % 10) as i64)]),
            _ => T::Op("Shr".into(), vec![sub(r), T::Num((r.next() % 4) as i64)]),
        }
    }

    #[test]
    fn rewrite_preserves_value() {
        let mut r = Rng(0x2545f4914f6cdd1d);
        let mut changed = 0;
        for w in [8u32, 16, 32, 64] {
            let wd = Width::new(w);
            for _ in 0..3000 {
                let depth = 1 + (r.next() % 4) as u32;
                let t = random_term(&mut r, depth);
                let alt = rewrite(&t, &wd);
                if alt != t {
                    changed += 1;
                }
                for _ in 0..64 {
                    let env: HashMap<String, u64> =
                        VARS.iter().map(|v| (v.to_string(), r.next())).collect();
                    assert_eq!(
                        full_eval(&t, &wd, &env),
                        full_eval(&alt, &wd, &env),
                        "w={w}\n  {}\n  {}\n  env={env:?}",
                        show(&t),
                        show(&alt)
                    );
                }
            }
        }
        assert!(changed > 1000, "only {changed} rewrites fired");
    }

    fn b_eval(b: &B, p: usize) -> bool {
        match b {
            B::V(i) => p >> i & 1 == 1,
            B::Not(x) => !b_eval(x, p),
            B::Bin(op, x, y) => {
                let (x, y) = (b_eval(x, p), b_eval(y, p));
                match *op {
                    "And" => x & y,
                    "Or" => x | y,
                    _ => x ^ y,
                }
            }
        }
    }

    fn b_size(b: &B) -> usize {
        match b {
            B::V(_) => 1,
            B::Not(x) => 1 + b_size(x),
            B::Bin(_, x, y) => 1 + b_size(x) + b_size(y),
        }
    }

    #[test]
    fn bool_expr_matches_table() {
        let check = |n: usize, tt: u64| {
            let vars: Vec<usize> = (0..n).collect();
            let BE::E(cost, b) = bool_expr(tt, &vars) else { panic!("n={n} table {tt:#x} not found") };
            assert_eq!(cost, b_size(&b), "n={n} table {tt:#x}: wrong cost");
            for p in 0..1usize << n {
                assert_eq!(b_eval(&b, p), tt >> p & 1 == 1, "n={n} table {tt:#x} point {p}");
            }
        };
        for n in 1..=4usize {
            for tt in 1..table_full(n) {
                check(n, tt);
            }
        }
        let mut r = Rng(0x853c49e6748fea9b);
        for n in 5..=MAX_LEAVES {
            for _ in 0..3000 {
                let tt = r.next() & table_full(n);
                if tt != 0 && tt != table_full(n) {
                    check(n, tt);
                }
            }
        }
    }
}
