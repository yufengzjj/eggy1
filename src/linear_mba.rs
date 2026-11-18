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
            "And" | "Or" | "Xor" => match (bit_operand(&a[0], w), bit_operand(&a[1], w)) {
                (Kind::Bit, Kind::Bit) => Kind::Bit,
                _ => Kind::ConstBit,
            },
            "Mul" if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => Kind::Lin,
            "Shl" if const_shift(&a[1], w).is_some() => Kind::Lin,
            _ => Kind::Atom,
        },
    }
}

/// Kind of `t` as an operand of a bitwise operation (`Bit` or `ConstBit`).
/// Arithmetic operands (`x + y`, `-(x | y)`) are opaque leaves there, but `~`
/// stays visible so that `~a` and `a` share the leaf `a`; see `leaves`.
fn bit_operand(t: &T, w: &Width) -> Kind {
    match t {
        T::Num(_) if kind(t, w) == Kind::Lin => Kind::ConstBit,
        T::Op(op, a) if op == "Not" => bit_operand(&a[0], w),
        _ if kind(t, w) == Kind::ConstBit => Kind::ConstBit,
        _ => Kind::Bit,
    }
}

/// Leaves of the linear region rooted at `t`: variables, atom subterms, and
/// arithmetic operands of bitwise operations.
pub(crate) fn leaves(t: &T, w: &Width, out: &mut Vec<T>) {
    leaves_in(t, w, out, false);
}

fn leaves_in(t: &T, w: &Width, out: &mut Vec<T>, in_bitwise: bool) {
    match t {
        T::Num(_) => {}
        T::Var(_) => {
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
        T::Op(op, a) => {
            let k = kind(t, w);
            if k == Kind::Atom || (in_bitwise && k == Kind::Lin && op != "Not") {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            } else {
                let inner = in_bitwise || matches!(op.as_str(), "And" | "Or" | "Xor");
                a.iter().for_each(|x| leaves_in(x, w, out, inner));
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

/// A linear region compiled once for evaluation at many points; `run` reads leaf
/// `i` of the `lv` given to `new` from `leaf(i)`.
pub(crate) struct Prog(Vec<Ins>);

enum Ins {
    Leaf(usize),
    Num(u64),
    Not(usize),
    Neg(usize),
    Shl(usize, u32),
    Bin(fn(u64, u64) -> u64, usize, usize),
}

impl Prog {
    pub(crate) fn new(t: &T, lv: &[T], w: &Width) -> Prog {
        let mut p = Prog(Vec::new());
        p.push(t, lv, w);
        p
    }

    fn push(&mut self, t: &T, lv: &[T], w: &Width) -> usize {
        let ins = match (lv.iter().position(|l| l == t), t) {
            (Some(i), _) => Ins::Leaf(i),
            (_, T::Num(c)) => Ins::Num(*c as u64),
            (_, T::Var(_)) => unreachable!("variable missing from leaves"),
            (_, T::Op(op, a)) => match op.as_str() {
                "Not" => Ins::Not(self.push(&a[0], lv, w)),
                "Neg" => Ins::Neg(self.push(&a[0], lv, w)),
                "Shl" => Ins::Shl(self.push(&a[0], lv, w), const_shift(&a[1], w).unwrap()),
                op => {
                    let f: fn(u64, u64) -> u64 = match op {
                        "Add" => u64::wrapping_add,
                        "Sub" => u64::wrapping_sub,
                        "Mul" => u64::wrapping_mul,
                        "And" => |x, y| x & y,
                        "Or" => |x, y| x | y,
                        "Xor" => |x, y| x ^ y,
                        _ => unreachable!("non-linear op {op} inside a linear region"),
                    };
                    let x = self.push(&a[0], lv, w);
                    Ins::Bin(f, x, self.push(&a[1], lv, w))
                }
            },
        };
        self.0.push(ins);
        self.0.len() - 1
    }

    pub(crate) fn run(&self, leaf: impl Fn(usize) -> u64, w: &Width) -> u64 {
        let mut v: Vec<u64> = Vec::with_capacity(self.0.len());
        for ins in &self.0 {
            let r = match *ins {
                Ins::Leaf(i) => leaf(i),
                Ins::Num(c) => c,
                Ins::Not(x) => !v[x],
                Ins::Neg(x) => u64::wrapping_neg(v[x]),
                Ins::Shl(x, k) => v[x] << k,
                Ins::Bin(f, x, y) => f(v[x], v[y]),
            };
            v.push(r & w.mask);
        }
        v[v.len() - 1]
    }

    /// Value with leaf `i` set to bit `i` of `p`.
    pub(crate) fn at(&self, p: usize, w: &Width) -> u64 {
        self.run(|i| (p >> i & 1) as u64, w)
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
    // c·t + c = -c·~t saves the constant term; for c = 1 only inside a longer sum,
    // where `a - ~t` is shorter than `a + t + 1`.
    if konst != 0 && (konst != 1 || terms.len() > 1) {
        if let Some(i) = terms.iter().position(|(c, _)| *c == konst) {
            let mut terms = terms.to_vec();
            let (c, t) = terms.remove(i);
            let not_t = match t {
                T::Op(op, mut a) if op == "Not" => a.remove(0),
                t => T::Op("Not".into(), vec![t]),
            };
            terms.push((c.wrapping_neg() & w.mask, not_t));
            return build_sum(&terms, 0, w);
        }
    }
    let num = |v: u64| T::Num(w.signed(v));
    let scaled = |c: u64, t: &T| if c == 1 { t.clone() } else { T::Op("Mul".into(), vec![num(c), t.clone()]) };
    let mut acc: Option<T> = None;
    for (c, t) in terms {
        let neg = w.signed(*c) < 0 && *c != 1u64 << (w.w - 1);
        acc = Some(match acc {
            None if *c == w.mask => T::Op("Neg".into(), vec![t.clone()]),
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
        let prog = Prog::new(t, &lv, w);
        let vals: Vec<u64> = (0..1usize << n).map(|p| prog.at(p, w)).collect();
        let rebuilt = rebuild_values(&vals, &lv, w);
        match related_leaves(t, &lv, w) {
            Some(r) if size(&r) < size(&rebuilt) => r,
            _ => rebuilt,
        }
    };
    Some(rebuilt).filter(|b| size(b) < size(t))
}


/// The linear MBA over `lv` with values `vals` on {0,1}^n.
fn rebuild_values(vals: &[u64], lv: &[T], w: &Width) -> T {
    let m = w.mask;
    // e(x) = Σ_j 2^j g(bit j of x), with g(p) = e(p) - 2e(0); k = g(0).
    let g: Vec<u64> = vals.iter().map(|v| v.wrapping_sub(vals[0].wrapping_mul(2)) & m).collect();
    let k = g[0];
    let gp: Vec<u64> = g.iter().map(|v| v.wrapping_sub(k) & m).collect();
    let (terms, konst) = rebuild_gp(&gp, lv, k.wrapping_neg() & m, w);
    build_sum(&terms, konst, w)
}

/// Most leaves `small_blocks` handles.
const MAX_BLOCK_LEAVES: usize = 12;

/// Upper bound on the degree of `t`'s conjunction-basis expansion: the most leaves
/// any bitwise subterm of the linear region has.
fn bit_degree(t: &T, w: &Width) -> usize {
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

/// Rebuild a linear region from its conjunction-basis expansion when every maximal
/// set of leaves with a non-zero coefficient (a block) has at most 3 leaves: one
/// term `c·f` per block, with `f` any bitwise function of the block's leaves and `c`
/// set by the block's top coefficient, plus the lower-degree monomials still left
/// over. The choice per block that gives the smallest sum wins, so `c·(x & y)` may
/// come back as `x + y - (x | y)` or `-(x ^ y)` when the single terms absorb the rest.
/// Not limited to `MAX_LEAVES`.
fn small_blocks(t: &T, w: &Width) -> Option<T> {
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
    let wsize = |t: &T| -> usize {
        fn go(t: &T, ph: &[T], ls: &[usize]) -> usize {
            match t {
                T::Var(_) => ph.iter().position(|p| p == t).map_or(1, |i| ls[i]),
                T::Num(_) => 1,
                T::Op(_, a) => 1 + a.iter().map(|x| go(x, ph, ls)).sum::<usize>(),
            }
        }
        go(t, &ph, &leaf_size)
    };
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
            let BE::E(_, b) = bool_expr(tt, &vars) else { continue };
            let adds: Vec<(usize, u64)> = (1..full).map(|q| (global(q), c.wrapping_mul(a[q]) & m)).filter(|&(_, v)| v != 0).collect();
            out.push((c, b_to_t(&b, &ph), adds, c.wrapping_mul(a[0]) & m));
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
            let conj = (0..n).filter(|i| q >> i & 1 == 1).map(|i| ph[i].clone()).reduce(|a, b| T::Op("And".into(), vec![a, b])).unwrap();
            terms.push((c, conj));
        }
        build_sum(&terms, konst, w)
    };
    let mut choice = vec![0usize; blocks.len()];
    let mut best = build(&choice);
    let mut best_size = wsize(&best);
    // Coordinate descent: the remaining terms only couple blocks that share leaves.
    for _ in 0..4 {
        let mut improved = false;
        for e in 0..blocks.len() {
            for ci in 0..opts[e].len() {
                let mut c = choice.clone();
                c[e] = ci;
                let cand = build(&c);
                let cs = wsize(&cand);
                if cs < best_size {
                    (best, best_size, choice, improved) = (cand, cs, c, true);
                }
            }
        }
        if !improved {
            break;
        }
    }
    fn fill(t: &T, ph: &[T], lv: &[T]) -> T {
        match t {
            T::Var(_) => ph.iter().position(|p| p == t).map_or_else(|| t.clone(), |i| lv[i].clone()),
            T::Num(_) => t.clone(),
            T::Op(op, a) => T::Op(op.clone(), a.iter().map(|x| fill(x, ph, lv)).collect()),
        }
    }
    (best_size < size(t)).then(|| fill(&best, &ph, &lv))
}

/// An arithmetic leaf `L` that is itself a linear MBA `ℓ` of other leaves (`a - d`,
/// `(b ^ d) - b`) is treated as independent, but `L - ℓ = 0`, so the region can
/// add `μ·(L - ℓ)` for any `μ`: in `(P & ~b) - (Q & (b | P)) + (b ^ d)` with
/// `Q = (b ^ d) - b`, `μ = 1` removes `d` and leaves `b | P | Q`. Tries up to two
/// such leaves with small `μ`.
fn related_leaves(t: &T, lv: &[T], w: &Width) -> Option<T> {
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
    combos
        .into_iter()
        .map(|combo| {
            let vals: Vec<u64> = (0..pts)
                .map(|p| combo.iter().fold(base[p], |v, &(i, mu)| v.wrapping_add(mu.wrapping_mul(diffs[i][p])) & w.mask))
                .collect();
            rebuild_values(&vals, &ext, w)
        })
        .min_by_key(size)
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
/// Also tries `t - a·v`, added back as a term, for the leaf `v` and small `a`
/// that leave no more groups and the smallest table values: in
/// `((x ^ K) | C) + x` the bits of the bitwise term have tables 0, ±1, but the
/// `+ x` makes them 0, 1, 2.
fn semi_linear(t: &T, lv: &[T], w: &Width) -> Option<T> {
    let m = w.mask;
    let (e0, groups) = bit_groups(t, lv, w)?;
    let mut cands = Vec::new();
    semi_linear_candidates(&groups, lv, e0, w, &mut cands);
    let mut peels = Vec::new();
    let mut best: Option<((u64, u64), usize)> = None;
    for (i, l) in lv.iter().enumerate() {
        for a in [1i64, -1, 2, -2, 3, -3] {
            let peeled = T::Op("Sub".into(), vec![t.clone(), T::Op("Mul".into(), vec![T::Num(a), l.clone()])]);
            let Some((e0, gs)) = bit_groups(&peeled, lv, w) else { continue };
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
        semi_linear_candidates(gs, lv, *e0, w, &mut sub);
        cands.extend(sub.into_iter().map(|c| add(c, *i, *a)));
    }
    let mut limit = cands.iter().map(size).min().unwrap_or(usize::MAX).min(size(t));
    shape_candidates(&groups, lv, e0, w, limit, &mut cands);
    for (i, a, e0, gs) in &peels {
        limit = cands.iter().map(size).min().unwrap_or(limit);
        let extra = size(&add(T::Num(1), *i, *a)) - 1;
        if limit > extra {
            let mut sub = Vec::new();
            shape_candidates(gs, lv, *e0, w, limit - extra, &mut sub);
            cands.extend(sub.into_iter().map(|c| add(c, *i, *a)));
        }
    }
    // Masks that differ only in bits that cannot matter tie on size; keep the short one.
    cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))
}

/// Largest table value in magnitude, then the sum of each group's largest.
fn spread(groups: &[(Vec<u64>, u64)], w: &Width) -> (u64, u64) {
    let per_group = groups.iter().map(|(g, _)| g.iter().map(|&v| w.signed(v).unsigned_abs()).max().unwrap_or(0));
    (per_group.clone().max().unwrap_or(0), per_group.fold(0, u64::saturating_add))
}

/// Largest bitwise expression size `shape_candidates` searches.
const MAX_SHAPE: usize = 14;

#[derive(Clone, Copy)]
enum Shape {
    Leaf(usize),
    Const,
    Not(usize),
    Bin(&'static str, usize, usize),
}

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
    seen: std::collections::HashSet<[u64; 4]>,
}

fn one(f: u8) -> [u64; 4] {
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
            level.push((one(f), Shape::Leaf(i)));
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
            if self.seen.insert(s) {
                self.elems.push((0..=255u8).filter(|&f| s[(f >> 6) as usize] >> (f & 63) & 1 == 1).collect());
                self.sets.push(s);
                self.how.push(how);
            }
        }
        self.levels.push(start..self.sets.len());
    }

    fn grow(&mut self, size: usize) {
        let full = self.full();
        while self.levels.len() <= size {
            let s = self.levels.len();
            let mut level = Vec::new();
            for i in self.levels[s - 1].clone() {
                let mut set = [0; 4];
                for &f in &self.elems[i] {
                    let g = !f & full;
                    set[(g >> 6) as usize] |= 1 << (g & 63);
                }
                level.push((set, Shape::Not(i)));
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
                        for (set, op) in sets.into_iter().zip(["And", "Or", "Xor"]) {
                            level.push((set, Shape::Bin(op, i, k)));
                        }
                    }
                }
            }
            self.push_level(level);
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
            Shape::Not(a) => self.solve(a, !f & self.full(), j, consts, slot),
            Shape::Bin(op, a, b) => {
                let apply = |x: u8, y: u8| match op {
                    "And" => x & y,
                    "Or" => x | y,
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

    fn build(&self, i: usize, lv: &[T], consts: &[u64], slot: &mut usize, w: &Width) -> T {
        match self.how[i] {
            Shape::Leaf(k) => lv[k].clone(),
            Shape::Const => {
                *slot += 1;
                T::Num(w.signed(consts.get(*slot - 1).copied().unwrap_or(0) & w.mask))
            }
            Shape::Not(a) => T::Op("Not".into(), vec![self.build(a, lv, consts, slot, w)]),
            Shape::Bin(op, a, b) => {
                let x = self.build(a, lv, consts, slot, w);
                T::Op(op.into(), vec![x, self.build(b, lv, consts, slot, w)])
            }
        }
    }
}

fn shapes(n: usize) -> &'static std::sync::Mutex<Shapes> {
    static SHAPES: [OnceLock<std::sync::Mutex<Shapes>>; 2] = [OnceLock::new(), OnceLock::new()];
    SHAPES[n - 2].get_or_init(|| std::sync::Mutex::new(Shapes::new(n)))
}

/// Candidates `c·B + r` smaller than `limit`, with `B` a bitwise expression of
/// 2 or 3 leaves and constants. Bit `j` of `B` has a table `f_j`, and the region
/// needs `c·(f_j(q) - f_j(0)) = g_j(q)` modulo `2^(w-j)`; the smallest `B` whose
/// table set meets each bit's acceptable tables is found in `Shapes`.
fn shape_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width, mut limit: usize, cands: &mut Vec<T>) {
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
        let mut memo = std::collections::HashMap::new();
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

/// The smallest expression in `Shapes` of size at most `top` whose table set meets
/// `acc[j]` for every bit `j`, with its constants solved bit by bit.
fn smallest_shape(acc: &[[u64; 4]], n: usize, top: usize, lv: &[T], w: &Width) -> Option<T> {
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

/// `e(0)` and the bits of the semi-linear region `t` grouped by table, as
/// `(table, mask)`; `None` if `t` is not semi-linear.
fn bit_groups(t: &T, lv: &[T], w: &Width) -> Option<(u64, Vec<(Vec<u64>, u64)>)> {
    let n = lv.len();
    let m = w.mask;
    let prog = Prog::new(t, lv, w);
    let at = |j: u32, q: usize| prog.run(|i| ((q >> i & 1) as u64) << j, w);
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

fn semi_linear_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width, cands: &mut Vec<T>) {
    let mut seen = std::collections::HashSet::new();
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
/// first two groups that have such entries (`r = w - j` for the group's lowest bit
/// `j`; both are the same value modulo `2^r`).
fn half_flips(groups: &[(Vec<u64>, u64)], w: &Width) -> Vec<Vec<(Vec<u64>, u64)>> {
    let mut out = vec![groups.to_vec()];
    let flippable = groups.iter().enumerate().filter_map(|(i, (g, mask))| {
        let rest = w.w - mask.trailing_zeros();
        let half = (1u64 << (rest - 1)).wrapping_neg() & w.mask;
        (rest > 1 && rest < w.w && g.contains(&half)).then_some((i, half))
    });
    for (i, half) in flippable.take(2) {
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

fn grouped_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width, cands: &mut Vec<T>) {
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
fn single_leaf(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Width, cands: &mut Vec<T>) {
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
    for (c, p, n) in [(c, p, n), (neg_c, n, p)] {
        let mask = p | n;
        let mut zs = vec![0, free];
        if let Some(h) = solve_mul(c, e0.wrapping_sub(c.wrapping_mul(n)) & m, w) {
            zs.extend([h, h & free]);
        }
        zs.sort_unstable();
        zs.dedup();
        for z in zs.into_iter().filter(|z| z & !free == 0) {
            let k = n | z;
            let mut inner = if mask == m { y.clone() } else { T::Op("And".into(), vec![y.clone(), T::Num(w.signed(mask))]) };
            if k != 0 {
                inner = T::Op("Xor".into(), vec![inner, T::Num(w.signed(k))]);
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
fn high_merges(groups: &[(Vec<u64>, u64)], w: &Width) -> Vec<Vec<(Vec<u64>, u64)>> {
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
    // Enumerate at most 16 variants; the other groups join the group holding the
    // bit just below them.
    let mut count = 1;
    let take = ambiguous
        .iter()
        .take_while(|&&i| {
            count *= options[i].len();
            count <= 16
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
/// Tried for every code assignment of at most 4 groups. Part of the constant
/// `e0` can also move into the table: adding `shifts[i]` to group `i`'s table
/// adds `shifts[i]·M_i` to the region, so `-2*(x & ~K) - 2*K` can come back as
/// `-2*(x | K)`.
fn const_leaf_groups(groups: &[(Vec<u64>, u64)], shifts: &[Vec<u64>], lv: &[T], e0: u64, w: &Width) -> Vec<T> {
    let (n, r) = (lv.len(), groups.len());
    let p = (usize::BITS - (r - 1).leading_zeros()) as usize;
    if r < 2 || r > 4 || n + p > MAX_LEAVES {
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
fn solve_mul(mask: u64, e0: u64, w: &Width) -> Option<u64> {
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
    let mut r = match crate::poly_mba::simplify_poly(t, w) {
        Some(p) if size(&p) < size(&lin) => p,
        _ => lin,
    };
    // A rebuilt region can expose more: once `9*(A & B) + ...` becomes `2*A - B`
    // with `A = -(x ^ y)`, A's own linear form joins the enclosing region. Only
    // arithmetic leaves of bitwise operations can do this.
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    if r != *t && lv.iter().any(|l| kind(l, w) == Kind::Lin) {
        let again = rewrite(&r, w);
        if size(&again) < size(&r) {
            r = again;
        }
    }
    REWRITTEN.with(|c| c.borrow_mut().insert(key, r.clone()));
    r
}

fn rewrite_linear(t: &T, w: &Width) -> T {
    let T::Op(op, args) = t else { return t.clone() };
    if kind(t, w) != Kind::Atom {
        let best = match (simba(t, w), small_blocks(t, w)) {
            (Some(s), Some(p)) => Some(if size(&p) < size(&s) { p } else { s }),
            (s, p) => s.or(p),
        };
        if let Some(best) = best {
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
/// MBA region, and every polynomial MBA region,
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
