//! Linear MBA simplification (SiMBA-style). A linear MBA, i.e. a sum of
//! constant multiples of bitwise functions, is fully determined by its values
//! on {0,1}^n, so it can be rebuilt from those values in a minimal form.
//! Subterms that are not linear (`x*y`, `x >> 3`, ...) are treated as opaque
//! variables; the identity holds for any value they take. Bitwise operations
//! with constant operands (`x & 0xff`) make the region semi-linear: each bit
//! position then has its own bitwise function, see `semi_linear`.

use crate::eval::{Op, Term as T, parse, show, size};
use std::sync::{Arc, OnceLock};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering::Relaxed};

mod linear;
mod polish;
mod relate;
mod semi;
mod shapes;
mod split;
mod tables;
mod wide;
#[cfg(test)]
mod tests;

use linear::*;
use relate::*;
use semi::*;
use shapes::*;
use split::*;
use tables::*;
use wide::*;
pub use polish::polish;
pub(crate) use linear::simba_memo;
pub(crate) use split::low_consts;

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

/// The width of the arithmetic, and the memos and limits shared by one pre-pass run.
pub(crate) struct Ctx {
    pub(crate) w: u32,
    pub(crate) mask: u64,
    st: std::sync::Arc<State>,
}

impl Ctx {
    pub(crate) fn new(w: u32) -> Ctx {
        Ctx { w, mask: if w == 64 { u64::MAX } else { (1u64 << w) - 1 }, st: Default::default() }
    }
    /// Lets `rewrite` make at most `n` more uncached calls in this run.
    pub(crate) fn limit_rewrites(&self, n: usize) {
        self.st.rewrites_left.store(n, Relaxed);
    }
    /// Most leaves of a semi-linear region rebuilt from now on in this run.
    pub(crate) fn limit_semi_leaves(&self, n: usize) {
        self.st.semi_leaves.store(n, Relaxed);
    }
    /// The same run at width `w`, sharing its state.
    pub(crate) fn narrow(&self, w: u32) -> Ctx {
        Ctx { st: self.st.clone(), ..Ctx::new(w) }
    }
    pub(crate) fn low_values(&self) -> &crate::lowbits::ValuesMemo {
        &self.st.low_values
    }
    pub(crate) fn signed(&self, v: u64) -> i64 {
        let sh = 64 - self.w;
        ((v << sh) as i64) >> sh
    }
}

type Memo<K, V> = std::sync::Mutex<crate::eval::FastMap<K, (V, u8)>>;
/// Bits of `State::used` and `State::excluded`.
pub(super) const CLUSTERED: u8 = 1;
pub(super) const WIDE: u8 = 2;
type RebuiltKey = (Vec<u64>, Vec<(usize, bool)>, u64, u32);
type GroupedKey = (Vec<(Vec<u64>, u64)>, Vec<T>, u64, u32);
type PairKey = (u32, Vec<(Vec<u64>, u64)>, u64, Vec<T>, usize);

struct State {
    simba_memo: Memo<(u32, usize, T), Option<T>>,
    rewritten: Memo<(u32, T), T>,
    related: Memo<(u32, usize, usize, T), T>,
    rebuilt: std::sync::Mutex<crate::eval::FastMap<RebuiltKey, (Vec<(u64, T)>, u64)>>,
    grouped: std::sync::Mutex<crate::eval::FastMap<GroupedKey, T>>,
    low_values: crate::lowbits::ValuesMemo,
    pairs: std::sync::Mutex<crate::eval::FastMap<PairKey, Vec<T>>>,
    /// Most leaves of a region `relate_region` tries.
    relate_leaves: AtomicUsize,
    /// `rewrite` calls left before it returns its input unchanged.
    rewrites_left: AtomicUsize,
    /// Most leaves a semi-linear region may have to be rebuilt.
    semi_leaves: AtomicUsize,
    bit_splits: AtomicUsize,
    /// `peel` calls nested inside each other.
    peel_depth: AtomicUsize,
    clustering: std::sync::Mutex<Vec<T>>,
    /// `CLUSTERED` turns `clustered` off and `WIDE` turns `wide_blocks` off, for the rebuilds without them.
    excluded: AtomicU8,
    /// Which of `clustered` and `wide_blocks` gave a kept form since the last reset.
    used: AtomicU8,
}

impl Default for State {
    fn default() -> State {
        State {
            simba_memo: Default::default(),
            rewritten: Default::default(),
            related: Default::default(),
            rebuilt: Default::default(),
            grouped: Default::default(),
            low_values: Default::default(),
            pairs: Default::default(),
            relate_leaves: AtomicUsize::new(MAX_WIDE_LEAVES),
            rewrites_left: AtomicUsize::new(usize::MAX),
            semi_leaves: AtomicUsize::new(MAX_LEAVES),
            bit_splits: AtomicUsize::new(BIT_SPLIT_BUDGET),
            peel_depth: AtomicUsize::new(0),
            clustering: Default::default(),
            excluded: AtomicU8::new(0),
            used: AtomicU8::new(0),
        }
    }
}

/// Decrements `a` down to 0 and returns its old value.
fn take_one(a: &AtomicUsize) -> usize {
    let left = a.load(Relaxed);
    a.store(left.saturating_sub(1), Relaxed);
    left
}

pub(crate) fn const_shift(t: &T, w: &Ctx) -> Option<u32> {
    match t {
        T::Num(k) if (0..w.w as i64).contains(k) => Some(*k as u32),
        _ => None,
    }
}

pub(crate) fn kind(t: &T, w: &Ctx) -> Kind {
    let bit = |k: Kind| if k == Kind::Atom { Kind::Bit } else { k };
    match t {
        T::Var(_) => Kind::Bit,
        T::Num(c) => {
            let c = *c as u64 & w.mask;
            if c == 0 || c == w.mask { Kind::Bit } else { Kind::Lin }
        }
        T::Op(op, a) => match op {
            Op::Not => bit(kind(&a[0], w)),
            Op::Neg | Op::Add | Op::Sub => Kind::Lin,
            Op::And | Op::Or | Op::Xor => match (bit_operand(&a[0], w), bit_operand(&a[1], w)) {
                (Kind::Bit, Kind::Bit) => Kind::Bit,
                _ => Kind::ConstBit,
            },
            Op::Mul if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => Kind::Lin,
            Op::Shl if const_shift(&a[1], w).is_some() => Kind::Lin,
            _ => Kind::Atom,
        },
    }
}

/// Kind of `t` as an operand of a bitwise operation (`Bit` or `ConstBit`).
/// Arithmetic operands (`x + y`, `-(x | y)`) are opaque leaves there, but `~`
/// stays visible so that `~a` and `a` share the leaf `a`; see `leaves`.
fn bit_operand(t: &T, w: &Ctx) -> Kind {
    match t {
        T::Num(_) if kind(t, w) == Kind::Lin => Kind::ConstBit,
        T::Op(op, a) if *op == Op::Not => bit_operand(&a[0], w),
        _ if kind(t, w) == Kind::ConstBit => Kind::ConstBit,
        _ => Kind::Bit,
    }
}

/// Leaves of the linear region rooted at `t`: variables, atom subterms, and
/// arithmetic operands of bitwise operations.
pub(crate) fn leaves(t: &T, w: &Ctx, out: &mut Vec<T>) {
    let mut seen = out.iter().map(term_hash).collect();
    leaves_in(t, w, out, &mut seen, false);
}

fn term_hash(t: &T) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    t.hash(&mut h);
    h.finish()
}

/// `seen` holds the hashes of `out`, so that only a hash match is compared in full.
fn leaves_in(t: &T, w: &Ctx, out: &mut Vec<T>, seen: &mut std::collections::HashSet<u64>, in_bitwise: bool) {
    let mut add = |t: &T| {
        if seen.insert(term_hash(t)) || !out.contains(t) {
            out.push(t.clone());
        }
    };
    match t {
        T::Num(_) => {}
        T::Var(_) => add(t),
        T::Op(op, a) => {
            let k = kind(t, w);
            if k == Kind::Atom || (in_bitwise && k == Kind::Lin && *op != Op::Not) {
                add(t);
            } else {
                let inner = in_bitwise || matches!(op, Op::And | Op::Or | Op::Xor);
                a.iter().for_each(|x| leaves_in(x, w, out, seen, inner));
            }
        }
    }
}

fn eval(t: &T, w: &Ctx, leaf_vals: &[(T, u64)]) -> u64 {
    if let Some((_, v)) = leaf_vals.iter().find(|(l, _)| l == t) {
        return *v;
    }
    let m = w.mask;
    let e = |x: &T| eval(x, w, leaf_vals);
    match t {
        T::Num(c) => *c as u64 & m,
        T::Var(_) => unreachable!("variable missing from leaves"),
        T::Op(op, a) => {
            let r = match op {
                Op::Not => !e(&a[0]),
                Op::Neg => e(&a[0]).wrapping_neg(),
                Op::Add => e(&a[0]).wrapping_add(e(&a[1])),
                Op::Sub => e(&a[0]).wrapping_sub(e(&a[1])),
                Op::Mul => e(&a[0]).wrapping_mul(e(&a[1])),
                Op::And => e(&a[0]) & e(&a[1]),
                Op::Or => e(&a[0]) | e(&a[1]),
                Op::Xor => e(&a[0]) ^ e(&a[1]),
                Op::Shl => e(&a[0]) << const_shift(&a[1], w).unwrap(),
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
    Bin(BinOp, usize, usize),
}

#[derive(Clone, Copy)]
enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
}

impl BinOp {
    fn apply(self, x: u64, y: u64) -> u64 {
        match self {
            BinOp::Add => x.wrapping_add(y),
            BinOp::Sub => x.wrapping_sub(y),
            BinOp::Mul => x.wrapping_mul(y),
            BinOp::And => x & y,
            BinOp::Or => x | y,
            BinOp::Xor => x ^ y,
        }
    }
}

impl Prog {
    pub(crate) fn new(t: &T, lv: &[T], w: &Ctx) -> Prog {
        let mut p = Prog(Vec::new());
        p.push(t, lv, w);
        p
    }

    fn push(&mut self, t: &T, lv: &[T], w: &Ctx) -> usize {
        let ins = match (lv.iter().position(|l| l == t), t) {
            (Some(i), _) => Ins::Leaf(i),
            (_, T::Num(c)) => Ins::Num(*c as u64),
            (_, T::Var(_)) => unreachable!("variable missing from leaves"),
            (_, T::Op(op, a)) => match op {
                Op::Not => Ins::Not(self.push(&a[0], lv, w)),
                Op::Neg => Ins::Neg(self.push(&a[0], lv, w)),
                Op::Shl => Ins::Shl(self.push(&a[0], lv, w), const_shift(&a[1], w).unwrap()),
                op => {
                    let f = match op {
                        Op::Add => BinOp::Add,
                        Op::Sub => BinOp::Sub,
                        Op::Mul => BinOp::Mul,
                        Op::And => BinOp::And,
                        Op::Or => BinOp::Or,
                        Op::Xor => BinOp::Xor,
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

    pub(crate) fn run(&self, leaf: impl Fn(usize) -> u64, w: &Ctx) -> u64 {
        let mut v: Vec<u64> = Vec::with_capacity(self.0.len());
        for ins in &self.0 {
            let r = match *ins {
                Ins::Leaf(i) => leaf(i),
                Ins::Num(c) => c,
                Ins::Not(x) => !v[x],
                Ins::Neg(x) => u64::wrapping_neg(v[x]),
                Ins::Shl(x, k) => v[x] << k,
                Ins::Bin(f, x, y) => f.apply(v[x], v[y]),
            };
            v.push(r & w.mask);
        }
        v[v.len() - 1]
    }

    /// `run` at `n` points at once, leaf `i` at point `k` being `leaf(i, k)`.
    pub(crate) fn run_many(&self, n: usize, leaf: impl Fn(usize, usize) -> u64, w: &Ctx) -> Vec<u64> {
        let mut v = vec![0u64; self.0.len() * n];
        for (i, ins) in self.0.iter().enumerate() {
            let (done, rest) = v.split_at_mut(i * n);
            let out = &mut rest[..n];
            let col = |x: usize| &done[x * n..(x + 1) * n];
            match *ins {
                Ins::Leaf(l) => out.iter_mut().enumerate().for_each(|(k, o)| *o = leaf(l, k)),
                Ins::Num(c) => out.fill(c),
                Ins::Not(x) => out.iter_mut().zip(col(x)).for_each(|(o, a)| *o = !a),
                Ins::Neg(x) => out.iter_mut().zip(col(x)).for_each(|(o, a)| *o = a.wrapping_neg()),
                Ins::Shl(x, s) => out.iter_mut().zip(col(x)).for_each(|(o, a)| *o = a << s),
                Ins::Bin(f, x, y) => {
                    let (a, b) = (col(x), col(y));
                    match f {
                        BinOp::Add => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a.wrapping_add(*b)),
                        BinOp::Sub => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a.wrapping_sub(*b)),
                        BinOp::Mul => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a.wrapping_mul(*b)),
                        BinOp::And => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a & b),
                        BinOp::Or => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a | b),
                        BinOp::Xor => out.iter_mut().zip(a.iter().zip(b)).for_each(|(o, (a, b))| *o = a ^ b),
                    }
                }
            }
            out.iter_mut().for_each(|o| *o &= w.mask);
        }
        v.split_off((self.0.len() - 1) * n)
    }

    /// Value with leaf `i` set to bit `i` of `p`.
    pub(crate) fn at(&self, p: usize, w: &Ctx) -> u64 {
        self.run(|i| (p >> i & 1) as u64, w)
    }
}

/// Largest region (in leaves) that gets rebuilt; truth tables are `u64`.
pub(crate) const MAX_LEAVES: usize = 6;

/// `Σ coef·term + konst`, using Sub/Neg for negative coefficients.
pub(crate) fn build_sum(terms: &[(u64, T)], konst: u64, w: &Ctx) -> T {
    // c·t + c = -c·~t saves the constant term; for c = 1 only inside a longer sum,
    // where `a - ~t` is shorter than `a + t + 1`.
    if konst != 0 && (konst != 1 || terms.len() > 1) {
        if let Some(i) = terms.iter().position(|(c, _)| *c == konst) {
            let mut terms = terms.to_vec();
            let (c, t) = terms.remove(i);
            let not_t = match t {
                T::Op(op, mut a) if op == Op::Not => a.remove(0),
                t => T::Op(Op::Not, vec![t]),
            };
            terms.push((c.wrapping_neg() & w.mask, not_t));
            return build_sum(&terms, 0, w);
        }
    }
    let num = |v: u64| T::Num(w.signed(v));
    let scaled = |c: u64, t: &T| if c == 1 { t.clone() } else { T::Op(Op::Mul, vec![num(c), t.clone()]) };
    let mut acc: Option<T> = None;
    for (c, t) in terms {
        let neg = w.signed(*c) < 0 && *c != 1u64 << (w.w - 1);
        acc = Some(match acc {
            None if *c == w.mask => T::Op(Op::Neg, vec![t.clone()]),
            None => scaled(*c, t),
            Some(a) if neg => T::Op(Op::Sub, vec![a, scaled(c.wrapping_neg() & w.mask, t)]),
            Some(a) => T::Op(Op::Add, vec![a, scaled(*c, t)]),
        });
    }
    match acc {
        None => num(konst),
        Some(a) if konst == 0 => a,
        Some(a) if w.signed(konst) < 0 => T::Op(Op::Sub, vec![a, num(konst.wrapping_neg() & w.mask)]),
        Some(a) => T::Op(Op::Add, vec![a, num(konst)]),
    }
}

/// `size(&build_sum(terms, konst, w))` without building it.
fn sum_size(terms: &[(u64, T)], konst: u64, w: &Ctx) -> usize {
    let terms: Vec<(u64, usize, bool)> = terms.iter().map(|(c, t)| (*c, size(t), matches!(t, T::Op(op, _) if *op == Op::Not))).collect();
    folded_sum_size(&terms, konst, w)
}

/// `sum_size` from each term's coefficient, size and whether it is a `Not`.
fn folded_sum_size(terms: &[(u64, usize, bool)], konst: u64, w: &Ctx) -> usize {
    if konst != 0 && (konst != 1 || terms.len() > 1) {
        if let Some(i) = terms.iter().position(|t| t.0 == konst) {
            let not_size = if terms[i].2 { terms[i].1 - 1 } else { terms[i].1 + 1 };
            let neg = konst.wrapping_neg() & w.mask;
            let rest = terms.iter().enumerate().filter(|&(j, _)| j != i).map(|(_, t)| (t.0, t.1));
            return sized_sum(rest.chain([(neg, not_size)]), 0, w);
        }
    }
    sized_sum(terms.iter().map(|t| (t.0, t.1)), konst, w)
}

fn sized_sum(terms: impl Iterator<Item = (u64, usize)>, konst: u64, w: &Ctx) -> usize {
    let scaled = |c: u64, s: usize| if c == 1 { s } else { s + 2 };
    let mut acc: Option<usize> = None;
    for (c, s) in terms {
        let neg = w.signed(c) < 0 && c != 1u64 << (w.w - 1);
        acc = Some(match acc {
            None if c == w.mask => 1 + s,
            None => scaled(c, s),
            Some(a) if neg => 1 + a + scaled(c.wrapping_neg() & w.mask, s),
            Some(a) => 1 + a + scaled(c, s),
        });
    }
    match acc {
        None => 1,
        Some(a) if konst == 0 => a,
        Some(a) => a + 2,
    }
}

/// `relate_leaves` in the rebuild without `clustered`, where wider regions take seconds.
const UNCLUSTERED_RELATE_LEAVES: usize = 10;
/// Most `rewrite` calls the rebuild without `clustered` makes; past them it is dropped.
const UNCLUSTERED_REWRITES: usize = 256;
/// Most `rewrite` calls of the other rebuilds after which the one without `clustered` is
/// still tried: inputs that need more are slow to rebuild without it.
const UNCLUSTERED_AFTER: usize = 1024;

/// Whether the linear region `t` has a bitwise operation with a constant operand.
fn has_const_bitwise(t: &T, w: &Ctx) -> bool {
    match (t, kind(t, w)) {
        (_, Kind::ConstBit) => true,
        (T::Op(_, a), Kind::Lin) => a.iter().any(|x| has_const_bitwise(x, w)),
        _ => false,
    }
}

/// Replace every linear or polynomial region (and, recursively, regions inside
/// atoms) by its rebuilt form when that is smaller. Memoized per thread.
pub(crate) fn rewrite(t: &T, w: &Ctx) -> T {
    if !matches!(t, T::Op(..)) {
        return t.clone();
    }
    let key = (w.w, t.clone());
    if let Some(r) = memo_get(&w.st.rewritten, &key, w) {
        return r;
    }
    if take_one(&w.st.rewrites_left) == 0 {
        return t.clone();
    }
    let (r, used) = tracking_clusters(w, || rewrite_uncached(t, w));
    w.st.rewritten.lock().unwrap().insert(key, (r.clone(), used));
    r
}

fn rewrite_uncached(t: &T, w: &Ctx) -> T {
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
    r
}

/// The terms `(c, t)` and the constant of the sum `t`, scaled by `c`.
pub(crate) fn sum_terms(t: &T, c: u64, w: &Ctx, out: &mut Vec<(u64, T)>, konst: &mut u64) {
    match t {
        T::Num(v) => *konst = konst.wrapping_add(c.wrapping_mul(*v as u64)) & w.mask,
        T::Op(Op::Add, a) => a.iter().for_each(|x| sum_terms(x, c, w, out, konst)),
        T::Op(Op::Sub, a) => {
            sum_terms(&a[0], c, w, out, konst);
            sum_terms(&a[1], c.wrapping_neg() & w.mask, w, out, konst);
        }
        T::Op(Op::Neg, a) => sum_terms(&a[0], c.wrapping_neg() & w.mask, w, out, konst),
        T::Op(Op::Mul, a) if matches!((&a[0], &a[1]), (T::Num(_), _) | (_, T::Num(_))) => {
            let ((T::Num(k), x) | (x, T::Num(k))) = (&a[0], &a[1]) else { unreachable!() };
            sum_terms(x, c.wrapping_mul(*k as u64) & w.mask, w, out, konst);
        }
        _ => out.push((c, t.clone())),
    }
}

/// `t` with `recombine_products` applied to each linear region, innermost first, and the
/// changed regions rewritten again (`11·L` then joins the rest of its region).
fn recombine_regions(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| recombine_regions(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    match recombine_products(&node, w) {
        Some(s) => {
            let again = rewrite(&s, w);
            if size(&again) < size(&s) { again } else { s }
        }
        None => node,
    }
}

/// The sum `t` with two products `c·P1·Q1 + c·P2·Q2` where `P1 = Q1 + P2 + Q2` written as
/// `c·(Q1 + P2)·(Q1 + Q2)`, which expands to the same: the product identity
/// `a·b = (a | b)·(a & b) + (a & ~b)·(~a & b)` with its factors rebuilt.
fn recombine_products(t: &T, w: &Ctx) -> Option<T> {
    if kind(t, w) != Kind::Lin {
        return None;
    }
    let (mut terms, mut konst) = (Vec::new(), 0);
    sum_terms(t, 1, w, &mut terms, &mut konst);
    let factors = |x: &T| match x {
        T::Op(Op::Mul, a) if !matches!(a[0], T::Num(_)) && !matches!(a[1], T::Num(_)) => Some((a[0].clone(), a[1].clone())),
        _ => None,
    };
    if terms.iter().filter(|(_, x)| factors(x).is_some()).count() < 2 {
        return None;
    }
    let sub = |a: T, b: T| T::Op(Op::Sub, vec![a, b]);
    let add = |a: T, b: T| T::Op(Op::Add, vec![a, b]);
    let mut changed = false;
    'search: loop {
        for i in 0..terms.len() {
            let Some((a, b)) = factors(&terms[i].1) else { continue };
            for j in i + 1..terms.len() {
                let Some((c, d)) = factors(&terms[j].1) else { continue };
                if terms[i].0 != terms[j].0 {
                    continue;
                }
                let ways = [(&a, &b, &c, &d), (&b, &a, &c, &d), (&c, &d, &a, &b), (&d, &c, &a, &b)];
                for (p1, q1, p2, q2) in ways {
                    let diff = sub(sub(sub(p1.clone(), q1.clone()), p2.clone()), q2.clone());
                    if !maybe_zero(&diff, w) || rewrite(&diff, w) != T::Num(0) {
                        continue;
                    }
                    let f1 = rewrite(&add(q1.clone(), p2.clone()), w);
                    let f2 = rewrite(&add(q1.clone(), q2.clone()), w);
                    let coef = terms[i].0;
                    terms.remove(j);
                    terms[i] = match (f1, f2) {
                        (T::Num(k), f) | (f, T::Num(k)) => (coef.wrapping_mul(k as u64) & w.mask, f),
                        (f1, f2) => (coef, T::Op(Op::Mul, vec![f1, f2])),
                    };
                    changed = true;
                    continue 'search;
                }
            }
        }
        break;
    }
    let r = build_sum(&terms, konst, w);
    (changed && size(&r) < size(t)).then_some(r)
}

fn rewrite_linear(t: &T, w: &Ctx) -> T {
    let T::Op(op, args) = t else { return t.clone() };
    if kind(t, w) != Kind::Atom {
        let best = [simba(t, w), small_blocks(t, w)].into_iter().flatten().reduce(|b, x| if size(&x) < size(&b) { x } else { b });
        let best = match (best, wide_blocks(t, w)) {
            (Some(b), Some(x)) if size(&x) >= size(&b) => Some(b),
            (b, None) => b,
            (_, Some(x)) => {
                w.st.used.fetch_or(WIDE, Relaxed);
                Some(x)
            }
        };
        if let Some(best) = best {
            return substitute_atoms(&best, w);
        }
    }
    T::Op(*op, args.iter().map(|a| rewrite(a, w)).collect())
}

/// The terms `(c, t)` and the constant of the linear region `t`, scaled by `c`, with
/// `~a` and `a << k` of arithmetic `a` expanded and like terms merged.
fn region_terms(t: &T, w: &Ctx) -> (Vec<(u64, T)>, u64) {
    fn go(t: &T, c: u64, w: &Ctx, out: &mut Vec<(u64, T)>, konst: &mut u64) {
        let m = w.mask;
        match t {
            T::Num(v) => *konst = konst.wrapping_add(c.wrapping_mul(*v as u64)) & m,
            T::Op(Op::Add, a) => a.iter().for_each(|x| go(x, c, w, out, konst)),
            T::Op(Op::Sub, a) => {
                go(&a[0], c, w, out, konst);
                go(&a[1], c.wrapping_neg() & m, w, out, konst);
            }
            T::Op(Op::Neg, a) => go(&a[0], c.wrapping_neg() & m, w, out, konst),
            T::Op(Op::Not, a) if kind(&a[0], w) == Kind::Lin => {
                *konst = konst.wrapping_sub(c) & m;
                go(&a[0], c.wrapping_neg() & m, w, out, konst);
            }
            T::Op(Op::Mul, a) if matches!((&a[0], &a[1]), (T::Num(_), _) | (_, T::Num(_))) => {
                let ((T::Num(k), x) | (x, T::Num(k))) = (&a[0], &a[1]) else { unreachable!() };
                go(x, c.wrapping_mul(*k as u64) & m, w, out, konst);
            }
            T::Op(Op::Shl, a) if const_shift(&a[1], w).is_some() => {
                let k = const_shift(&a[1], w).unwrap();
                go(&a[0], c.wrapping_shl(k) & m, w, out, konst);
            }
            _ if c == 0 => {}
            _ => match out.iter_mut().find(|(_, x)| x == t) {
                Some(e) => e.0 = e.0.wrapping_add(c) & m,
                None => out.push((c, t.clone())),
            },
        }
    }
    let (mut terms, mut konst) = (Vec::new(), 0);
    go(t, 1, w, &mut terms, &mut konst);
    terms.retain(|(c, _)| *c != 0);
    (terms, konst)
}

/// `t` with `clustered` applied to each linear region of more than `MAX_LEAVES` leaves,
/// innermost first.
fn cluster_regions(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| cluster_regions(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    let mut lv = Vec::new();
    leaves(&node, w, &mut lv);
    if lv.len() <= MAX_LEAVES {
        return node;
    }
    match clustered(&node, w) {
        Some(c) => {
            w.st.used.fetch_or(CLUSTERED, Relaxed);
            c
        }
        None => node,
    }
}

/// `f()`, and which of `clustered` and `wide_blocks` gave a kept form during it (which then
/// also counts for the enclosing call).
fn tracking_clusters<R>(w: &Ctx, f: impl FnOnce() -> R) -> (R, u8) {
    let outer = w.st.used.swap(0, Relaxed);
    let r = f();
    let used = w.st.used.load(Relaxed);
    w.st.used.store(outer | used, Relaxed);
    (r, used)
}

/// A memoized result, unless it came from a pass that is now off.
fn memo_get<K: std::hash::Hash + Eq, V: Clone>(memo: &Memo<K, V>, key: &K, w: &Ctx) -> Option<V> {
    let (r, used) = memo.lock().unwrap().get(key).cloned()?;
    if used & w.st.excluded.load(Relaxed) != 0 {
        return None;
    }
    w.st.used.fetch_or(used, Relaxed);
    Some(r)
}

/// Most `rewrite` calls the rebuild of the input with unified operands makes; past them it is dropped.
const UNIFIED_REWRITES: usize = 128;
/// Rewrite inside the atom leaves of a rebuilt region.
fn substitute_atoms(t: &T, w: &Ctx) -> T {
    match t {
        T::Op(op, args) => {
            if kind(t, w) == Kind::Atom {
                rewrite(t, w)
            } else {
                T::Op(*op, args.iter().map(|a| substitute_atoms(a, w)).collect())
            }
        }
        _ => t.clone(),
    }
}

/// Rebuilds of at most this size are not searched further: the input is not halved, and
/// the driver does not saturate the input beside them.
pub const TINY: usize = 3;

/// Candidates of `simplify_linear_uncached` rebuilt with subterms abstracted to variables,
/// kept only when at most 3/4 the size of the first rebuild.
const ABSTRACTED: [&str; 2] = ["over_const_bitwise", "over_shared_bitwise"];

/// The rebuild `simplify_linear` applies to its input, without `relate`.
fn rebuild_once(t: &T, w: &Ctx) -> T {
    let t = unshift(&crate::lowbits::simplify(t, w), w);
    crate::tfunc::replacement(&t, w).unwrap_or_else(|| crate::tfunc::simplify(&cluster_regions(&rewrite(&t, w), w, false), w))
}

/// Rewrite the egglog term `egg` (W-bit wrapping semantics) with every linear
/// MBA region, and every polynomial MBA region,
/// rebuilt in a smaller form. Returns `egg` unchanged when nothing gets smaller.
pub fn simplify_linear(egg: &str, w: u32) -> String {
    simplify_linear_with(egg, w, false).0
}

/// `simplify_linear`, and the other rebuilds worth unioning: the next smallest (`egg` and
/// its first rebuild are also rebuilt with bitwise operations of even operands halved,
/// `halve`, and which result the rules finish best is not known) and the first rebuild
/// without `clustered`, when that was used.
pub fn simplify_linear_both(egg: &str, w: u32) -> (String, Vec<String>) {
    simplify_linear_with(egg, w, false)
}

/// `simplify_linear_both`, printing the candidates to stderr when `trace` is set.
pub fn simplify_linear_with(egg: &str, w: u32, trace: bool) -> (String, Vec<String>) {
    type Result = (String, Vec<String>);
    type Last = Option<(String, u32, bool, Result)>;
    thread_local! {
        static LAST: std::cell::RefCell<Last> = const { std::cell::RefCell::new(None) };
    }
    let hit = |(e, bits, t, _): &&(String, u32, bool, Result)| e == egg && *bits == w && *t == trace;
    match LAST.with(|c| c.borrow().as_ref().filter(hit).map(|l| l.3.clone())) {
        Some(r) => r,
        None => {
            let r = simplify_linear_uncached(egg, w, trace);
            LAST.with(|c| *c.borrow_mut() = Some((egg.to_string(), w, trace, r.clone())));
            r
        }
    }
}

/// Rewrites of a rebuilt candidate that would break subterms the rebuild relates if done
/// earlier: recombined products, product factors with constants cut below trailing zeros,
/// and `shifted_xor`.
fn finish(t: &T, w: &Ctx) -> T {
    // Products selected by a bit are left whole for `split_bits` in the next round (Hikari).
    let t = if selectors(t, w).is_empty() { recombine_regions(t, w, false) } else { t.clone() };
    let t = crate::lowbits::shifted_xor(&crate::lowbits::cut_products(&t, w), w);
    // Rebuilds can leave bits known by evaluation only (`-(A & B) & 1` with `A & B` even).
    let low = crate::lowbits::simplify_rebuilt(&t, w);
    if size(&low) < size(&t) { low } else { t }
}

/// `t` without additions of 0, multiplications by 1 and bitwise operations with their
/// identity.
fn drop_identities(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| drop_identities(x, w)).collect();
    let is = |x: &T, k: u64| matches!(x, T::Num(v) if *v as u64 & w.mask == k);
    match (op, a.as_slice()) {
        (Op::Add | Op::Or | Op::Xor, [x, z]) | (Op::Add | Op::Or | Op::Xor, [z, x]) | (Op::Sub, [x, z]) if is(z, 0) => x.clone(),
        (Op::And, [x, m]) | (Op::And, [m, x]) if is(m, w.mask) => x.clone(),
        (Op::Mul, [x, o]) | (Op::Mul, [o, x]) if is(o, 1) => x.clone(),
        _ => T::Op(*op, a),
    }
}

/// The pre-pass result and the forms to union with it.
fn simplify_linear_uncached(egg: &str, w: u32, trace: bool) -> (String, Vec<String>) {
    use crate::stats;
    let clock = std::time::Instant::now();
    let w = Ctx::new(w);
    let t = parse(egg);
    let t0 = t.clone();
    let t = unshift(&crate::lowbits::simplify(&t, &w), &w);
    // Subterms are replaced only after the rebuild: earlier, `~(y - 1)` would become
    // `-y`, a leaf the rebuild no longer relates to `y - 1`.
    let run = |t: &T, related: bool| match crate::tfunc::replacement(t, &w) {
        Some(r) => r,
        None => {
            let r = cluster_regions(&rewrite(t, &w), &w, false);
            crate::tfunc::simplify(&if related { relate(&r, &w) } else { r }, &w)
        }
    };
    let r = run(&t, true);
    stats::add("pre/first/made", stats::since(clock));
    let clock = std::time::Instant::now();
    let mut first_name = "first";
    // Unified operands let the regions around them share leaves, but the rebuild of the
    // input as written is sometimes smaller. The second rebuild redoes only the regions
    // unification changed, and is dropped once it needs `UNIFIED_REWRITES` rewrites.
    let unified = unify_operands(&t, &w);
    let r = if unified != t {
        let left = w.st.rewrites_left.load(Relaxed);
        w.limit_rewrites(UNIFIED_REWRITES);
        let within = || w.st.rewrites_left.load(Relaxed) > 0;
        let u = match crate::tfunc::replacement(&unified, &w) {
            Some(u) => Some(u),
            None => Some(rewrite(&unified, &w))
                .filter(|_| within())
                .map(|u| relate(&cluster_regions(&u, &w, false), &w))
                .filter(|_| within())
                .map(|u| crate::tfunc::simplify(&u, &w)),
        };
        let used = UNIFIED_REWRITES - w.st.rewrites_left.load(Relaxed);
        w.limit_rewrites(left.saturating_sub(used));
        stats::add("pre/unified/made", stats::since(clock));
        match u {
            Some(u) if size(&u) < size(&r) => {
                first_name = "unified";
                u
            }
            _ => r,
        }
    } else {
        r
    };
    let mut rebuilt: Vec<(&str, T)> = vec![(first_name, r.clone())];
    let mut clock = std::time::Instant::now();
    let made_by = |name: &str, clock: &mut std::time::Instant| {
        stats::add(&format!("pre/{name}/made"), stats::since(*clock));
        *clock = std::time::Instant::now();
    };
    // A region rebuilt by `wide_blocks` is smaller there, but the other rebuilds can leave
    // subterms the abstracted rebuilds share across terms. Only smaller ones are kept: a
    // larger one unioned beside the first rebuild made the rules finish worse as often as better.
    if w.st.used.load(Relaxed) & WIDE != 0 {
        w.st.excluded.store(WIDE, Relaxed);
        let n = run(&t, true);
        let abstracted = [over_const_bitwise(&n, &w), over_shared_bitwise(&n, &w)];
        w.st.excluded.store(0, Relaxed);
        made_by("no_wide", &mut clock);
        for (name, o) in [("no_wide", n.clone())].into_iter().chain(abstracted.map(|o| ("no_wide_abstracted", o))) {
            if size(&o) < size(&r) && (name == "no_wide" || 4 * size(&o) <= 3 * size(&n)) {
                rebuilt.push((name, o));
            }
        }
    }
    if size(&r) <= MAX_SPLIT_SIZE {
        let s = split_in(&r, &w, &|t| run(&unshift(&crate::lowbits::simplify(t, &w), &w), false));
        if s != r {
            rebuilt.push(("split_bits", s));
        }
        made_by("split_bits", &mut clock);
    }
    let hr = halve(&r, &w);
    if hr != r {
        rebuilt.push(("halve_first", run(&hr, false)));
    }
    made_by("halve_first", &mut clock);
    let pr = crate::lowbits::over_products(&r, &w, |t| rebuild_once(t, &w));
    if pr != r {
        rebuilt.push(("over_products", pr));
    }
    made_by("over_products", &mut clock);
    for (name, o) in [("over_const_bitwise", over_const_bitwise(&r, &w)), ("over_shared_bitwise", over_shared_bitwise(&r, &w))] {
        if o != r {
            rebuilt.push((name, o));
        }
    }
    made_by("over_bitwise", &mut clock);
    // Halving the whole input can give semi-linear regions that are slow to search,
    // so only small ones are rebuilt there, also inside `halve`.
    w.st.semi_leaves.store(2, Relaxed);
    let ht = if size(&r) <= TINY { t.clone() } else { halve(&t, &w) };
    if ht != t {
        rebuilt.push(("halve_input", run(&ht, false)));
    }
    made_by("halve_input", &mut clock);
    w.st.semi_leaves.store(MAX_LEAVES, Relaxed);
    let mut rebuilt: Vec<(&str, T)> = rebuilt.into_iter().map(|(n, t)| (n, finish(&t, &w))).collect();
    // A form from abstracted subterms only a little smaller than the first rebuild, or
    // larger, made the rules finish worse at least as often as better (Ensia, LLVM Pluto);
    // much smaller ones mostly win.
    let first = size(&rebuilt[0].1);
    let dropped: Vec<String> = rebuilt.iter().filter(|(n, t)| ABSTRACTED.contains(n) && 4 * size(t) > 3 * first).map(|(n, t)| format!("{n} {}", size(t))).collect();
    rebuilt.retain(|(n, t)| !ABSTRACTED.contains(n) || 4 * size(t) <= 3 * first);
    // A region rebuilt in clusters is smaller there but can leave the rules a worse
    // start than rebuilding it whole, so the rebuild without clusters is kept too.
    let made = usize::MAX - w.st.rewrites_left.load(Relaxed);
    let unclustered = if w.st.used.load(Relaxed) & CLUSTERED != 0 && made <= UNCLUSTERED_AFTER && crate::tfunc::replacement(&t, &w).is_none() {
        w.st.bit_splits.store(BIT_SPLIT_BUDGET, Relaxed);
        w.st.excluded.store(CLUSTERED, Relaxed);
        w.st.relate_leaves.store(UNCLUSTERED_RELATE_LEAVES, Relaxed);
        w.st.rewrites_left.store(UNCLUSTERED_REWRITES, Relaxed);
        let within = || w.st.rewrites_left.load(Relaxed) > 0;
        let r = Some(rewrite(&t, &w)).filter(|_| within());
        let r = r.map(|r| relate(&r, &w)).filter(|_| within());
        let u = r.map(|r| drop_identities(&finish(&crate::tfunc::simplify(&r, &w), &w), &w));
        w.st.rewrites_left.store(usize::MAX, Relaxed);
        w.st.relate_leaves.store(MAX_WIDE_LEAVES, Relaxed);
        w.st.excluded.store(0, Relaxed);
        made_by("unclustered", &mut clock);
        u
    } else {
        None
    };
    for (n, t) in &rebuilt {
        if *n != first_name {
            stats::add(&format!("pre/{n}/differs"), 0.0);
        }
        stats::label(&show(t), n);
    }
    if let Some(u) = &unclustered {
        stats::add("pre/unclustered/differs", 0.0);
        stats::label(&show(u), "unclustered");
    }
    if trace {
        let all: Vec<String> = rebuilt.iter().map(|(n, t)| format!("{n} {}", size(t))).chain(unclustered.iter().map(|u| format!("unclustered {}", size(u)))).collect();
        eprintln!("prepass: input {} candidates: {}; dropped: {}", size(&t0), all.join(", "), dropped.join(", "));
    }
    rebuilt.sort_by_key(|(_, t)| size(t));
    rebuilt.dedup_by(|a, b| a.1 == b.1);
    rebuilt.truncate(2);
    // An equal-size one can take the extraction from the first rebuild with nothing gained.
    match unclustered {
        Some(u) if size(&u) < size(&rebuilt[0].1) => rebuilt.insert(0, ("unclustered", u)),
        Some(u) if size(&u) > size(&rebuilt[0].1) && size(&u) < size(&t0) && !rebuilt.iter().any(|(_, t)| *t == u) => rebuilt.push(("unclustered", u)),
        _ => {}
    }
    if trace {
        let kept: Vec<String> = rebuilt.iter().map(|(n, t)| format!("{n} {}", size(t))).collect();
        eprintln!("prepass: chosen {}", kept.join(", then "));
    }
    for (i, (n, _)) in rebuilt.iter().enumerate() {
        stats::add(&format!("pre/{n}/{}", if i == 0 { "main" } else { "kept" }), 0.0);
    }
    let others: Vec<T> = rebuilt.split_off(1).into_iter().map(|(_, t)| t).collect();
    let r = rebuilt.swap_remove(0).1;
    let r = if r == t0 { egg.to_string() } else { show(&r) };
    (r, others.iter().map(show).collect())
}
