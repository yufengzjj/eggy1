//! Linear MBA simplification (SiMBA-style). A linear MBA, i.e. a sum of
//! constant multiples of bitwise functions, is fully determined by its values
//! on {0,1}^n, so it can be rebuilt from those values in a minimal form.
//! Subterms that are not linear (`x*y`, `x >> 3`, ...) are treated as opaque
//! variables; the identity holds for any value they take. Bitwise operations
//! with constant operands (`x & 0xff`) make the region semi-linear: each bit
//! position then has its own bitwise function, see `semi_linear`.

use crate::eval::{Op, Term as T, show, size};
use crate::sched::{Limit, Passes, limit};
use crate::stats;
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
pub(crate) use polish::POLISH;
pub(crate) use linear::simba_memo;
pub(crate) use split::low_consts;
pub(crate) use wide::MAX_WIDE_LEAVES;

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
    /// Whether `>>` is arithmetic; `None` where a result must hold for both.
    pub(crate) signed: Option<bool>,
    st: std::sync::Arc<State>,
}

impl Ctx {
    #[cfg(test)]
    pub(crate) fn new(w: u32) -> Ctx {
        Ctx::typed(w, None)
    }
    pub(crate) fn typed(w: u32, signed: Option<bool>) -> Ctx {
        Ctx { w, mask: if w == 64 { u64::MAX } else { (1u64 << w) - 1 }, signed, st: Default::default() }
    }
    /// The same run at width `w`, sharing its state; `>>` there has no signedness unless
    /// `w` is the width of this run.
    pub(crate) fn narrow(&self, w: u32) -> Ctx {
        Ctx { st: self.st.clone(), ..Ctx::typed(w, self.signed.filter(|_| w == self.w)) }
    }
    /// Which of `clustered` (`CLUSTERED`) and `wide_blocks` (`WIDE`) gave a kept form since
    /// the last call, which sets it to `v`.
    pub(crate) fn swap_used(&self, v: u8) -> u8 {
        self.st.used.swap(v, Relaxed)
    }
    pub(crate) fn low_values(&self) -> &crate::lowbits::ValuesMemo {
        &self.st.low_values
    }
    pub(super) fn semi_leaves(&self) -> usize {
        crate::sched::read(crate::sched::SEMI_LEAVES) as usize
    }
    pub(super) fn relate_leaves(&self) -> usize {
        crate::sched::read(crate::sched::RELATE_LEAVES) as usize
    }
    pub(super) fn peel_depth(&self) -> usize {
        self.read(|d| d.peel = true);
        self.st.peel_depth.load(Relaxed)
    }
    /// Records in the running computation's `Deps` what it read.
    fn read(&self, f: impl FnOnce(&mut Deps)) {
        f(&mut self.st.deps.lock().unwrap());
    }
    /// Whether a region `clustered` is running on has a hash in `hs` (sorted).
    fn in_clustering(&self, hs: &[u64]) -> bool {
        self.st.clustering.lock().unwrap().iter().any(|(h, _)| hs.binary_search(h).is_ok())
    }
    fn clustering_depth(&self) -> i64 {
        self.st.clustering.lock().unwrap().len() as i64
    }
    /// Records that the running computation was cut short, so it is not memoized.
    pub(crate) fn mark_cut(&self) {
        self.read(|d| d.cut = true);
    }
    /// Takes one from the budget variable `i` (`crate::sched::take`), or records a cut when
    /// it is used up.
    fn take_budget(&self, i: usize) -> bool {
        let ok = crate::sched::take(i);
        if !ok {
            self.read(|d| d.cut = true);
        }
        ok
    }
    pub(crate) fn signed(&self, v: u64) -> i64 {
        let sh = 64 - self.w;
        ((v << sh) as i64) >> sh
    }
}

/// Memoized results with what each depends on; a key can hold results for a few contexts.
type Memo<K, V> = std::sync::Mutex<crate::eval::FastMap<K, Vec<Entry<V>>>>;

/// What a computation read besides its key, collected while it runs (`tracked`).
#[derive(Clone)]
struct Deps {
    peel: bool,
    /// The changes of the `clustered` nesting depth at its start that keep every depth
    /// check inside it the same.
    shift: (i64, i64),
    /// Hashes of the regions `clustered` ran on inside it, which must not be running
    /// already where the result is reused.
    absent: Vec<u64>,
    /// A budget or a cycle check refused work, so the result is not the one a full run gives.
    cut: bool,
}

const ANY_SHIFT: (i64, i64) = (i64::MIN / 4, i64::MAX / 4);

impl Default for Deps {
    fn default() -> Deps {
        Deps { peel: false, shift: ANY_SHIFT, absent: Vec::new(), cut: false }
    }
}

impl Deps {
    fn add(&mut self, o: &Deps) {
        self.peel |= o.peel;
        self.cut |= o.cut;
        self.shift = (self.shift.0.max(o.shift.0), self.shift.1.min(o.shift.1));
        self.absent.extend_from_slice(&o.absent);
    }
    /// A `clustered` call on a region with hash `h` at nesting depth `depth` (limit `max`),
    /// refused when `deep` or a `cycle`.
    fn nesting(&mut self, depth: i64, max: i64, deep: bool, cycle: bool, h: u64) {
        let s = &mut self.shift;
        *s = if deep { (s.0.max(max - depth), s.1) } else { (s.0, s.1.min(max - 1 - depth)) };
        if cycle {
            self.cut = true;
        } else if !deep {
            self.absent.push(h);
        }
    }
}

/// A memoized result, valid where the variables in `read` (`crate::sched::var`) have the
/// values `vals` and the run state it read has the values given.
#[derive(Clone)]
struct Entry<V> {
    v: V,
    /// `State::used` of the computation.
    used: u8,
    read: u128,
    vals: Vec<u64>,
    peel: Option<usize>,
    /// The `clustered` nesting depths it holds at, and `Deps::absent` sorted.
    depths: (i64, i64),
    absent: Vec<u64>,
}

/// Most results one memo key keeps, the oldest dropped first.
const MEMO_CONTEXTS: usize = 4;

/// Bits of `State::used`.
pub(crate) const CLUSTERED: u8 = 1;
pub(crate) const WIDE: u8 = 2;
type RebuiltKey = (Vec<u64>, Vec<(usize, bool)>, u64, u32);
type GroupedKey = (Vec<(Vec<u64>, u64)>, Vec<T>, u64, u32);
type PairKey = (u32, Vec<(Vec<u64>, u64)>, u64, Vec<T>, usize);

struct State {
    simba_memo: Memo<(u32, T), Option<T>>,
    rewritten: Memo<(u32, T), T>,
    related: Memo<(u32, T), T>,
    rebuilt: std::sync::Mutex<crate::eval::FastMap<RebuiltKey, (Vec<(u64, T)>, u64)>>,
    grouped: std::sync::Mutex<crate::eval::FastMap<GroupedKey, T>>,
    low_values: crate::lowbits::ValuesMemo,
    pairs: std::sync::Mutex<crate::eval::FastMap<PairKey, Vec<T>>>,
    /// `peel` calls nested inside each other.
    peel_depth: AtomicUsize,
    /// The regions `clustered` is running on, with their hashes.
    clustering: std::sync::Mutex<Vec<(u64, T)>>,
    deps: std::sync::Mutex<Deps>,
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
            peel_depth: AtomicUsize::new(0),
            clustering: Default::default(),
            deps: Default::default(),
            used: AtomicU8::new(0),
        }
    }
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
    let f = || stats::try_pass("rewrite", t, || rewrite_uncached(t, w));
    if let Some(r) = memo_get(&w.st.rewritten, &key, w, "rewrite", f) {
        return r;
    }
    if !w.take_budget(crate::sched::REWRITES) {
        return t.clone();
    }
    memo_compute(&w.st.rewritten, key, w, f)
}

/// `t` rebuilt by `Passes::subs` entry `i` (`crate::sched::SUBS`), for a pass that rebuilds
/// a subterm.
pub(crate) fn sub(i: usize, t: &T, w: &Ctx) -> T {
    let p = crate::sched::current();
    match &p.subs[i] {
        crate::sched::Pipe::Pass(crate::sched::Pass::Term { name, .. }) if name == "rewrite" => rewrite(t, w),
        crate::sched::Pipe::Pass(crate::sched::Pass::Term { name, .. }) if name == "rebuild" => rebuild_once(t, w),
        pipe => crate::pipe::run_term(pipe, t, w),
    }
}

pub(crate) use crate::sched::sub_index;

fn rewrite_uncached(t: &T, w: &Ctx) -> T {
    crate::pipe::run_term(&crate::sched::current().rewrite, t, w)
}

/// `t` with its linear region rebuilt by `rebuild` and the atom leaves of that form
/// rewritten, or, when `t` is not a region or `rebuild` finds no form, with its operands
/// rewritten (`crate::sched::Pipe::Regions`).
pub(crate) fn on_region(t: &T, w: &Ctx, rebuild: impl FnOnce() -> Option<T>) -> T {
    let T::Op(op, args) = t else { return t.clone() };
    if kind(t, w) != Kind::Atom
        && let Some(r) = rebuild()
    {
        return substitute_atoms(&r, w);
    }
    T::Op(*op, args.iter().map(|a| rewrite(a, w)).collect())
}

/// `r`, a rebuild of `t`, rewritten again when that is smaller and `t` has an arithmetic
/// leaf of a bitwise operation (`crate::sched::Pipe::Again`): once `9*(A & B) + ...` becomes
/// `2*A - B` with `A = -(x ^ y)`, A's own linear form joins the enclosing region.
pub(crate) fn again(t: &T, r: &T, w: &Ctx) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    if r == t || !lv.iter().any(|l| kind(l, w) == Kind::Lin) {
        return None;
    }
    Some(rewrite(r, w)).filter(|a| size(a) < size(r))
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
            let again = sub(sub_index("recombine"), &s, w);
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
                    let f1 = crate::linear_mba::sub(sub_index("recombine"), &add(q1.clone(), p2.clone()), w);
                    let f2 = crate::linear_mba::sub(sub_index("recombine"), &add(q1.clone(), q2.clone()), w);
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
    match stats::pass("cluster_regions", &node, || clustered(&node, w)) {
        Some(c) => {
            w.st.used.fetch_or(CLUSTERED, Relaxed);
            c
        }
        None => node,
    }
}

/// `f()`, which of `clustered` and `wide_blocks` gave a kept form during it, the variables
/// it read and what else it read; all of it also counts for the enclosing call.
fn tracked<R>(w: &Ctx, f: impl FnOnce() -> R) -> (R, u8, u128, Deps) {
    let used0 = w.st.used.swap(0, Relaxed);
    let read0 = crate::sched::swap_read(0);
    let deps0 = std::mem::take(&mut *w.st.deps.lock().unwrap());
    let r = f();
    let used = w.st.used.load(Relaxed);
    w.st.used.store(used0 | used, Relaxed);
    let read = crate::sched::swap_read(0);
    crate::sched::swap_read(read0 | read);
    let deps = {
        let mut d = w.st.deps.lock().unwrap();
        let inner = std::mem::replace(&mut *d, deps0);
        d.add(&inner);
        inner
    };
    (r, used, read, deps)
}

/// `f()` with nothing it changes in the run state kept: budgets, `used`, the tracked reads.
fn isolated<R>(w: &Ctx, f: impl FnOnce() -> R) -> (R, Deps) {
    let st = &w.st;
    let budgets = [crate::sched::REWRITES, crate::sched::BIT_SPLITS].map(|i| (i, crate::sched::get(i)));
    let used = st.used.load(Relaxed);
    let read = crate::sched::swap_read(0);
    let deps = st.deps.lock().unwrap().clone();
    let (r, _, _, d) = tracked(w, f);
    budgets.iter().for_each(|&(i, v)| crate::sched::set(i, v));
    st.used.store(used, Relaxed);
    crate::sched::swap_read(read);
    *st.deps.lock().unwrap() = deps;
    (r, d)
}

/// The bits of `State::used` whose pass is now off.
pub(super) fn used_off() -> u8 {
    const C: usize = crate::sched::inner_index("clustered");
    const W: usize = crate::sched::inner_index("wide_blocks");
    (crate::sched::is_off_at(C) as u8 * CLUSTERED) | (crate::sched::is_off_at(W) as u8 * WIDE)
}

/// With `EGGY_CHECK_MEMO` set, each memo hit outside another check is computed again and
/// compared, and differences are counted in `memo/differs/NAME` and printed.
fn check_memo() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("EGGY_CHECK_MEMO").is_some())
}

thread_local! {
    static CHECKING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The result memoized for `key` that holds in the current run state; what it read then
/// counts for the running computation too. `f` computes it again for `check_memo`.
fn memo_get<K: std::hash::Hash + Eq, V: Clone + PartialEq>(memo: &Memo<K, V>, key: &K, w: &Ctx, name: &str, f: impl FnOnce() -> V) -> Option<V> {
    let e = {
        let m = memo.lock().unwrap();
        m.get(key)?.iter().find(|e| holds(e, w)).cloned()?
    };
    w.st.used.fetch_or(e.used, Relaxed);
    crate::sched::swap_read(crate::sched::swap_read(0) | e.read);
    let at = w.clustering_depth();
    let shift = (e.depths.0 - at, e.depths.1 - at);
    w.read(|d| d.add(&Deps { peel: e.peel.is_some(), shift, absent: e.absent.clone(), cut: false }));
    if check_memo() && !CHECKING.with(|c| c.replace(true)) {
        let (again, d) = isolated(w, f);
        CHECKING.with(|c| c.set(false));
        if !d.cut && again != e.v {
            stats::add(&format!("memo/differs/{name}"), 0.0);
            eprintln!("memo: {name} hit differs from a new run");
        }
    }
    Some(e.v)
}

fn holds<V>(e: &Entry<V>, w: &Ctx) -> bool {
    let st = &w.st;
    crate::sched::same_values(e.read, &e.vals)
        && e.peel.is_none_or(|v| v == st.peel_depth.load(Relaxed))
        && (e.depths.0..=e.depths.1).contains(&w.clustering_depth())
        && (e.absent.is_empty() || !w.in_clustering(&e.absent))
}

/// `f()`, memoized for `key` unless a budget or a cycle check cut it short.
fn memo_compute<K: std::hash::Hash + Eq, V: Clone>(memo: &Memo<K, V>, key: K, w: &Ctx, f: impl FnOnce() -> V) -> V {
    let (v, used, mut read, mut d) = tracked(w, f);
    if d.cut {
        return v;
    }
    // `clustered` and `wide_blocks` are alternatives: a result neither gave holds without them.
    for (bit, name) in [(CLUSTERED, "clustered"), (WIDE, "wide_blocks")] {
        let i = crate::sched::inner_index(name);
        if used & bit == 0 && crate::sched::get(i) == 1 {
            read &= !(1u128 << i);
        }
    }
    let st = &w.st;
    let mut absent = std::mem::take(&mut d.absent);
    absent.sort_unstable();
    absent.dedup();
    let e = Entry {
        v: v.clone(),
        used,
        read,
        vals: crate::sched::values(read),
        peel: d.peel.then(|| st.peel_depth.load(Relaxed)),
        depths: {
            let at = w.clustering_depth();
            (at + d.shift.0, at + d.shift.1)
        },
        absent,
    };
    let mut m = memo.lock().unwrap();
    let list = m.entry(key).or_default();
    list.retain(|o| !holds(o, w));
    if list.len() >= MEMO_CONTEXTS {
        list.remove(0);
    }
    list.push(e);
    v
}

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

/// Pre-pass candidates rebuilt with subterms abstracted to variables, kept only when at most
/// 3/4 the size of the first rebuild.
pub(crate) const ABSTRACTED: [&str; 2] = ["over_const_bitwise", "over_shared_bitwise"];

/// The rebuild `simplify_linear` applies to its input, without `relate`.
pub(crate) fn rebuild_once(t: &T, w: &Ctx) -> T {
    let t = unshift(&crate::lowbits::simplify(t, w), w);
    crate::tfunc::replacement(&t, w).unwrap_or_else(|| crate::tfunc::simplify(&cluster_regions(&rewrite(&t, w), w, false), w))
}

/// The passes over one term that `crate::pipe` runs by name: each gives an equivalent
/// term, or `None` when it does not apply (see `ALTERNATIVES`).
pub(crate) const TERM_PASSES: &[(&str, fn(&T, &Ctx) -> Option<T>)] = &[
    ("lowbits", |t, w| Some(crate::lowbits::simplify(t, w))),
    ("unshift", |t, w| Some(unshift(t, w))),
    ("tfunc_whole", |t, w| crate::tfunc::replacement(t, w)),
    ("rewrite", |t, w| Some(rewrite(t, w))),
    ("rewrite_top", |t, w| Some(rewrite(t, w))),
    ("cluster_regions", |t, w| Some(cluster_regions(t, w, false))),
    ("cluster_top", |t, w| Some(cluster_regions(t, w, false))),
    ("relate", |t, w| Some(relate(t, w))),
    ("tfunc", |t, w| Some(crate::tfunc::simplify(t, w))),
    ("unify_operands", |t, w| Some(unify_operands(t, w))),
    ("recombine", |t, w| Some(recombine_regions(t, w, false))),
    ("cut_products", |t, w| Some(crate::lowbits::cut_products(t, w))),
    ("shifted_xor", |t, w| Some(crate::lowbits::shifted_xor(t, w))),
    ("simplify_rebuilt", |t, w| Some(crate::lowbits::simplify_rebuilt(t, w))),
    ("finish", |t, w| Some(finish(t, w))),
    ("halve", |t, w| Some(halve(t, w))),
    ("over_const_bitwise", |t, w| Some(over_const_bitwise(t, w))),
    ("over_shared_bitwise", |t, w| Some(over_shared_bitwise(t, w))),
    ("over_products", |t, w| Some(crate::lowbits::over_products(t, w, |x| sub(sub_index("over_products"), x, w)))),
    ("split_bits", |t, w| Some(split_in(t, w, &|x| sub(sub_index("split_bits"), x, w)))),
    ("drop_identities", |t, w| Some(drop_identities(t, w))),
    ("rebuild", |t, w| Some(rebuild_once(t, w))),
    ("simba", simba),
    ("small_blocks", small_blocks),
    ("wide_blocks", wide_blocks),
    ("poly_mba", crate::poly_mba::simplify_poly),
    ("drop_unused", drop_unused_pass),
    ("clustered", clustered),
    ("peel", peel),
    ("peel_clustered", peel),
    ("semi_linear", semi_linear_pass),
    ("rebuild_values", rebuild_values_pass),
    ("common_multiple", common_multiple_pass),
    ("related_leaves", related_leaves_pass),
    ("one_wide_term", one_wide_term_pass),
];

/// Passes of `TERM_PASSES` that are alternatives: each runs on the candidate whole and gives
/// no candidate when it finds no form, and the `State::used` bit its form sets when kept.
pub(crate) const ALTERNATIVES: [(&str, u8); 13] = [
    ("simba", 0),
    ("small_blocks", 0),
    ("wide_blocks", WIDE),
    ("poly_mba", 0),
    ("drop_unused", 0),
    ("clustered", CLUSTERED),
    ("peel", 0),
    ("peel_clustered", 0),
    ("semi_linear", 0),
    ("rebuild_values", 0),
    ("common_multiple", 0),
    ("related_leaves", 0),
    ("one_wide_term", 0),
];

/// Number of leaves of the linear region `t` (`crate::pipe` conditions).
pub(crate) fn leaf_count(t: &T, w: &Ctx) -> usize {
    region_leaves(t, w).len()
}

/// Whether the linear region `t` has a bitwise operation with a constant operand.
pub(crate) fn const_bitwise(t: &T, w: &Ctx) -> bool {
    has_const_bitwise(t, w)
}

/// The pass over one term at `at`.
pub(crate) fn term_pass_at(at: crate::sched::TermAt) -> TermPass {
    match at {
        crate::sched::TermAt::Term(i) => TermPass::Term(TERM_PASSES[i].1),
        crate::sched::TermAt::Polish(i) => TermPass::Polish(POLISH[i].1),
    }
}

#[derive(Clone, Copy)]
pub(crate) enum TermPass {
    Term(fn(&T, &Ctx) -> Option<T>),
    Polish(fn(&T, &Ctx) -> T),
}

impl TermPass {
    pub(crate) fn run(self, t: &T, w: &Ctx) -> Option<T> {
        match self {
            TermPass::Term(f) => f(t, w),
            TermPass::Polish(f) => Some(f(t, w)),
        }
    }
}

/// Rewrite the egglog term `egg` (W-bit wrapping semantics) with every linear
/// MBA region, and every polynomial MBA region,
/// rebuilt in a smaller form. Returns `egg` unchanged when nothing gets smaller.
pub fn simplify_linear(egg: &str, w: u32) -> String {
    simplify_linear_with(egg, w, None, false, &Passes::default()).0
}

/// `simplify_linear`, and the other rebuilds worth unioning: the next smallest (`egg` and
/// its first rebuild are also rebuilt with bitwise operations of even operands halved,
/// `halve`, and which result the rules finish best is not known) and the first rebuild
/// without `clustered`, when that was used.
pub fn simplify_linear_both(egg: &str, ty: crate::eval::NumType) -> (String, Vec<String>) {
    simplify_linear_with(egg, ty.bits, Some(ty.signed), false, &Passes::default())
}

/// `simplify_linear_both` with the candidates of `p`, printing them to stderr when `trace`
/// is set; `signed` as in `Ctx`.
pub fn simplify_linear_with(egg: &str, w: u32, signed: Option<bool>, trace: bool, p: &Passes) -> (String, Vec<String>) {
    type Result = (String, Vec<String>);
    type Last = Option<(String, u32, Option<bool>, bool, Passes, Vec<u64>, Result)>;
    thread_local! {
        static LAST: std::cell::RefCell<Last> = const { std::cell::RefCell::new(None) };
    }
    crate::sched::apply(p);
    // A variable bound where it is called (`(off NAME)`, `with`) changes the result as `p` does.
    let vars = crate::sched::key();
    let hit = |(e, bits, s, t, q, v, _): &&(String, u32, Option<bool>, bool, Passes, Vec<u64>, Result)| e == egg && *bits == w && *s == signed && *t == trace && q == p && *v == vars;
    match LAST.with(|c| c.borrow().as_ref().filter(hit).map(|l| l.6.clone())) {
        Some(r) => r,
        None => {
            let r = simplify_linear_uncached(egg, w, signed, trace, p);
            LAST.with(|c| *c.borrow_mut() = Some((egg.to_string(), w, signed, trace, p.clone(), vars, r.clone())));
            r
        }
    }
}

/// Rewrites of a rebuilt candidate that would break subterms the rebuild relates if done
/// earlier: recombined products, product factors with constants cut below trailing zeros,
/// and `shifted_xor`.
fn finish(t: &T, w: &Ctx) -> T {
    // Products selected by a bit are left whole for `split_bits` in the next round (Hikari).
    let t = if selectors(t, w).is_empty() { stats::pass("recombine", t, || recombine_regions(t, w, false)) } else { t.clone() };
    let t = stats::pass("cut_products", &t, || crate::lowbits::cut_products(&t, w));
    let t = stats::pass("shifted_xor", &t, || crate::lowbits::shifted_xor(&t, w));
    // Rebuilds can leave bits known by evaluation only (`-(A & B) & 1` with `A & B` even).
    let low = stats::pass("simplify_rebuilt", &t, || crate::lowbits::simplify_rebuilt(&t, w));
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

/// The pre-pass result and the forms to union with it: `Passes::prepass` on `egg`.
fn simplify_linear_uncached(egg: &str, w: u32, signed: Option<bool>, trace: bool, p: &Passes) -> (String, Vec<String>) {
    let env = crate::pipe::Env::prepass(p, w, signed, trace, egg);
    let input = crate::pipe::Cand::new(egg, "input");
    let mut out = crate::pipe::run(&p.prepass, vec![input], &env).expect("the pre-pass runs no egglog").into_iter().map(|c| c.term().to_string());
    let main = out.next().unwrap_or_else(|| egg.to_string());
    (main, out.collect())
}
