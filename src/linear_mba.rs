//! Linear MBA simplification (SiMBA-style). A linear MBA, i.e. a sum of
//! constant multiples of bitwise functions, is fully determined by its values
//! on {0,1}^n, so it can be rebuilt from those values in a minimal form.
//! Subterms that are not linear (`x*y`, `x >> 3`, ...) are treated as opaque
//! variables; the identity holds for any value they take. Bitwise operations
//! with constant operands (`x & 0xff`) make the region semi-linear: each bit
//! position then has its own bitwise function, see `semi_linear`.

use crate::eval::{Op, Term as T, parse, show, size};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

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
    pub(crate) fn signed(&self, v: u64) -> i64 {
        let sh = 64 - self.w;
        ((v << sh) as i64) >> sh
    }
}

type Memo<K, V> = std::sync::Mutex<std::collections::HashMap<K, (V, bool)>>;
type RebuiltKey = (Vec<u64>, Vec<(usize, bool)>, u64, u32);
type GroupedKey = (Vec<(Vec<u64>, u64)>, Vec<T>, u64, u32);

struct State {
    simba_memo: Memo<(u32, usize, T), Option<T>>,
    rewritten: Memo<(u32, T), T>,
    related: Memo<(u32, usize, usize, T), T>,
    rebuilt: std::sync::Mutex<std::collections::HashMap<RebuiltKey, (Vec<(u64, T)>, u64)>>,
    grouped: std::sync::Mutex<std::collections::HashMap<GroupedKey, T>>,
    /// Most leaves of a region `relate_region` tries.
    relate_leaves: AtomicUsize,
    /// `rewrite` calls left before it returns its input unchanged.
    rewrites_left: AtomicUsize,
    /// Most leaves a semi-linear region may have to be rebuilt.
    semi_leaves: AtomicUsize,
    bit_splits: AtomicUsize,
    clustering: std::sync::Mutex<Vec<T>>,
    /// Turns `clustered` off, for the rebuild without it.
    no_cluster: AtomicBool,
    /// Whether a form from `clustered` was kept since the last reset.
    clustered: AtomicBool,
}

impl Default for State {
    fn default() -> State {
        State {
            simba_memo: Default::default(),
            rewritten: Default::default(),
            related: Default::default(),
            rebuilt: Default::default(),
            grouped: Default::default(),
            relate_leaves: AtomicUsize::new(MAX_WIDE_LEAVES),
            rewrites_left: AtomicUsize::new(usize::MAX),
            semi_leaves: AtomicUsize::new(MAX_LEAVES),
            bit_splits: AtomicUsize::new(BIT_SPLIT_BUDGET),
            clustering: Default::default(),
            no_cluster: AtomicBool::new(false),
            clustered: AtomicBool::new(false),
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

pub(crate) fn eval(t: &T, w: &Ctx, leaf_vals: &[(T, u64)]) -> u64 {
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
    Bin(fn(u64, u64) -> u64, usize, usize),
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
                    let f: fn(u64, u64) -> u64 = match op {
                        Op::Add => u64::wrapping_add,
                        Op::Sub => u64::wrapping_sub,
                        Op::Mul => u64::wrapping_mul,
                        Op::And => |x, y| x & y,
                        Op::Or => |x, y| x | y,
                        Op::Xor => |x, y| x ^ y,
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
                Ins::Bin(f, x, y) => f(v[x], v[y]),
            };
            v.push(r & w.mask);
        }
        v[v.len() - 1]
    }

    /// Value with leaf `i` set to bit `i` of `p`.
    pub(crate) fn at(&self, p: usize, w: &Ctx) -> u64 {
        self.run(|i| (p >> i & 1) as u64, w)
    }
}

#[derive(Clone)]
enum B {
    V(usize),
    Not(Box<B>),
    Bin(Op, Box<B>, Box<B>),
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
                    for (op, tt) in [(Op::And, ta & tb), (Op::Or, ta | tb), (Op::Xor, ta ^ tb)] {
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
        B::Bin(op, x, y) => B::Bin(*op, Box::new(remap(x, vars)), Box::new(remap(y, vars))),
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
            (BE::Zero, BE::E(c, e)) => (c + 2, bin(Op::And, x, e)),
            (BE::E(c, e), BE::Zero) => (c + 3, bin(Op::And, not(x), e)),
            (BE::Ones, BE::E(c, e)) => (c + 3, bin(Op::Or, not(x), e)),
            (BE::E(c, e), BE::Ones) => (c + 2, bin(Op::Or, x, e)),
            (BE::E(c, e), _) if f0 == f1 => (c, e),
            (BE::E(c, e), _) if f1 == !f0 & sub_full => (c + 2, bin(Op::Xor, x, e)),
            (BE::E(c0, e0), BE::E(c1, e1)) => {
                let mux = (c0 + c1 + 6, bin(Op::Or, bin(Op::And, x.clone(), e1), bin(Op::And, not(x.clone()), e0.clone())));
                match bool_expr(f0 ^ f1, &rest) {
                    BE::E(cd, d) if c0 + cd + 3 < mux.0 => (c0 + cd + 3, bin(Op::Xor, e0, bin(Op::And, x, d))),
                    _ => mux,
                }
            }
            (BE::Zero, BE::Zero) | (BE::Ones, BE::Ones) => unreachable!("tt is not constant"),
        };
        if best.as_ref().is_none_or(|(c, _)| cand.0 < *c) {
            best = Some(cand);
        }
    }
    let split = if n <= MAX_DECOMPOSE { decompose(tt, n) } else { None };
    if let Some(cand) = split.filter(|d| best.as_ref().is_none_or(|(c, _)| d.0 < *c)) {
        best = Some(cand);
    }
    let (c, b) = best.unwrap();
    BE::E(c, b)
}

/// Most variables `bool_expr` tries `decompose` on; its cost grows with the pairs of
/// subsets (`decompose_regions` goes to 6 on the final result).
const MAX_DECOMPOSE: usize = 5;

/// Smallest `g(A) op h(B)` with `A ∪ B` all variables and both proper subsets, as in
/// `((w ^ x) | (x & y)) & ~(y ^ z)`. For `&`, `g` and `h` are `tt` ORed over the
/// variables outside their set; for `|`, ANDed; for `^`, `g = tt(B \ A = 0)` and
/// `h = tt(A \ B = 0) ^ tt(A \ B = 0, B \ A = 0)`. Each is checked against `tt`.
fn decompose(tt: u64, n: usize) -> Option<(usize, B)> {
    let full_vars = (1usize << n) - 1;
    let full = table_full(n);
    // Table with variable `i` forced to `v`, still over all `n` variables.
    let fix = |t: u64, i: usize, v: usize| {
        let low = [0x5555_5555_5555_5555u64, 0x3333_3333_3333_3333, 0x0f0f_0f0f_0f0f_0f0f, 0x00ff_00ff_00ff_00ff, 0x0000_ffff_0000_ffff, 0x0000_0000_ffff_ffff][i];
        let half = (if v == 0 { t } else { t >> (1 << i) }) & low & full;
        half | half << (1 << i)
    };
    let over = |t: u64, keep: usize, f: &dyn Fn(u64, u64) -> u64| {
        (0..n).filter(|&i| keep >> i & 1 == 0).fold(t, |t, i| f(fix(t, i, 0), fix(t, i, 1)))
    };
    let zero_out = |t: u64, keep: usize| (0..n).filter(|&i| keep >> i & 1 == 0).fold(t, |t, i| fix(t, i, 0));
    let sub = |t: u64, keep: usize| -> Option<(usize, B)> {
        let vars: Vec<usize> = (0..n).filter(|&i| keep >> i & 1 == 1).collect();
        let st = (0..1usize << vars.len())
            .filter(|&q| t >> vars.iter().enumerate().fold(0, |p, (j, &i)| p | (q >> j & 1) << i) & 1 == 1)
            .fold(0u64, |a, q| a | 1 << q);
        match bool_expr(st, &vars) {
            BE::E(c, b) => Some((c, b)),
            _ => None,
        }
    };
    let mut best: Option<(usize, B)> = None;
    for a in 1..full_vars {
        for b in a..full_vars {
            if a | b != full_vars {
                continue;
            }
            let pairs = [
                (Op::And, over(tt, a, &|x, y| x | y), over(tt, b, &|x, y| x | y)),
                (Op::Or, over(tt, a, &|x, y| x & y), over(tt, b, &|x, y| x & y)),
                (Op::Xor, zero_out(tt, a), zero_out(tt, b) ^ zero_out(tt, a & b)),
            ];
            for (op, g, h) in pairs {
                let joined = match op {
                    Op::And => g & h,
                    Op::Or => g | h,
                    _ => g ^ h,
                } & full;
                if joined != tt {
                    continue;
                }
                let (Some((cg, eg)), Some((ch, eh))) = (sub(g, a), sub(h, b)) else { continue };
                if best.as_ref().is_none_or(|(c, _)| cg + ch + 1 < *c) {
                    best = Some((cg + ch + 1, B::Bin(op, Box::new(eg), Box::new(eh))));
                }
            }
        }
    }
    best
}

fn b_to_t(b: &B, leaves: &[T]) -> T {
    match b {
        B::V(i) => leaves[*i].clone(),
        B::Not(x) => T::Op(Op::Not, vec![b_to_t(x, leaves)]),
        B::Bin(op, x, y) => T::Op(*op, vec![b_to_t(x, leaves), b_to_t(y, leaves)]),
    }
}

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

/// `simba` memoized per thread, for the linear cofactors `poly_mba` rebuilds: the same
/// ones come back across its factoring choices and across regions.
pub(crate) fn simba_memo(t: &T, w: &Ctx) -> Option<T> {
    let key = (w.w, w.st.semi_leaves.load(Relaxed), t.clone());
    if let Some(r) = memo_get(&w.st.simba_memo, &key, w) {
        return r;
    }
    let (r, used) = tracking_clusters(w, || simba(t, w));
    w.st.simba_memo.lock().unwrap().insert(key, (r.clone(), used));
    r
}

/// Smallest rebuilt form of the linear region `t`, if it has 1..=MAX_LEAVES leaves.
pub(crate) fn simba(t: &T, w: &Ctx) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let n = lv.len();
    if n > MAX_LEAVES {
        return match (drop_unused(t, &lv, w), clustered(t, w)) {
            (Some(d), Some(c)) if size(&c) >= size(&d) => Some(d),
            (d, None) => d,
            (_, c) => {
                w.st.clustered.store(true, Relaxed);
                c
            }
        };
    }
    if n == 0 {
        return None;
    }
    let rebuilt = if has_const_bitwise(t, w) {
        semi_linear(t, &lv, w)?
    } else {
        let prog = Prog::new(t, &lv, w);
        let vals: Vec<u64> = (0..1usize << n).map(|p| prog.at(p, w)).collect();
        let rebuilt = rebuild_values(&vals, &lv, w);
        let rebuilt = match common_multiple(&vals, &lv, w) {
            Some(r) if size(&r) < size(&rebuilt) => r,
            _ => rebuilt,
        };
        match related_leaves(t, &lv, w) {
            Some(r) if size(&r) < size(&rebuilt) => r,
            _ => rebuilt,
        }
    };
    Some(rebuilt).filter(|b| size(b) < size(t))
}


/// `c·(v_1 + ... + v_k) + L` for leaves whose own coefficients are within 1 of `c = ±2^k`
/// (a shifted sum), `L` rebuilt from the rest (`8*(y + z) + ((z ^ x) - x)` for `8*y + 9*z - 2*(z & x)`).
fn common_multiple(vals: &[u64], lv: &[T], w: &Ctx) -> Option<T> {
    let n = lv.len();
    let a: Vec<u64> = (0..n).map(|i| vals[1 << i].wrapping_sub(vals[0]) & w.mask).collect();
    let near = |x: u64, c: u64| w.signed(x.wrapping_sub(c) & w.mask).unsigned_abs() <= 1;
    let mut tried = Vec::new();
    let mut best: Option<T> = None;
    for c in a.iter().flat_map(|&x| [x, x.wrapping_add(1), x.wrapping_sub(1)].map(|c| c & w.mask)) {
        if w.signed(c).unsigned_abs() < MIN_COMMON || !w.signed(c).unsigned_abs().is_power_of_two() || tried.contains(&c) || tried.len() == MAX_COMMON_TRIES {
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

/// Smallest `|c|` `common_multiple` pulls out, and how many `c` it tries.
const MIN_COMMON: u64 = 4;
const MAX_COMMON_TRIES: usize = 2;

/// Most leaves `drop_unused` evaluates a region on.
const MAX_WIDE_LEAVES: usize = 16;
/// Most instructions times points `drop_unused` runs.
const WIDE_BUDGET: usize = 1 << 25;

/// A region with more than `MAX_LEAVES` leaves, rewritten with the leaves its values on
/// {0,1}^n do not depend on set to 0, as in opaque predicates over many variables.
fn drop_unused(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
    if has_const_bitwise(t, w) {
        return None;
    }
    drop_leaves(t, lv, w)
}

/// `drop_unused` for any region; with constant masks only where `relate` has cancelled leaves,
/// since elsewhere the rebuilds of the operands do better.
fn drop_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
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
fn used_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<(u64, Vec<bool>)> {
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
    let column = |j: u32| ks.iter().map(|k| k >> j & 1 == 1).collect::<Vec<_>>();
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
    let used = (0..n).map(|i| tables.iter().any(|g| (0..g.len()).any(|q| g[q] != g[q & !(1 << i)]))).collect();
    Some((e0, used))
}

/// The linear MBA over `lv` with values `vals` on {0,1}^n. When every value is a
/// multiple of `2^k`, `±2^k·L` with `L` rebuilt from `±vals / 2^k` is also tried, as in
/// `2*x - 4*(x & y) = 2*((x ^ y) - y)`; `L` only matters modulo `2^(w-k)`.
fn rebuild_values(vals: &[u64], lv: &[T], w: &Ctx) -> T {
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
fn small_blocks(t: &T, w: &Ctx) -> Option<T> {
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
            let conj = (0..n).filter(|i| q >> i & 1 == 1).map(|i| ph[i].clone()).reduce(|a, b| T::Op(Op::And, vec![a, b])).unwrap();
            terms.push((c, conj));
        }
        build_sum(&terms, konst, w)
    };
    let mut choice = vec![0usize; blocks.len()];
    let mut best = build(&choice);
    let mut best_size = wsize(&best);
    // Blocks that share leaves can need to change together (`2*~(a|c) + 2*(e & (c|d))`),
    // so few enough combinations are all tried; otherwise coordinate descent.
    let combos = opts.iter().try_fold(1usize, |acc, o| acc.checked_mul(o.len())).unwrap_or(usize::MAX);
    if combos <= MAX_BLOCK_COMBOS {
        let mut c = vec![0usize; blocks.len()];
        'all: loop {
            let cand = build(&c);
            let cs = wsize(&cand);
            if cs < best_size {
                (best, best_size) = (cand, cs);
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
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill(x, ph, lv)).collect()),
        }
    }
    (best_size < size(t)).then(|| fill(&best, &ph, &lv))
}

/// An arithmetic leaf `L` that is itself a linear MBA `ℓ` of other leaves (`a - d`,
/// `(b ^ d) - b`) is treated as independent, but `L - ℓ = 0`, so the region can
/// add `μ·(L - ℓ)` for any `μ`: in `(P & ~b) - (Q & (b | P)) + (b ^ d)` with
/// `Q = (b ^ d) - b`, `μ = 1` removes `d` and leaves `b | P | Q`. Tries up to two
/// such leaves with small `μ`.
fn related_leaves(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
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
pub(crate) fn relate(t: &T, w: &Ctx) -> T {
    if !matches!(t, T::Op(..)) {
        return t.clone();
    }
    // The scheduler relates many forms of one term, which share most regions.
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

/// `relate_leaves` in the rebuild without `clustered`, where wider regions take seconds.
const UNCLUSTERED_RELATE_LEAVES: usize = 10;
/// Most `rewrite` calls the rebuild without `clustered` makes; past them it is dropped.
const UNCLUSTERED_REWRITES: usize = 256;
/// Most `rewrite` calls of the other rebuilds after which the one without `clustered` is
/// still tried: inputs that need more are slow to rebuild without it.
const UNCLUSTERED_AFTER: usize = 1024;

/// Most arithmetic leaves `relate_region` tries.
const MAX_RELATED: usize = 4;
/// Largest product leaf `relate_region` tries when it is not an operand of a bitwise operation.
const MAX_FREE_PRODUCT: usize = 20;

fn relate_region(t: &T, w: &Ctx) -> Option<T> {
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
    let arith: Vec<usize> = (0..lv.len())
        .filter(|&i| matches!(&lv[i], T::Op(..)) && kind(&lv[i], w) != Kind::Bit && (operands.contains(&lv[i]) || size(&lv[i]) <= MAX_FREE_PRODUCT) && (0..lv.len()).any(|j| j != i && vars[j].iter().any(|v| vars[i].contains(v))))
        .take(MAX_RELATED)
        .collect();
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
    let mut tried: Vec<(Option<usize>, Option<usize>, Vec<(usize, i64)>, T)> = Vec::new();
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
        if by_used.is_some() || by_monos.is_some() {
            tried.push((by_used, by_monos, combo, s));
        }
    }
    let low_used = tried.iter().filter_map(|c| c.0).min();
    let low_monos = tried.iter().filter_map(|c| c.1).min();
    if low_used.is_none() && low_monos.is_none() {
        return None;
    }
    let mut best: Option<T> = None;
    for (_, _, combo, s) in tried.into_iter().filter(|c| (c.0.is_some() && c.0 == low_used) || (c.1.is_some() && c.1 == low_monos)) {
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
        // In a wide region only results where leaves cancelled: others shift extraction for little gain.
        if (!wide || fewer) && best.as_ref().is_none_or(|b| size(&r) < size(b)) {
            best = Some(r);
        }
    }
    best
}

/// Whether `t` is 0 at a few fixed points, a quick check before a proof.
fn maybe_zero(t: &T, w: &Ctx) -> bool {
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

/// Whether the linear region `t` has a bitwise operation with a constant operand.
fn has_const_bitwise(t: &T, w: &Ctx) -> bool {
    match (t, kind(t, w)) {
        (_, Kind::ConstBit) => true,
        (T::Op(_, a), Kind::Lin) => a.iter().any(|x| has_const_bitwise(x, w)),
        _ => false,
    }
}

/// Shortest `(terms, konst')` with `konst + Σ_j 2^j gp(bit j of x) = Σ terms + konst'`,
/// where `gp(0) = 0` and table point `p` sets leaf `i` to bit `i` of `p`.
fn rebuild_gp(gp: &[u64], lv: &[T], mut konst: u64, w: &Ctx) -> (Vec<(u64, T)>, u64) {
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
fn semi_linear(t: &T, lv: &[T], w: &Ctx) -> Option<T> {
    if lv.len() > w.st.semi_leaves.load(Relaxed) {
        return None;
    }
    let m = w.mask;
    let pts = 1usize << lv.len();
    let base: Vec<u64> = {
        let prog = Prog::new(t, lv, w);
        (0..w.w).flat_map(|j| (0..pts).map(move |q| (j, q))).map(|(j, q)| prog.run(|i| ((q >> i & 1) as u64) << j, w)).collect()
    };
    let (e0, all_groups) = groups_from(&|j, q| base[j as usize * pts + q], lv.len(), w)?;
    // Leaves that cancel out are dropped, so the shape search sees fewer leaves.
    let used: Vec<usize> = (0..lv.len())
        .filter(|&i| all_groups.iter().any(|(g, _)| (0..g.len()).any(|q| g[q] != g[q & !(1 << i)])))
        .collect();
    if used.is_empty() {
        return Some(T::Num(w.signed(e0)));
    }
    let project = |gs: Vec<(Vec<u64>, u64)>| -> Vec<(Vec<u64>, u64)> {
        let at = |q: usize| used.iter().enumerate().fold(0, |p, (j, &i)| p | (q >> j & 1) << i);
        gs.into_iter().map(|(g, mask)| ((0..1usize << used.len()).map(|q| g[at(q)]).collect(), mask)).collect()
    };
    let groups = project(all_groups);
    let full_lv = lv;
    let real: Vec<&T> = used.iter().map(|&i| &full_lv[i]).collect();
    let arith = real.iter().any(|l| kind(l, w) == Kind::Lin);
    // The search only needs each leaf's size, so it runs on slots: cheap to copy,
    // and the memoized searches repeat across regions with other leaves.
    let lv: &[T] = &real.iter().enumerate().map(|(i, l)| T::Op(Op::Slot(i as u32, size(l) as u32), Vec::new())).collect::<Vec<_>>();
    let mut cands = Vec::new();
    semi_linear_candidates(&groups, lv, e0, w, &mut cands);
    let mut peels = Vec::new();
    let mut best: Option<((u64, u64), usize)> = None;
    for i in 0..lv.len() {
        for a in [1i64, -1, 2, -2, 3, -3] {
            let peeled = |j: u32, q: usize| base[j as usize * pts + q].wrapping_sub((a as u64).wrapping_mul(((q >> used[i] & 1) as u64) << j)) & m;
            let Some((e0, gs)) = groups_from(&peeled, full_lv.len(), w) else { continue };
            let gs = project(gs);
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
    // Leaves can be large, so each candidate's size is taken once.
    let (mut sized, mut limit) = (0, size(t));
    let mut smallest = |cands: &[T]| {
        limit = cands[sized..].iter().map(size).fold(limit, usize::min);
        sized = cands.len();
        limit
    };
    shape_candidates(&groups, lv, e0, w, smallest(&cands), &mut cands);
    pair_candidates(&groups, lv, e0, w, smallest(&cands), &mut cands);
    for (i, a, e0, gs) in &peels {
        let limit = smallest(&cands);
        let extra = size(&add(T::Num(1), *i, *a)) - 1;
        if limit > extra {
            let mut sub = Vec::new();
            shape_candidates(gs, lv, *e0, w, limit - extra, &mut sub);
            cands.extend(sub.into_iter().map(|c| add(c, *i, *a)));
        }
    }
    cands.extend(semi_split(&groups, lv, e0, w, smallest(&cands)));
    cands.extend(scaled(&groups, lv, e0, w, smallest(&cands)));
    cands.extend(bit_split(&groups, lv, arith, e0, w, smallest(&cands)));
    // Masks that differ only in bits that cannot matter tie on size; keep the short one.
    let best = cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))?;
    Some(fill_slots(&short_consts(best, lv, w), &real))
}

fn fill_slots(t: &T, lv: &[&T]) -> T {
    match t {
        T::Op(Op::Slot(i, _), _) => lv[*i as usize].clone(),
        T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill_slots(x, lv)).collect()),
        _ => t.clone(),
    }
}

/// Most leaf splits `bit_split` rebuilds per region.
const MAX_BIT_SPLITS: usize = 4;
/// Most `P op Q` pairs `bit_split` rebuilds per `simplify_linear` call.
const BIT_SPLIT_BUDGET: usize = 8;

/// A purely bitwise semi-linear region of 4 to 6 leaves as `P op Q`, `P` over the
/// leaves `A` and `Q` over `B` (they may share leaves, neither holds the other),
/// each rebuilt on its own: `(x0 ^ x3 ^ K1) & (x3 | K2 | (x5 & x6))`. Bits are grouped
/// by their Boolean function `f`; `P` and `Q` take its projections onto `A` and `B`
/// (`f(x & !onlyB)` and the rest for `^`), and bits with a constant `f` try each
/// pair of constants that gives it.
fn bit_split(groups: &[(Vec<u64>, u64)], lv: &[T], arith: bool, e0: u64, w: &Ctx, mut limit: usize) -> Vec<T> {
    let n = lv.len();
    // Arithmetic leaves are left to `relate`, which needs the rebuilt region's shape.
    if !(4..=6).contains(&n) || w.st.bit_splits.load(Relaxed) == 0 || arith {
        return Vec::new();
    }
    let pts = 1usize << n;
    let all = if pts == 64 { u64::MAX } else { (1u64 << pts) - 1 };
    let mut funcs: Vec<(u64, u64)> = Vec::new();
    for (g, mask) in groups {
        for b in [0u64, 1] {
            let sub = mask & if b == 1 { e0 } else { !e0 } & w.mask;
            if sub == 0 {
                continue;
            }
            let rest = w.w - sub.trailing_zeros();
            let rm = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
            let mut table = 0u64;
            for (q, &v) in g.iter().enumerate() {
                let f = b.wrapping_add(v) & 1;
                if (f.wrapping_sub(b) ^ v) & rm != 0 {
                    return Vec::new();
                }
                table |= f << q;
            }
            match funcs.iter_mut().find(|(_, t)| *t == table) {
                Some(e) => e.0 |= sub,
                None => funcs.push((sub, table)),
            }
        }
    }
    let at = |t: u64, p: usize| t >> p & 1;
    // Points with leaf `i` set, as a table.
    let ones: Vec<u64> = (0..n).map(|i| (0..pts).filter(|p| p >> i & 1 == 1).fold(0, |m, p| m | 1 << p)).collect();
    let over = |mut t: u64, free: usize, any: bool| -> u64 {
        for i in (0..n).filter(|i| free >> i & 1 == 1) {
            let (hi, lo) = (t & ones[i], t & !ones[i] & all);
            let (up, down) = (lo << (1 << i), hi >> (1 << i));
            t = if any { t | up | down } else { (hi & up) | (lo & down) };
        }
        t
    };
    let zeroed = |mut t: u64, free: usize| -> u64 {
        for i in (0..n).filter(|i| free >> i & 1 == 1) {
            let lo = t & !ones[i] & all;
            t = lo | lo << (1 << i);
        }
        t
    };
    let split = |op: Op, t: u64, a: usize, b: usize| -> Option<(u64, u64)> {
        let (only_a, only_b) = (a & !b, b & !a);
        let (p, q) = match op {
            Op::And => (over(t, only_b, true), over(t, only_a, true)),
            Op::Or => (over(t, only_b, false), over(t, only_a, false)),
            _ => {
                let p = zeroed(t, only_b);
                (p, t ^ p)
            }
        };
        let ok = match op {
            Op::And => p & q == t,
            Op::Or => p | q == t,
            _ => zeroed(q, only_a) == q,
        };
        ok.then_some((p, q))
    };
    let const_pairs = |op: Op, f: u64| -> Vec<(u64, u64)> {
        match (op, f) {
            (Op::And, 0) => vec![(0, 0), (0, 1), (1, 0)],
            (Op::And, _) => vec![(1, 1)],
            (Op::Or, 0) => vec![(0, 0)],
            (Op::Or, _) => vec![(1, 1), (1, 0), (0, 1)],
            (_, 0) => vec![(0, 0), (1, 1)],
            _ => vec![(1, 0), (0, 1)],
        }
    };
    let full = pts - 1;
    // Variants 0-2 give constant bits each constant pair; 3 and 4 leave the side that
    // does not decide such bits (`q` in `1 | q`) the table of the widest other bits.
    let pick = |op: Op, a: usize, b: usize, v: usize| -> Option<(Vec<(u64, u64)>, Vec<(u64, u64)>)> {
        let mut split_all = Vec::new();
        for &(_, t) in &funcs {
            split_all.push(if t == 0 || t == all { None } else { Some(split(op, t, a, b)?) });
        }
        let widest = funcs.iter().zip(&split_all).filter_map(|((m, _), s)| s.map(|s| (m.count_ones(), s))).max_by_key(|x| x.0).map(|x| x.1);
        let (mut ps, mut qs, mut fresh) = (Vec::new(), Vec::new(), v == 0);
        for (&(mask, t), s) in funcs.iter().zip(&split_all) {
            let (p, q) = match s {
                Some(pq) => *pq,
                None => {
                    let pairs = const_pairs(op, t & 1);
                    let forced = pairs.len() == 3;
                    let (p, q) = match (v, widest) {
                        (0..3, _) => {
                            fresh |= v < pairs.len();
                            let (p, q) = pairs[v.min(pairs.len() - 1)];
                            (p * all, q * all)
                        }
                        (3, Some((_, wq))) if forced => {
                            fresh = true;
                            (pairs[1].0 * all, wq)
                        }
                        (4, Some((wp, _))) if forced => {
                            fresh = true;
                            (wp, pairs[2].1 * all)
                        }
                        _ => (pairs[0].0 * all, pairs[0].1 * all),
                    };
                    (p, q)
                }
            };
            let joined = match op {
                Op::And => p & q,
                Op::Or => p | q,
                _ => p ^ q,
            };
            if joined != t {
                return None;
            }
            ps.push((mask, p));
            qs.push((mask, q));
        }
        fresh.then_some((ps, qs))
    };
    let support = |parts: &[(u64, u64)]| -> u32 {
        let dep = (0..n).filter(|&i| parts.iter().any(|&(_, t)| (0..pts).any(|p| at(t, p) != at(t, p ^ 1 << i)))).count();
        let mut tables: Vec<u64> = parts.iter().map(|&(_, t)| t).filter(|&t| t != 0 && t != all).collect();
        tables.sort_unstable();
        tables.dedup();
        dep as u32 + tables.len() as u32
    };
    let mut found: Vec<(u32, Op, usize, usize, Vec<(u64, u64)>, Vec<(u64, u64)>)> = Vec::new();
    for code in 0..3usize.pow(n as u32) {
        let (mut a, mut b, mut c) = (0usize, 0usize, code);
        for i in 0..n {
            match c % 3 {
                0 => a |= 1 << i,
                1 => b |= 1 << i,
                _ => {
                    a |= 1 << i;
                    b |= 1 << i;
                }
            }
            c /= 3;
        }
        if a == full || b == full || a > b {
            continue;
        }
        for op in [Op::And, Op::Or, Op::Xor] {
            if let Some((ps, qs)) = pick(op, a, b, 0)
                && !found.iter().any(|f| f.1 == op && f.4 == ps && f.5 == qs)
            {
                found.push((support(&ps) + support(&qs), op, a, b, ps, qs));
            }
        }
    }
    found.sort_by_key(|f| f.0);
    let side = |parts: &[(u64, u64)], vars: usize| -> T {
        let terms: Vec<T> = parts
            .iter()
            .filter(|&&(_, t)| t != 0)
            .map(|&(mask, t)| {
                let k = T::Num(w.signed(mask));
                if t == all {
                    return k;
                }
                let minterms = (0..pts).filter(|&p| p & !vars == 0 && at(t, p) == 1).map(|p| {
                    (0..n)
                        .filter(|i| vars >> i & 1 == 1)
                        .map(|i| if p >> i & 1 == 1 { lv[i].clone() } else { T::Op(Op::Not, vec![lv[i].clone()]) })
                        .reduce(|x, y| T::Op(Op::And, vec![x, y]))
                        .unwrap()
                });
                T::Op(Op::And, vec![k, minterms.reduce(|x, y| T::Op(Op::Or, vec![x, y])).unwrap()])
            })
            .collect();
        terms.into_iter().reduce(|x, y| T::Op(Op::Or, vec![x, y])).unwrap_or(T::Num(0))
    };
    let mut out = Vec::new();
    // Each side has a leaf per leaf it depends on and a mask per table, so most
    // splits are ruled out by size before they are rebuilt.
    for &(low, op, a, b, ..) in found.iter().take(MAX_BIT_SPLITS) {
        for (ps, qs) in (0..5).filter_map(|v| pick(op, a, b, v)) {
            if low as usize + 1 >= limit || take_one(&w.st.bit_splits) == 0 {
                return out;
            }
            let t = T::Op(op, vec![rewrite(&side(&ps, a), w), rewrite(&side(&qs, b), w)]);
            limit = limit.min(size(&t));
            out.push(t);
        }
    }
    out
}

/// When `e0` and every table value are multiples of `2^k`, the region is `2^k·L`.
/// `L` only matters modulo `2^(w-k)`, so it is rebuilt in that width, where bit
/// `j` has the table `g_j / 2^k` and bits `j ≥ w-k` are free:
/// `(-((z | y) | (x & 0xff00)) - z) << 5`.
fn scaled(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let low_bits = |r: u32| if r == 64 { u64::MAX } else { (1u64 << r) - 1 };
    let mut k = if e0 == 0 { w.w } else { e0.trailing_zeros() };
    for (g, mask) in groups {
        let rest = low_bits(w.w - mask.trailing_zeros());
        k = g.iter().filter(|&&v| v & rest != 0).fold(k, |k, &v| k.min((v & rest).trailing_zeros()));
    }
    if k == 0 || k >= w.w || limit <= 3 {
        return None;
    }
    let nw = w.narrow(w.w - k);
    let gs: Vec<(Vec<u64>, u64)> = groups
        .iter()
        .filter(|(_, mask)| mask.trailing_zeros() < nw.w)
        .map(|(g, mask)| (g.iter().map(|&v| (w.signed(v) >> k) as u64 & nw.mask).collect(), mask & nw.mask))
        .collect();
    if gs.is_empty() {
        return None;
    }
    let e0 = e0 >> k;
    let mut cands = Vec::new();
    semi_linear_candidates(&gs, lv, e0, &nw, &mut cands);
    let inner = limit - 2;
    let limit = cands.iter().map(size).min().unwrap_or(inner).min(inner);
    shape_candidates(&gs, lv, e0, &nw, limit, &mut cands);
    let limit = cands.iter().map(size).min().unwrap_or(limit);
    cands.extend(semi_split(&gs, lv, e0, &nw, limit));
    let best = cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))?;
    Some(T::Op(Op::Mul, vec![T::Num(w.signed(1 << k)), short_consts(best, lv, &nw)]))
}

/// `t` with each constant replaced by the shortest sign- or zero-extension of its
/// low bits that leaves the function unchanged (`-0x7fffffffffffff6e` → `0x92`):
/// semi-linear terms are equal exactly when `e(0)` and every bit's table agree.
fn short_consts(t: T, lv: &[T], w: &Ctx) -> T {
    // `Prog` finds leaves by their context, which a rebuilt term may change, so
    // the leaves are replaced by placeholder variables first.
    let ph: Vec<T> = (0..lv.len()).map(|i| T::Var(format!("\u{4}{i}"))).collect();
    fn hide(t: &T, lv: &[T], ph: &[T]) -> T {
        if let Some(i) = lv.iter().position(|l| l == t) {
            return ph[i].clone();
        }
        match t {
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| hide(x, lv, ph)).collect()),
            _ => t.clone(),
        }
    }
    // Placeholders as the only variables, and no arithmetic under a bitwise operation.
    fn only_ph(t: &T, in_bit: bool) -> bool {
        match t {
            T::Var(v) => v.starts_with('\u{4}'),
            T::Num(_) => true,
            T::Op(op, a) => {
                let bit = matches!(op, Op::And | Op::Or | Op::Xor | Op::Not);
                (bit || !in_bit) && a.iter().all(|x| only_ph(x, bit))
            }
        }
    }
    fn show_leaves(t: &T, lv: &[T]) -> T {
        match t {
            T::Var(v) if v.starts_with('\u{4}') => lv[v[1..].parse::<usize>().unwrap()].clone(),
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| show_leaves(x, lv)).collect()),
            _ => t.clone(),
        }
    }
    let hidden = hide(&t, lv, &ph);
    if !only_ph(&hidden, false) {
        return t;
    }
    let Some(r) = short_consts_over(hidden, &ph, w) else { return t };
    show_leaves(&r, lv)
}

fn short_consts_over(t: T, lv: &[T], w: &Ctx) -> Option<T> {
    let reference = bit_groups(&t, lv, w)?;
    // Equal tables mean equal functions, so values at a few points rule out most
    // candidates before their tables are computed.
    let probe = |t: &T| {
        let prog = Prog::new(t, lv, w);
        [0x9e37_79b9_7f4a_7c15u64, 0x6a09_e667_f3bc_c909].map(|s| prog.run(|i| s.wrapping_mul(2 * i as u64 + 1).rotate_left(i as u32 * 7), w) & w.mask)
    };
    let at_probes = probe(&t);
    let same = |cand: &T| probe(cand) == at_probes && bit_groups(cand, lv, w).as_ref() == Some(&reference);
    let mut t = t;
    let count = {
        fn n(t: &T) -> usize {
            match t {
                T::Num(_) => 1,
                T::Op(_, a) => a.iter().map(n).sum(),
                _ => 0,
            }
        }
        n(&t)
    };
    fn replace(t: &T, idx: &mut usize, target: usize, v: i64) -> T {
        match t {
            T::Num(_) => {
                *idx += 1;
                if *idx - 1 == target { T::Num(v) } else { t.clone() }
            }
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| replace(x, idx, target, v)).collect()),
            _ => t.clone(),
        }
    }
    fn nth(t: &T, idx: &mut usize, target: usize) -> Option<i64> {
        match t {
            T::Num(v) => {
                *idx += 1;
                (*idx - 1 == target).then_some(*v)
            }
            T::Op(_, a) => a.iter().find_map(|x| nth(x, idx, target)),
            _ => None,
        }
    }
    let large = |k: i64| w.signed(k as u64 & w.mask).unsigned_abs() >> (w.w / 2) != 0;
    // Bits that cancel between constants (`(w ^ K) - (z ^ K')` with the top bit in
    // both) only go away together, so first all large constants are cut at once.
    for b in 0..w.w {
        let low = if b + 1 >= 64 { u64::MAX } else { (1u64 << (b + 1)) - 1 };
        fn cut(t: &T, f: &dyn Fn(i64) -> i64) -> T {
            match t {
                T::Num(v) => T::Num(f(*v)),
                T::Op(op, a) => T::Op(*op, a.iter().map(|x| cut(x, f)).collect()),
                _ => t.clone(),
            }
        }
        let f = |v: i64| {
            let k = v as u64 & w.mask;
            if !large(v) {
                return v;
            }
            let sign = if k >> b & 1 == 1 { !low } else { 0 };
            w.signed((k & low | sign) & w.mask)
        };
        let cand = cut(&t, &f);
        if cand != t && same(&cand) {
            t = cand;
            break;
        }
    }
    for i in 0..count {
        let Some(k) = nth(&t, &mut 0, i) else { continue };
        if !large(k) {
            continue;
        }
        let k = k as u64 & w.mask;
        let mut options: Vec<i64> = (0..w.w)
            .flat_map(|b| {
                let low = if b + 1 >= 64 { u64::MAX } else { (1u64 << (b + 1)) - 1 };
                let sign = if k >> b & 1 == 1 { !low } else { 0 };
                [w.signed((k & low | sign) & w.mask), w.signed(k & low)]
            })
            .filter(|&v| v != w.signed(k))
            .collect();
        options.sort_by_key(|v| v.unsigned_abs());
        options.dedup();
        for v in options.into_iter().filter(|v| v.unsigned_abs() < w.signed(k).unsigned_abs()) {
            let cand = replace(&t, &mut 0, i, v);
            if same(&cand) {
                t = cand;
                break;
            }
        }
    }
    Some(t)
}

/// Smallest of the grouped and shape candidates for a semi-linear table.
fn semi_from_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let mut cands = Vec::new();
    semi_linear_candidates(groups, lv, e0, w, &mut cands);
    let limit = cands.iter().map(size).min().unwrap_or(limit).min(limit);
    shape_candidates(groups, lv, e0, w, limit, &mut cands);
    cands.into_iter().min_by_key(|c| (size(c), const_bits(c)))
}

/// Leaves split into sets with no mixed difference in any bit's table, so each
/// table is the sum of its restrictions to the sets and each set is rebuilt on
/// its own: `(~w ^ 0x72) - 2*((v & 0x4bfa) | (x | 0xf))`. One set takes the rest of
/// `e(0)` so its shape can absorb it; each is tried in that role. The others take
/// either a constant their single term would have (`own_consts`) or the one their
/// own rebuild leaves.
fn semi_split(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize) -> Option<T> {
    let n = lv.len();
    let mut root: Vec<usize> = (0..n).collect();
    fn find(root: &mut [usize], i: usize) -> usize {
        if root[i] != i {
            root[i] = find(root, root[i]);
        }
        root[i]
    }
    for (g, mask) in groups {
        let rest = w.w - mask.trailing_zeros();
        let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
        for i in 0..n {
            for j in i + 1..n {
                let (bi, bj) = (1usize << i, 1usize << j);
                let joined = (0..1usize << n).filter(|p| p & (bi | bj) == 0).any(|p| g[p | bi | bj].wrapping_sub(g[p | bi]).wrapping_sub(g[p | bj]).wrapping_add(g[p]) & low != 0);
                if joined {
                    let (ri, rj) = (find(&mut root, i), find(&mut root, j));
                    root[ri] = rj;
                }
            }
        }
    }
    let mut sets: Vec<Vec<usize>> = Vec::new();
    for i in 0..n {
        let r = find(&mut root, i);
        match sets.iter_mut().find(|s| find(&mut root, s[0]) == r) {
            Some(s) => s.push(i),
            None => sets.push(vec![i]),
        }
    }
    if sets.len() < 2 {
        return None;
    }
    let restrict = |set: &[usize]| -> Vec<(Vec<u64>, u64)> {
        let at = |q: usize| set.iter().enumerate().fold(0, |p, (j, &i)| p | (q >> j & 1) << i);
        let mut out: Vec<(Vec<u64>, u64)> = Vec::new();
        for (g, mask) in groups {
            let h: Vec<u64> = (0..1usize << set.len()).map(|q| g[at(q)]).collect();
            match out.iter_mut().find(|(o, _)| *o == h) {
                Some(o) => o.1 |= mask,
                None => out.push((h, *mask)),
            }
        }
        out.sort_by_key(|(_, mask)| mask.trailing_zeros());
        out
    };
    let parts: Vec<(Vec<(Vec<u64>, u64)>, Vec<T>)> = sets.iter().map(|s| (restrict(s), s.iter().map(|&i| lv[i].clone()).collect())).collect();
    let free: Vec<Option<T>> = parts.iter().map(|(gs, sl)| semi_from_groups(gs, sl, 0, w, limit)).collect();
    let mut best: Option<T> = None;
    let mut keep = |cand: T| {
        if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
            best = Some(cand);
        }
    };
    let own: Vec<Vec<u64>> = parts.iter().map(|(gs, _)| own_consts(gs, w)).collect();
    let mut memo: std::collections::HashMap<(usize, u64), Option<T>> = Default::default();
    for last in 0..parts.len() {
        let others: Vec<usize> = (0..parts.len()).filter(|&k| k != last).collect();
        if others.iter().any(|&k| own[k].is_empty()) || others.iter().map(|&k| own[k].len()).product::<usize>() > 64 {
            continue;
        }
        let mut choice = vec![0usize; others.len()];
        'combos: loop {
            let mut terms = Vec::new();
            let mut target = e0;
            for (a, &k) in others.iter().enumerate() {
                let kc = own[k][choice[a]];
                target = target.wrapping_sub(kc) & w.mask;
                let (gs, sl) = &parts[k];
                match memo.entry((k, kc)).or_insert_with(|| semi_from_groups(gs, sl, kc, w, limit)) {
                    Some(t) => terms.push((1, t.clone())),
                    None => terms.clear(),
                }
            }
            let (gs, sl) = &parts[last];
            if terms.len() == others.len() {
                if let Some(t) = memo.entry((last, target)).or_insert_with(|| semi_from_groups(gs, sl, target, w, limit)) {
                    terms.push((1, t.clone()));
                    keep(build_sum(&terms, 0, w));
                }
            }
            let mut a = 0;
            loop {
                if a == choice.len() {
                    break 'combos;
                }
                choice[a] += 1;
                if choice[a] < own[others[a]].len() {
                    break;
                }
                choice[a] = 0;
                a += 1;
            }
        }
    }
    for last in 0..parts.len() {
        // The other sets either keep their own constant, or drop it and pass it to `last`.
        for strip in [false, true] {
            let mut terms = Vec::new();
            let mut target = e0;
            for (k, f) in free.iter().enumerate().filter(|&(k, _)| k != last) {
                let (body, k) = if strip { split_const(f.as_ref()?, &parts[k].1, w) } else { (f.clone()?, 0) };
                target = target.wrapping_add(k) & w.mask;
                terms.push((1, body));
            }
            let (gs, sl) = &parts[last];
            let Some(t) = semi_from_groups(gs, sl, target, w, limit) else { continue };
            terms.push((1, t));
            keep(build_sum(&terms, 0, w));
        }
    }
    best
}

/// Constants a set could absorb if it were one term `c·B`: bit `j` of `B(0)` is
/// set where bit `j`'s table takes `-c`, and bits with a zero table, or one that
/// is both `c` and `-c` in its width, may go either way; `-c·~B` gives the same
/// table with `c` more.
fn own_consts(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<u64> {
    let m = w.mask;
    let Some(c) = groups.iter().flat_map(|(g, _)| g.iter().copied()).find(|&v| v != 0) else { return Vec::new() };
    let neg_c = c.wrapping_neg() & m;
    let (mut n, mut f, mut amb) = (0u64, 0u64, 0u64);
    for (g, mask) in groups {
        let rest = w.w - mask.trailing_zeros();
        let low = if rest == 64 { u64::MAX } else { (1u64 << rest) - 1 };
        let is = |v: u64, x: u64| (v ^ x) & low == 0;
        let (pos, neg) = (g.iter().any(|&v| !is(v, 0) && is(v, c)), g.iter().any(|&v| !is(v, 0) && is(v, neg_c)));
        if g.iter().any(|&v| !is(v, 0) && !is(v, c) && !is(v, neg_c)) {
            return Vec::new();
        }
        match (pos, neg) {
            (_, false) if !g.iter().any(|&v| !is(v, 0)) => f |= mask,
            (true, true) => amb |= mask,
            (false, true) => n |= mask,
            _ => {}
        }
    }
    // At bits with `c ≡ -c` in their width the table cannot tell, whatever group
    // they joined.
    let hi = m & !((1u64 << (w.w - 1 - c.trailing_zeros().min(w.w - 1))) - 1);
    amb = (amb | hi) & !f;
    n &= !amb;
    let mut out: Vec<u64> = [n, n | f, n | amb, n | f | amb]
        .into_iter()
        .flat_map(|b| [c.wrapping_mul(b) & m, c.wrapping_mul(b).wrapping_add(c) & m])
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// `(x, k)` with `t = x + k` for a trailing constant `k` of `t`, else `(t, 0)`; a leaf
/// `t` is kept whole.
fn split_const(t: &T, lv: &[T], w: &Ctx) -> (T, u64) {
    match t {
        _ if lv.contains(t) => (t.clone(), 0),
        T::Op(op, a) if *op == Op::Add => match (&a[0], &a[1]) {
            (x, T::Num(k)) | (T::Num(k), x) => (x.clone(), *k as u64 & w.mask),
            _ => (t.clone(), 0),
        },
        T::Op(op, a) if *op == Op::Sub => match &a[1] {
            T::Num(k) => (a[0].clone(), (*k as u64).wrapping_neg() & w.mask),
            _ => (t.clone(), 0),
        },
        _ => (t.clone(), 0),
    }
}

/// Largest table value in magnitude, then the sum of each group's largest.
fn spread(groups: &[(Vec<u64>, u64)], w: &Ctx) -> (u64, u64) {
    let per_group = groups.iter().map(|(g, _)| g.iter().map(|&v| w.signed(v).unsigned_abs()).max().unwrap_or(0));
    (per_group.clone().max().unwrap_or(0), per_group.fold(0, u64::saturating_add))
}

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
fn shape_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, mut limit: usize, cands: &mut Vec<T>) {
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
fn pair_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, limit: usize, cands: &mut Vec<T>) {
    let n = lv.len();
    // One group is a linear table, which `overlapping_terms` covers.
    if !(1..=3).contains(&n) || !(2..=MAX_PAIR_GROUPS).contains(&groups.len()) {
        return;
    }
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
    // fits[acc2][s2]: the entries of size s2 that meet every group's acc2; many
    // shapes B1 and coefficient pairs give the same acc2.
    let mut fits: std::collections::HashMap<Vec<[u64; 4]>, Vec<Option<Vec<usize>>>> = Default::default();
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
            let mut zero_r: std::collections::HashMap<Vec<u8>, Option<bool>> = Default::default();
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
                        if !p1.iter().all(|p| meets(p, &sh.sets[i])) {
                            continue;
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
                        let row = fits.entry(acc2.clone()).or_default();
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
fn carry_layers(group_of: &[usize], options: &[Vec<(u8, u8)>], (c1, c2): (u64, u64), e0: u64, w: &Ctx) -> Result<Vec<std::collections::HashMap<i128, (i128, usize)>>, bool> {
    let bits = w.w as usize;
    let val = |o: (u8, u8)| (w.signed(c1) as i128) * (o.0 & 1) as i128 + (w.signed(c2) as i128) * (o.1 & 1) as i128;
    // layers[j]: carry into bit j -> (carry into bit j-1, option at bit j-1).
    let mut layers: Vec<std::collections::HashMap<i128, (i128, usize)>> = vec![std::collections::HashMap::from([(0, (0, 0))])];
    for j in 0..bits {
        let mut next = std::collections::HashMap::new();
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

/// `e(0)` and the bits of the semi-linear region `t` grouped by table, as
/// `(table, mask)`; `None` if `t` is not semi-linear.
fn bit_groups(t: &T, lv: &[T], w: &Ctx) -> Option<(u64, Vec<(Vec<u64>, u64)>)> {
    let prog = Prog::new(t, lv, w);
    groups_from(&|j, q| prog.run(|i| ((q >> i & 1) as u64) << j, w), lv.len(), w)
}

/// `bit_groups` from `at(j, q)`, the value with leaf `i` set to bit `j` of `q >> i & 1`.
fn groups_from(at: &dyn Fn(u32, usize) -> u64, n: usize, w: &Ctx) -> Option<(u64, Vec<(Vec<u64>, u64)>)> {
    let m = w.mask;
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

fn semi_linear_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
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
fn half_flips(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<Vec<(Vec<u64>, u64)>> {
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

/// The first smallest of `grouped_candidates_all`, memoized: callers only keep the first
/// smallest candidate, and semi-linear searches repeat the same groups.
fn grouped_candidates(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
    let key = (groups.to_vec(), lv.to_vec(), e0, w.w);
    let known = w.st.grouped.lock().unwrap().get(&key).cloned();
    if let Some(t) = known {
        cands.push(t);
        return;
    }
    let mut all = Vec::new();
    grouped_candidates_all(groups, lv, e0, w, &mut all);
    let Some(best) = all.into_iter().min_by_key(|c| (size(c), const_bits(c))) else { return };
    w.st.grouped.lock().unwrap().insert(key, best.clone());
    cands.push(best);
}

fn grouped_candidates_all(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
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
fn single_leaf(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx, cands: &mut Vec<T>) {
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
    // Bits where `c ≡ -c` in their width may count on either side.
    let hi = m & !((1u64 << (w.w - 1 - c.trailing_zeros().min(w.w - 1))) - 1) & (p | n);
    let sides = [(c, p, n), (neg_c, n, p)];
    for (c, p, n) in sides.into_iter().flat_map(|(c, p, n)| [(c, p, n), (c, p | hi, n & !hi), (c, p & !hi, n | hi)]) {
        let mask = p | n;
        let mut zs = vec![0, free];
        if let Some(h) = solve_mul(c, e0.wrapping_sub(c.wrapping_mul(n)) & m, w) {
            zs.extend([h, h & free]);
        }
        zs.sort_unstable();
        zs.dedup();
        for z in zs.into_iter().filter(|z| z & !free == 0) {
            let k = n | z;
            let mut inner = if mask == m { y.clone() } else { T::Op(Op::And, vec![y.clone(), T::Num(w.signed(mask))]) };
            if k != 0 {
                inner = T::Op(Op::Xor, vec![inner, T::Num(w.signed(k))]);
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
fn high_merges(groups: &[(Vec<u64>, u64)], w: &Ctx) -> Vec<Vec<(Vec<u64>, u64)>> {
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
fn masked_groups(groups: &[(Vec<u64>, u64)], lv: &[T], e0: u64, w: &Ctx) -> T {
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
            terms.push((c, T::Op(Op::And, vec![b, T::Num(w.signed(*mask))])));
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
fn const_leaf_groups(groups: &[(Vec<u64>, u64)], shifts: &[Vec<u64>], lv: &[T], e0: u64, w: &Ctx) -> Vec<T> {
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
fn solve_mul(mask: u64, e0: u64, w: &Ctx) -> Option<u64> {
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
fn fold_consts(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if !matches!(op, Op::And | Op::Or | Op::Xor | Op::Not | Op::Add | Op::Sub | Op::Neg) {
        return t.clone();
    }
    let a: Vec<T> = a.iter().map(|x| fold_consts(x, w)).collect();
    let t = T::Op(*op, a);
    match &t {
        T::Op(_, a) if a.iter().all(|x| matches!(x, T::Num(_))) => T::Num(w.signed(eval(&t, w, &[]))),
        _ => t,
    }
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
    let key = (gp.to_vec(), shape, konst, w.w);
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
    let all_vars: Vec<usize> = (0..n).collect();
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
        .min_by_key(|(ts, k)| sum_size(ts, *k, w))
        .unwrap()
}

/// Most distinct non-zero values for which `overlapping_terms` searches.
const OVERLAP_MAX_VALUES: usize = 4;

/// Up to 3 bitwise terms whose supports may overlap (`11*(x^y) - x`), possibly
/// non-zero at 0 (`-23*~(x|y)`). Shifting the table by `d` gives
/// `h = gp + d = Σ c_j·b_j` per bit, and then `e = Σ c_j·b_j(x) + konst + d`,
/// since a per-bit constant `d` is the word `-d`. `d` is tried as 0 or `-v`
/// for a value `v` of `gp`, i.e. `h` is zero where `gp` is `v`.
fn overlapping_terms(gp: &[u64], lv: &[T], konst: u64, w: &Ctx) -> Vec<(Vec<(u64, T)>, u64)> {
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
            // At k = 3 a repeated coefficient leaves ambiguous points (rejected) or two equal terms.
            for coefs in combinations(&pool, k, k == 2) {
                if let Some(c) = split_by_sums(&h, &hv, &coefs, &all_vars, lv, konst.wrapping_add(d) & m, w) {
                    out.push(c);
                }
            }
        }
    }
    out
}

/// The `k`-element multisets of `pool` (sets unless `repeat`), in pool order.
fn combinations(pool: &[u64], k: usize, repeat: bool) -> Vec<Vec<u64>> {
    if k == 0 {
        return vec![Vec::new()];
    }
    (0..pool.len())
        .flat_map(|i| {
            combinations(&pool[i + usize::from(!repeat)..], k - 1, repeat).into_iter().map(move |mut rest| {
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
fn split_by_sums(h: &[u64], h_vals: &[u64], coefs: &[u64], vars: &[usize], lv: &[T], konst: u64, w: &Ctx) -> Option<(Vec<(u64, T)>, u64)> {
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
        if best.as_ref().is_none_or(|(bt, bk)| sum_size(&terms, kk, w) < sum_size(bt, *bk, w)) {
            best = Some((terms, kk));
        }
    }
    best
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
pub(crate) fn recombine_regions(t: &T, w: &Ctx, in_lin: bool) -> T {
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
        let best = match (simba(t, w), small_blocks(t, w)) {
            (Some(s), Some(p)) => Some(if size(&p) < size(&s) { p } else { s }),
            (s, p) => s.or(p),
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
pub(crate) fn cluster_regions(t: &T, w: &Ctx, in_lin: bool) -> T {
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
            w.st.clustered.store(true, Relaxed);
            c
        }
        None => node,
    }
}

/// `f()`, and whether a form from `clustered` was kept during it (which then also counts
/// for the enclosing call).
fn tracking_clusters<R>(w: &Ctx, f: impl FnOnce() -> R) -> (R, bool) {
    let outer = w.st.clustered.swap(false, Relaxed);
    let r = f();
    let used = w.st.clustered.load(Relaxed);
    w.st.clustered.store(outer || used, Relaxed);
    (r, used)
}

/// A memoized result, unless it came from `clustered` while that is off.
fn memo_get<K: std::hash::Hash + Eq, V: Clone>(memo: &Memo<K, V>, key: &K, w: &Ctx) -> Option<V> {
    let (r, used) = memo.lock().unwrap().get(key).cloned()?;
    if used && w.st.no_cluster.load(Relaxed) {
        return None;
    }
    w.st.clustered.fetch_or(used, Relaxed);
    Some(r)
}

/// Most `clustered` calls nested inside each other.
const MAX_CLUSTER_DEPTH: usize = 2;

/// A region with more than `MAX_LEAVES` leaves rebuilt in parts: its terms grouped by the
/// leaves they use, a group whose leaves are a subset of another's joining the smallest
/// such, and each group of at most `MAX_LEAVES` leaves rewritten on its own, which is
/// exact since the parts add up to the region. Splits such as `7·(a & 0xffff) +
/// 7·(a & -0x10000)` and constants spread over the region then come together.
fn clustered(t: &T, w: &Ctx) -> Option<T> {
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
fn leaf_groups(terms: Vec<(u64, T)>, w: &Ctx) -> Vec<(Vec<u64>, Vec<(u64, T)>)> {
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

/// Most leaves of two groups together that `join_constant` rebuilds with the region's
/// constant (one group: `MAX_LEAVES`), and most such rebuilds per region.
const MAX_JOINED_LEAVES: usize = 3;
const MAX_JOINED_SETS: usize = 10;

/// `t` with the constant of each linear region rebuilt together with one leaf group, or two
/// groups of at most `MAX_JOINED_LEAVES` leaves, where that is smaller: the rebuild of a
/// whole region (or of its groups, `clustered`) keeps the constant apart, but
/// `3·((r | 0x7fffffff) ^ u)` is `-3·u + (r & 2^31) + 0x7ffffffd`, one term only when
/// rebuilt with its constant.
pub(crate) fn join_constants(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| join_constants(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    join_constant(&node, w).unwrap_or(node)
}

fn join_constant(t: &T, w: &Ctx) -> Option<T> {
    let (mut terms, mut konst) = region_terms(t, w);
    // Constants also hide in complemented terms: `c·~B` is `-c·B - c`.
    for (c, y) in terms.iter_mut() {
        if let T::Op(Op::Not, a) = y {
            konst = konst.wrapping_sub(*c) & w.mask;
            *c = c.wrapping_neg() & w.mask;
            *y = a[0].clone();
        }
    }
    if konst == 0 || terms.len() < 2 {
        return None;
    }
    let groups = leaf_groups(terms, w);
    let n = groups.len();
    let joined = |s: &[usize]| {
        let mut leaves: Vec<u64> = s.iter().flat_map(|&i| groups[i].0.clone()).collect();
        leaves.sort_unstable();
        leaves.dedup();
        leaves.len()
    };
    let mut sets: Vec<Vec<usize>> = (0..n).map(|i| vec![i]).chain((0..n).flat_map(|i| (i + 1..n).map(move |j| vec![i, j]))).collect();
    sets.retain(|s| joined(s) <= if s.len() == 1 { MAX_LEAVES } else { MAX_JOINED_LEAVES });
    // Each rebuild searches a semi-linear region with a constant, which is slow.
    sets.sort_by_key(|s| joined(s));
    sets.truncate(MAX_JOINED_SETS);
    let mut best = t.clone();
    for set in sets {
        let g: Vec<(u64, T)> = set.iter().flat_map(|&i| groups[i].1.clone()).collect();
        let others: Vec<(u64, T)> = (0..n).filter(|j| !set.contains(j)).flat_map(|j| groups[j].1.clone()).collect();
        let alt = T::Op(Op::Add, vec![build_sum(&others, 0, w), rewrite(&build_sum(&g, konst, w), w)]);
        if size(&alt) < size(&best) {
            best = alt;
        }
    }
    (best != *t).then_some(best)
}

/// Most leaf groups of a region `join_linear` moves leaves between: it rebuilds each
/// ordered pair for every shared leaf and multiple.
const MAX_MOVE_GROUPS: usize = 12;

/// `t` with each bitwise region of 6 leaves written as its smallest `g(A) op h(B)`
/// (`decompose`), where that is smaller; `bool_expr` only splits up to `MAX_DECOMPOSE`
/// variables, since over 6 it takes milliseconds per table:
/// `(((y·s) | (2·v)) ^ ((s ^ w) & (v + t))) | (u & w)`.
pub(crate) fn decompose_regions(t: &T, w: &Ctx, in_bit: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let bit = matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) && kind(t, w) == Kind::Bit;
    let node = T::Op(*op, a.iter().map(|x| decompose_regions(x, w, bit)).collect());
    if !bit || in_bit {
        return node;
    }
    let mut lv = Vec::new();
    leaves(&node, w, &mut lv);
    if lv.len() != 6 {
        return node;
    }
    let vars: Vec<T> = (0..6).map(|i| T::Var(format!("%d{i}"))).collect();
    let x = crate::lowbits::replace(&node, &lv, &vars);
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    let tt = (0..64usize).fold(0u64, |acc, p| {
        let env = |v: &str| if p >> v[2..].parse::<usize>().unwrap() & 1 == 1 { w.mask } else { 0 };
        acc | (crate::eval::eval(&x, ty, &env).unwrap_or(0) & 1) << p
    });
    let Some((_, b)) = decompose(tt, 6) else { return node };
    let r = b_to_t(&b, &lv);
    if size(&r) < size(&node) { r } else { node }
}

/// Multiples of a shared leaf `join_linear` moves between two leaf groups; 0 rebuilds the
/// two groups as they are.
const MOVED_MULTIPLES: [i64; 7] = [0, 1, -1, 2, -2, 3, -3];

/// `t` with each linear region's smallest rebuild after moving `a·v` from one leaf group to
/// another that also uses leaf `v` (and the region's constant into the first, or not): the
/// groups are rebuilt apart, and which group takes a shared leaf's linear part is not
/// known; `(s - (z & (y | s))) + z + (u ^ x ^ z)` is `((z & ~y) | s) + (u ^ x ^ z)`.
pub(crate) fn join_linear(t: &T, w: &Ctx, in_lin: bool) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let lin = kind(t, w) == Kind::Lin;
    let node = T::Op(*op, a.iter().map(|x| join_linear(x, w, lin)).collect());
    if !lin || in_lin {
        return node;
    }
    move_linear(&node, w).unwrap_or(node)
}

fn move_linear(t: &T, w: &Ctx) -> Option<T> {
    let (terms, konst) = region_terms(t, w);
    if terms.len() < 2 {
        return None;
    }
    let groups = leaf_groups(terms, w);
    let n = groups.len();
    if n > MAX_MOVE_GROUPS {
        return None;
    }
    let leaf_terms: Vec<Vec<T>> = groups
        .iter()
        .map(|(_, g)| {
            let mut lv = Vec::new();
            g.iter().for_each(|(_, x)| leaves(x, w, &mut lv));
            lv
        })
        .collect();
    let mut best = t.clone();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for v in leaf_terms[i].iter().filter(|v| leaf_terms[j].contains(v)) {
                for a in MOVED_MULTIPLES {
                    let a = a as u64 & w.mask;
                    let (mut gi, mut gj) = (groups[i].1.clone(), groups[j].1.clone());
                    if a != 0 {
                        gi.push((a, v.clone()));
                        gj.push((a.wrapping_neg() & w.mask, v.clone()));
                    }
                    let rj = rewrite(&build_sum(&gj, 0, w), w);
                    let others: Vec<(u64, T)> = (0..n).filter(|&k| k != i && k != j).flat_map(|k| groups[k].1.clone()).collect();
                    for with_konst in [false, true] {
                        let (k_in, k_out) = if with_konst { (konst, 0) } else { (0, konst) };
                        let ri = rewrite(&build_sum(&gi, k_in, w), w);
                        let mut all = others.clone();
                        all.extend([(1, ri), (1, rj.clone())]);
                        // A negative first term costs a `Neg`; later ones become `Sub`.
                        if let Some(p) = all.iter().position(|(c, _)| w.signed(*c) > 0) {
                            all[..=p].rotate_right(1);
                        }
                        let alt = build_sum(&all, k_out, w);
                        if size(&alt) < size(&best) {
                            best = alt;
                        }
                    }
                }
            }
        }
    }
    (best != *t).then_some(best)
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

/// `t` with each `p·(a >> s)` (`p = 2^s·q` as `split_low` builds it) and `(a >> s) << s'` (`s' ≥ s`) written
/// with `a & -2^s` (or `~(a | (2^s - 1))` under a `~`), so that the semi-linear
/// rebuild sees `a`: `7·(x & 0xffffffff) + 0x700000000·(x >> 32)` is `7·x`. Only for
/// `a` built of T-function operations, so `(mulhi(x, M) >> 1)·12` keeps the shape the
/// magic-number division rules match.
pub(crate) fn unshift(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| unshift(x, w)).collect();
    // `(a >> s) << s` for both shifts: the bits filled in by `>>` are shifted out.
    let low_cleared = |x: &T, k: u32| -> Option<(T, u32)> {
        let num = |v: u64| T::Num(w.signed(v & w.mask));
        let bin = |o: Op, p: T, q: T| T::Op(o, vec![p, q]);
        fn tfunc_ops(t: &T, w: &Ctx) -> bool {
            match t {
                T::Op(o, a) if *o == Op::Shl => const_shift(&a[1], w).is_some() && tfunc_ops(&a[0], w),
                T::Op(o, a) => matches!(o, Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Not | Op::And | Op::Or | Op::Xor) && a.iter().all(|x| tfunc_ops(x, w)),
                _ => true,
            }
        }
        match x {
            T::Op(o, b) if *o == Op::Shr && tfunc_ops(&b[0], w) => {
                let s = const_shift(&b[1], w).filter(|&s| s > 0 && s <= k)?;
                Some((bin(Op::And, b[0].clone(), num(u64::MAX << s)), s))
            }
            T::Op(o, b) if *o == Op::Not => match &b[0] {
                T::Op(o, c) if *o == Op::Shr && tfunc_ops(&c[0], w) => {
                    let s = const_shift(&c[1], w).filter(|&s| s > 0 && s <= k)?;
                    let or = bin(Op::Or, c[0].clone(), num((1u64 << s) - 1));
                    Some((T::Op(Op::Not, vec![or]), s))
                }
                _ => None,
            },
            _ => None,
        }
    };
    match (op, &a[..]) {
        (Op::Mul, [T::Num(c), x]) | (Op::Mul, [x, T::Num(c)]) if *c as u64 & w.mask != 0 => {
            if let Some((y, s)) = low_cleared(x, (*c as u64 & w.mask).trailing_zeros()) {
                return T::Op(Op::Mul, vec![T::Num(w.signed(*c as u64 & w.mask) >> s), y]);
            }
        }
        (Op::Mul, [x, p]) | (Op::Mul, [p, x]) if low_cleared(x, w.w).is_some() => {
            let (y, s) = low_cleared(x, w.w).unwrap();
            if let Some((q, 0)) = split_low(p, s, w) {
                return T::Op(Op::Mul, vec![y, q]);
            }
        }
        (Op::Shl, [x, k]) => {
            if let Some((y, s)) = const_shift(k, w).and_then(|k| low_cleared(x, k)) {
                let k = const_shift(k, w).unwrap() - s;
                return if k == 0 { y } else { T::Op(Op::Shl, vec![y, T::Num(k as i64)]) };
            }
        }
        _ => {}
    }
    T::Op(*op, a)
}

/// `(a, c)` with `t = 2^k·a + c` and `0 ≤ c < 2^k`, if `t` is built so.
fn split_low(t: &T, k: u32, w: &Ctx) -> Option<(T, u64)> {
    let lk = (1u64 << k) - 1;
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    let num = |v: u64| T::Num(w.signed(v & w.mask));
    let scaled = |c: i64, e: &T| -> Option<(T, u64)> {
        let c = c as u64 & w.mask;
        if c == 0 || c.trailing_zeros() < k {
            return None;
        }
        let c = w.signed(c) >> k;
        Some((if c == 1 { e.clone() } else { op(Op::Mul, vec![T::Num(c), e.clone()]) }, 0))
    };
    match t {
        T::Num(v) => Some((T::Num(w.signed(*v as u64 & w.mask) >> k), *v as u64 & lk)),
        T::Op(o, a) => match (o, &a[..]) {
            (Op::Mul, [T::Num(c), e]) | (Op::Mul, [e, T::Num(c)]) => scaled(*c, e),
            (Op::Mul, [x, y]) => match (split_low(x, k, w), split_low(y, k, w)) {
                (Some((p, 0)), _) => Some((op(Op::Mul, vec![p, y.clone()]), 0)),
                (_, Some((q, 0))) => Some((op(Op::Mul, vec![x.clone(), q]), 0)),
                _ => None,
            },
            (Op::Shl, [x, s]) => {
                let s = const_shift(s, w).filter(|&s| s >= k)?;
                Some((if s == k { x.clone() } else { op(Op::Shl, vec![x.clone(), T::Num((s - k) as i64)]) }, 0))
            }
            (Op::Neg, [x]) => match split_low(x, k, w)? {
                (p, 0) => Some((op(Op::Neg, vec![p]), 0)),
                (p, c) => Some((op(Op::Not, vec![p]), (1 << k) - c)),
            },
            (Op::Not, [x]) => split_low(x, k, w).map(|(p, c)| (op(Op::Not, vec![p]), lk - c)),
            (o @ (Op::Add | Op::Sub), [x, y]) => {
                let ((p, c), (q, d)) = (split_low(x, k, w)?, split_low(y, k, w)?);
                let (v, carry) = if *o == Op::Add { (c + d, c + d > lk) } else { (c.wrapping_sub(d), c < d) };
                let s = op(*o, vec![p, q]);
                let s = match (carry, o) {
                    (false, _) => s,
                    (true, Op::Add) => op(Op::Add, vec![s, num(1)]),
                    _ => op(Op::Sub, vec![s, num(1)]),
                };
                Some((s, v & lk))
            }
            (o @ (Op::And | Op::Or | Op::Xor), [x, y]) => {
                let ((p, c), (q, d)) = (split_low(x, k, w)?, split_low(y, k, w)?);
                let v = match o {
                    Op::And => c & d,
                    Op::Or => c | d,
                    _ => c ^ d,
                };
                Some((op(*o, vec![p, q]), v))
            }
            _ => None,
        },
        _ => None,
    }
}

/// `t` with the constants its low `r` bits depend on sign-extended from bit `r - 1`.
pub(crate) fn low_consts(t: &T, r: u32) -> T {
    match t {
        T::Num(v) => T::Num(v << (64 - r) >> (64 - r)),
        T::Op(op, a) if *op == Op::Shl => T::Op(*op, vec![low_consts(&a[0], r), a[1].clone()]),
        T::Op(op, a) if matches!(op, Op::Add | Op::Sub | Op::Mul | Op::And | Op::Or | Op::Xor | Op::Not | Op::Neg) => {
            T::Op(*op, a.iter().map(|x| low_consts(x, r)).collect())
        }
        _ => t.clone(),
    }
}

/// `t` with each bitwise operation whose operands are `2^k·a + c` (`c < 2^k`)
/// written as `2^k·(a op b) + (c op d)`, for the largest such `k`: a bitwise
/// operation only sees the bits of `a` that `2^k·a` keeps, so the rebuild can
/// treat `x - ((2·x) | ~(2·K)) - K - 1` as the semi-linear `x - 2·(x | ~K) - K - 2`,
/// which is `x ^ K`.
pub(crate) fn halve(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| halve(x, w)).collect();
    let node = T::Op(*op, a);
    let T::Op(_, a) = &node else { unreachable!() };
    if !matches!(op, Op::And | Op::Or | Op::Xor) || a.iter().all(|x| matches!(x, T::Num(_))) {
        return node;
    }
    let mut best = None;
    for k in 1..w.w {
        match split_low(&node, k, w) {
            Some(s) => best = Some((k, s)),
            None => break,
        }
    }
    let Some((k, (T::Op(op, a), c))) = best else { return node };
    // Only the low `w - k` bits of the operands matter, so their constants are cut
    // to that width, once the rebuild has merged them: `(2^63 + 1)·y` becomes `y`.
    let inner = T::Op(op, a.iter().map(|x| low_consts(&rewrite(x, w), w.w - k)).collect());
    let scaled = T::Op(Op::Mul, vec![T::Num(w.signed(1 << k)), inner]);
    if c == 0 { scaled } else { T::Op(Op::Add, vec![scaled, T::Num(c as i64)]) }
}

/// Rebuilds of at most this size are not searched further: the input is not halved, and
/// the driver does not saturate the input beside them.
pub const TINY: usize = 3;

/// Most variable bits `split_bits` tries on one term, how deep it nests, and the
/// largest first rebuild it runs on.
const MAX_SPLITS: usize = 4;
const SPLIT_DEPTH: usize = 2;
const MAX_SPLIT_SIZE: usize = 64;
/// Most rebuilds one `split_bits` call runs.
const SPLIT_RUNS: usize = 16;

/// `(s, k)` for a product factor with one or two bits not known, `k` the lowest of them:
/// first the subterm `s` it is built from with constants alone, as `z + x` in
/// `3 & ((z + x) + 5)`, then each variable `s` of it.
fn split_points(t: &T, w: &Ctx) -> Vec<(T, u32)> {
    fn is_const(t: &T) -> bool {
        match t {
            T::Var(_) => false,
            T::Num(_) => true,
            T::Op(_, a) => a.iter().all(is_const),
        }
    }
    fn core(t: &T) -> &T {
        match t {
            T::Op(_, a) if a.iter().filter(|x| !is_const(x)).count() == 1 => core(a.iter().find(|x| !is_const(x)).unwrap()),
            _ => t,
        }
    }
    fn go(t: &T, w: &Ctx, out: &mut Vec<(T, u32)>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) {
            for f in a {
                let g = match f {
                    T::Op(Op::Neg, b) => &b[0],
                    _ => f,
                };
                let bits = crate::lowbits::unknown_bits(g, w);
                if bits != 0 && bits.count_ones() <= 2 {
                    let k = bits.trailing_zeros();
                    let s = core(f);
                    let vars = crate::eval::vars(f).into_iter().map(T::Var);
                    for s in std::iter::once(s.clone()).filter(|s| matches!(s, T::Op(..))).chain(vars) {
                        if !out.contains(&(s.clone(), k)) {
                            out.push((s, k));
                        }
                    }
                }
            }
        }
        a.iter().for_each(|x| go(x, w, out));
    }
    let mut out = Vec::new();
    go(t, w, &mut out);
    out
}

/// `(v, k)` for each variable `v` of a product factor that is 0 or `2^k` by known bits.
pub(crate) fn selectors(t: &T, w: &Ctx) -> Vec<(String, u32)> {
    fn go(t: &T, w: &Ctx, out: &mut Vec<(String, u32)>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) {
            for f in a {
                let bits = crate::lowbits::possible_bits(f, w);
                if bits.is_power_of_two() {
                    for v in crate::eval::vars(f) {
                        if !out.contains(&(v.clone(), bits.trailing_zeros())) {
                            out.push((v, bits.trailing_zeros()));
                        }
                    }
                }
            }
        }
        a.iter().for_each(|x| go(x, w, out));
    }
    let mut out = Vec::new();
    go(t, w, &mut out);
    out
}

/// `t` rebuilt by cases on bit `k` of a variable `v` that selects a product, as in
/// `(1 & ~y)*(-y & -2) + (-y | 1)*(y & 1)`, which is `-y`: with `r0` and `r1` the
/// rebuilds of `t` with that bit cleared and set, `t = r0 + ((v >> k) & 1)*(r1 - r0)`.
/// A subterm `s` is split as a variable `v` that replaces it, which holds for any `v`
/// and so for `v = s`. The halves are split again, up to `depth` times.
/// Returns `t` when nothing smaller without selecting products is found or `budget`
/// (rebuilds left) runs out.
fn split_bits(t: T, depth: usize, budget: &std::cell::Cell<usize>, w: &Ctx, run: &dyn Fn(&T) -> T) -> T {
    if depth == 0 {
        return t;
    }
    let run = |t: &T| {
        budget.set(budget.get().saturating_sub(1));
        run(t)
    };
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    for (s, k) in split_points(&t, w).into_iter().take(MAX_SPLITS) {
        if budget.get() < 3 {
            break;
        }
        let (var, ts) = match s {
            T::Var(_) => (s.clone(), t.clone()),
            _ => {
                let v = T::Var(format!("\u{3}{depth}"));
                let ts = crate::lowbits::replace(&t, std::slice::from_ref(&s), std::slice::from_ref(&v));
                (v, ts)
            }
        };
        let m = 1u64 << k;
        let half = |b: T| split_bits(run(&crate::lowbits::replace(&ts, std::slice::from_ref(&var), &[b])), depth - 1, budget, w, &run);
        let r0 = half(op(Op::And, vec![var.clone(), T::Num(w.signed(!m & w.mask))]));
        if !selectors(&r0, w).is_empty() {
            continue;
        }
        let r1 = half(op(Op::Or, vec![var.clone(), T::Num(w.signed(m))]));
        if !selectors(&r1, w).is_empty() {
            continue;
        }
        let d = run(&op(Op::Sub, vec![r1, r0.clone()]));
        let ty = crate::eval::NumType { bits: w.w, signed: false };
        let c = Some(()).filter(|_| crate::eval::vars(&d).is_empty()).and_then(|_| crate::eval::eval(&d, ty, &|_| 0));
        let sel = match c {
            Some(c) if c & (m - 1) == 0 => op(Op::Mul, vec![op(Op::And, vec![var.clone(), T::Num(w.signed(m))]), T::Num(w.signed(c >> k))]),
            _ if k == 0 => op(Op::Mul, vec![op(Op::And, vec![var.clone(), T::Num(1)]), d]),
            _ => op(Op::Mul, vec![op(Op::And, vec![op(Op::Shr, vec![var.clone(), T::Num(k as i64)]), T::Num(1)]), d]),
        };
        let mut r = run(&op(Op::Add, vec![r0, sel]));
        if var != s {
            r = run(&crate::lowbits::replace(&r, std::slice::from_ref(&var), std::slice::from_ref(&s)));
        }
        if size(&r) < size(&t) && selectors(&r, w).is_empty() {
            return r;
        }
    }
    t
}

/// `split_in` with the rebuild the first rebuild of `simplify_linear` uses, for terms of at
/// most `MAX_SPLIT_SIZE` nodes.
pub(crate) fn split_rebuilt(t: &T, w: &Ctx) -> T {
    if size(t) > MAX_SPLIT_SIZE {
        return t.clone();
    }
    split_in(t, w, &|t| rebuild_once(t, w))
}

/// Candidates of `simplify_linear_uncached` rebuilt with subterms abstracted to variables,
/// kept only when at most 3/4 the size of the first rebuild.
const ABSTRACTED: [&str; 2] = ["over_const_bitwise", "over_shared_bitwise"];

/// The rebuild `simplify_linear` applies to its input, without `relate`.
pub(crate) fn rebuild_once(t: &T, w: &Ctx) -> T {
    let t = unshift(&crate::lowbits::simplify(t, w), w);
    crate::tfunc::replacement(&t, w).unwrap_or_else(|| crate::tfunc::simplify(&cluster_regions(&rewrite(&t, w), w, false), w))
}

/// `rebuild_once` with each bitwise operation of a term and a constant (`y ^ 0xdeadbeef`)
/// first replaced by a fresh variable: a region whose constants all sit in such subterms
/// becomes linear, `(z & (u ^ ((K & p) ^ ~w))) + 2·(z & p & ~(u ^ w) & K)` is
/// `(z & ~(u ^ w)) + (z & p & K)`.
pub(crate) fn over_const_bitwise(t: &T, w: &Ctx) -> T {
    over_subterms(t, w, &|x| match x {
        T::Op(Op::And | Op::Or | Op::Xor, a) => a.iter().any(|y| matches!(y, T::Num(_))) && !a.iter().all(|y| matches!(y, T::Num(_))),
        _ => false,
    })
}

/// `rebuild_once` with each bitwise subterm of at least 3 nodes that occurs more than once
/// first replaced by a fresh variable: the region then has fewer leaves, and a table over
/// few leaves rebuilds exactly, `6·(t & u & A & B) - 3·(A ^ (t & ~(B & u)))` is
/// `3·((t & u & B) - (t ^ A))` with `A = y ^ (u + w)`, `B = y ^ w`.
pub(crate) fn over_shared_bitwise(t: &T, w: &Ctx) -> T {
    fn count(t: &T, seen: &mut std::collections::HashMap<T, usize>) {
        let T::Op(op, a) = t else { return };
        if matches!(op, Op::And | Op::Or | Op::Xor) && size(t) >= 3 {
            let n = seen.entry(t.clone()).or_insert(0);
            *n += 1;
            if *n > 1 {
                return;
            }
        }
        a.iter().for_each(|x| count(x, seen));
    }
    let mut seen = std::collections::HashMap::new();
    count(t, &mut seen);
    over_subterms(t, w, &|x| seen.get(x).is_some_and(|&n| n > 1))
}

/// `rebuild_once` with the outermost subterms that `pick` selects replaced by fresh
/// variables, which are put back after; kept when smaller. The identity found holds for
/// every value of the variables, so for the subterms too.
fn over_subterms(t: &T, w: &Ctx, pick: &dyn Fn(&T) -> bool) -> T {
    fn go(t: &T, pick: &dyn Fn(&T) -> bool, found: &mut Vec<T>) -> T {
        if pick(t) {
            let i = found.iter().position(|f| f == t).unwrap_or_else(|| {
                found.push(t.clone());
                found.len() - 1
            });
            return T::Var(format!("%k{i}"));
        }
        let T::Op(op, a) = t else { return t.clone() };
        T::Op(*op, a.iter().map(|x| go(x, pick, found)).collect())
    }
    let mut found = Vec::new();
    let a = go(t, pick, &mut found);
    if found.is_empty() {
        return t.clone();
    }
    let r = rebuild_once(&a, w);
    if r == a {
        return t.clone();
    }
    let vars: Vec<T> = (0..found.len()).map(|i| T::Var(format!("%k{i}"))).collect();
    let back = crate::lowbits::replace(&r, &vars, &found);
    if size(&back) < size(t) { back } else { t.clone() }
}

/// Most variable shift amounts `shift_cases` splits on, nested.
const SHIFT_CASE_DEPTH: usize = 2;

/// `t` rebuilt by cases of a variable shift amount `s` of `a << s`, when smaller and equal
/// to `t` in every case (the rebuild of their difference is 0). The candidates are the
/// rebuild with each such shift a fresh `2^K·v` (`K` = 1, 2), checked for `s = k < K`; for
/// `s = (b & (w-1))` or `~b`, also the rebuild of case `s = k` with `b` put back, checked
/// for every `k`. Case `k` sets the low bits of each `b` there, so other uses of `b` see
/// them: `(A | (~c & ((A << (c & 63)) & 1))) + y` is `A + y`.
pub(crate) fn shift_cases(t: &T, w: &Ctx) -> T {
    if size(t) > MAX_SHIFT_CASE_SIZE {
        return t.clone();
    }
    shift_cases_in(t, w, SHIFT_CASE_DEPTH)
}

/// Largest term `shift_cases` runs on: it rebuilds up to `2w` cases per amount.
const MAX_SHIFT_CASE_SIZE: usize = 64;

fn shift_cases_in(t: &T, w: &Ctx, depth: usize) -> T {
    fn amounts(t: &T, out: &mut Vec<T>) {
        let T::Op(op, a) = t else { return };
        if *op == Op::Shl && !matches!(a[1], T::Num(_)) && !out.contains(&a[1]) {
            out.push(a[1].clone());
        }
        a.iter().for_each(|x| amounts(x, out));
    }
    fn wide(t: &T, s: &T, k: u32, tag: &str, fresh: &mut Vec<T>) -> T {
        let T::Op(op, a) = t else { return t.clone() };
        if *op == Op::Shl && a[1] == *s {
            let i = fresh.iter().position(|f| *f == a[0]).unwrap_or_else(|| {
                fresh.push(a[0].clone());
                fresh.len() - 1
            });
            return T::Op(Op::Mul, vec![T::Num(1 << k), T::Var(format!("{tag}{i}"))]);
        }
        T::Op(*op, a.iter().map(|x| wide(x, s, k, tag, fresh)).collect())
    }
    let rebuild = |x: &T| if depth > 1 { shift_cases_in(&rebuild_once(x, w), w, depth - 1) } else { rebuild_once(x, w) };
    let m = (w.w - 1) as i64;
    let tag = format!("%s{depth}_");
    let mut found = Vec::new();
    amounts(t, &mut found);
    let mut best = t.clone();
    for s in found.iter().take(2) {
        let var = match s {
            T::Op(Op::And, a) if a.contains(&T::Num(m)) => match a.iter().find(|x| **x != T::Num(m)) {
                Some(T::Op(Op::Not, b)) => Some((b[0].clone(), true)),
                Some(b) => Some((b.clone(), false)),
                None => None,
            },
            _ => None,
        };
        let set = |k: i64| {
            let (b, not) = var.as_ref().unwrap();
            let low = if *not { m - k } else { k };
            (b.clone(), T::Op(Op::Or, vec![T::Op(Op::And, vec![b.clone(), T::Num(!m)]), T::Num(low)]))
        };
        let case = |x: &T, k: i64| match &var {
            Some(_) => {
                let (v, e) = set(k);
                crate::lowbits::replace(x, &[v], &[e])
            }
            None => crate::lowbits::replace(x, std::slice::from_ref(s), &[T::Num(k)]),
        };
        let holds = |r: &T, k: i64| fold_consts(&rebuild_once(&T::Op(Op::Sub, vec![case(t, k), case(r, k)]), w), w) == T::Num(0);
        let mut tried = Vec::new();
        let mut candidates: Vec<(T, i64)> = Vec::new();
        for k in 1..=2u32 {
            let r = rebuild(&wide(t, s, k, &tag, &mut Vec::new()));
            if !has_var_prefix(&r, &tag) {
                candidates.push((r, k as i64));
            }
        }
        if var.is_some() {
            for k in [0, 1, m] {
                let (v, e) = set(k);
                let e2 = rebuild_once(&e, w);
                let r = crate::lowbits::replace(&rebuild(&case(t, k)), &[e, e2], &[v.clone(), v]);
                candidates.push((r, m + 1));
            }
        }
        for (r, cases) in candidates {
            if size(&r) >= size(&best) || tried.contains(&r) {
                continue;
            }
            tried.push(r.clone());
            if (0..cases).all(|k| holds(&r, k)) {
                best = r;
            }
        }
    }
    best
}

fn has_var_prefix(t: &T, p: &str) -> bool {
    match t {
        T::Var(v) => v.starts_with(p),
        T::Op(_, a) => a.iter().any(|x| has_var_prefix(x, p)),
        _ => false,
    }
}

/// `split_bits` on `t`, then on the operands of `t` when it is a bitwise operation, since
/// a case split rarely gives a constant difference through one; each with its own budget.
fn split_in(t: &T, w: &Ctx, run: &dyn Fn(&T) -> T) -> T {
    let s = split_bits(t.clone(), SPLIT_DEPTH, &std::cell::Cell::new(SPLIT_RUNS), w, run);
    if s != *t {
        return s;
    }
    match t {
        T::Op(op, a) if matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) => {
            let b: Vec<T> = a.iter().map(|x| if split_points(x, w).is_empty() { x.clone() } else { split_in(x, w, run) }).collect();
            if b == *a {
                return t.clone();
            }
            let r = run(&T::Op(*op, b));
            if size(&r) < size(t) { r } else { t.clone() }
        }
        _ => t.clone(),
    }
}

/// Largest final result `polish` runs `relate` on.
const MAX_POLISH_RELATE: usize = 128;
/// Uncached `rewrite` calls one `polish` call may make.
const POLISH_REWRITES: usize = 2000;

/// The egglog term `egg` with the passes below applied while one makes it smaller, and the
/// names of those that did. Run on the final result only: as a pre-pass candidate, even a
/// slightly smaller form changes how the rules finish.
pub fn polish(egg: &str, w: u32) -> (String, Vec<&'static str>) {
    type Pass = (&'static str, fn(&T, &Ctx) -> T);
    const PASSES: [Pass; 10] = [
        ("join_constants", |t, w| join_constants(t, w, false)),
        ("join_linear", |t, w| join_linear(t, w, false)),
        ("relate", |t, w| {
            if size(t) > MAX_POLISH_RELATE {
                return t.clone();
            }
            w.limit_semi_leaves(2);
            let r = relate(t, w);
            w.limit_semi_leaves(MAX_LEAVES);
            r
        }),
        ("over_const_bitwise", over_const_bitwise),
        ("over_shared_bitwise", over_shared_bitwise),
        ("over_products", |t, w| crate::lowbits::over_products(t, w, |a| rebuild_once(a, w))),
        ("recombine", |t, w| if selectors(t, w).is_empty() { recombine_regions(t, w, false) } else { t.clone() }),
        ("shift_cases", shift_cases),
        ("split_bits", split_rebuilt),
        ("decompose", |t, w| decompose_regions(t, w, false)),
    ];
    let w = Ctx::new(w);
    w.limit_rewrites(POLISH_REWRITES);
    let mut best = parse(egg);
    let mut used = Vec::new();
    loop {
        let before = used.len();
        for (name, run) in PASSES {
            let r = run(&best, &w);
            if size(&r) < size(&best) {
                best = r;
                used.push(name);
            }
        }
        if used.len() == before || used.len() >= 8 {
            break;
        }
    }
    if used.is_empty() { (egg.to_string(), used) } else { (show(&best), used) }
}

/// Rewrite the egglog term `egg` (W-bit wrapping semantics) with every linear
/// MBA region, and every polynomial MBA region,
/// rebuilt in a smaller form. Returns `egg` unchanged when nothing gets smaller.
pub fn simplify_linear(egg: &str, w: u32) -> String {
    simplify_linear_with(egg, w, &Default::default()).0
}

/// `simplify_linear`, and the other rebuilds worth unioning: the next smallest (`egg` and
/// its first rebuild are also rebuilt with bitwise operations of even operands halved,
/// `halve`, and which result the rules finish best is not known) and the first rebuild
/// without `clustered`, when that was used.
pub fn simplify_linear_both(egg: &str, w: u32) -> (String, Vec<String>) {
    simplify_linear_with(egg, w, &Default::default())
}

/// `simplify_linear_both` with the scheduler settings `opts`.
pub fn simplify_linear_with(egg: &str, w: u32, opts: &crate::sched::Options) -> (String, Vec<String>) {
    type Result = (String, Vec<String>, bool);
    type Last = Option<(String, u32, crate::sched::Options, Result)>;
    thread_local! {
        static LAST: std::cell::RefCell<Last> = const { std::cell::RefCell::new(None) };
    }
    let hit = |(e, bits, o, _): &&(String, u32, crate::sched::Options, Result)| e == egg && *bits == w && o == opts;
    let r = match LAST.with(|c| c.borrow().as_ref().filter(hit).map(|l| l.3.clone())) {
        Some(r) => r,
        None => {
            let r = simplify_linear_uncached(egg, w, opts);
            LAST.with(|c| *c.borrow_mut() = Some((egg.to_string(), w, opts.clone(), r.clone())));
            r
        }
    };
    if r.2 {
        crate::sched::mark_used();
    }
    (r.0, r.1)
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

/// `t` without additions of 0 and multiplications by 1.
fn drop_identities(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| drop_identities(x, w)).collect();
    let is = |x: &T, k: u64| matches!(x, T::Num(v) if *v as u64 & w.mask == k);
    match (op, a.as_slice()) {
        (Op::Add, [x, z]) | (Op::Add, [z, x]) | (Op::Sub, [x, z]) if is(z, 0) => x.clone(),
        (Op::Mul, [x, o]) | (Op::Mul, [o, x]) if is(o, 1) => x.clone(),
        _ => T::Op(*op, a),
    }
}

/// The legacy pre-pass result and the forms to union with it, and whether the scheduler
/// replaced the first one.
fn simplify_linear_uncached(egg: &str, w: u32, opts: &crate::sched::Options) -> (String, Vec<String>, bool) {
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
    let mut rebuilt: Vec<(&str, T)> = vec![("first", r.clone())];
    if size(&r) <= MAX_SPLIT_SIZE {
        let s = split_in(&r, &w, &|t| run(&unshift(&crate::lowbits::simplify(t, &w), &w), false));
        if s != r {
            rebuilt.push(("split_bits", s));
        }
    }
    let hr = halve(&r, &w);
    if hr != r {
        rebuilt.push(("halve_first", run(&hr, false)));
    }
    let pr = crate::lowbits::over_products(&r, &w, |t| rebuild_once(t, &w));
    if pr != r {
        rebuilt.push(("over_products", pr));
    }
    for (name, o) in [("over_const_bitwise", over_const_bitwise(&r, &w)), ("over_shared_bitwise", over_shared_bitwise(&r, &w))] {
        if o != r {
            rebuilt.push((name, o));
        }
    }
    // Halving the whole input can give semi-linear regions that are slow to search,
    // so only small ones are rebuilt there, also inside `halve`.
    w.st.semi_leaves.store(2, Relaxed);
    let ht = if size(&r) <= TINY { t.clone() } else { halve(&t, &w) };
    if ht != t {
        rebuilt.push(("halve_input", run(&ht, false)));
    }
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
    let unclustered = if w.st.clustered.load(Relaxed) && made <= UNCLUSTERED_AFTER && crate::tfunc::replacement(&t, &w).is_none() {
        w.st.bit_splits.store(BIT_SPLIT_BUDGET, Relaxed);
        w.st.no_cluster.store(true, Relaxed);
        w.st.relate_leaves.store(UNCLUSTERED_RELATE_LEAVES, Relaxed);
        w.st.rewrites_left.store(UNCLUSTERED_REWRITES, Relaxed);
        let within = || w.st.rewrites_left.load(Relaxed) > 0;
        let r = Some(rewrite(&t, &w)).filter(|_| within());
        let r = r.map(|r| relate(&r, &w)).filter(|_| within());
        let u = r.map(|r| drop_identities(&finish(&crate::tfunc::simplify(&r, &w), &w), &w));
        w.st.rewrites_left.store(usize::MAX, Relaxed);
        w.st.relate_leaves.store(MAX_WIDE_LEAVES, Relaxed);
        w.st.no_cluster.store(false, Relaxed);
        u
    } else {
        None
    };
    let seeds: Vec<T> = rebuilt.iter().map(|(_, t)| t).chain(&unclustered).cloned().collect();
    let scheduled = crate::sched::schedule(&t0, &seeds, &w, opts);
    if opts.trace {
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
    let used = scheduled.first().is_some_and(|b| size(b) < size(&rebuilt[0].1));
    if used {
        rebuilt.insert(0, ("sched", scheduled[0].clone()));
    }
    if opts.trace {
        let kept: Vec<String> = rebuilt.iter().map(|(n, t)| format!("{n} {}", size(t))).collect();
        eprintln!("prepass: chosen {}", kept.join(", then "));
    }
    let others: Vec<T> = rebuilt.split_off(1).into_iter().map(|(_, t)| t).collect();
    let r = rebuilt.swap_remove(0).1;
    let r = if r == t0 { egg.to_string() } else { show(&r) };
    (r, others.iter().map(show).collect(), used)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{NumType, eval};
    use std::collections::HashMap;

    fn full_eval(t: &T, w: &Ctx, env: &HashMap<String, u64>) -> u64 {
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
        random_term_in(r, depth, &VARS)
    }

    fn random_term_in(r: &mut Rng, depth: u32, vars: &[&str]) -> T {
        let var = |r: &mut Rng| T::Var(vars[(r.next() % vars.len() as u64) as usize].into());
        if depth == 0 {
            return match r.next() % 6 {
                0 => T::Num((r.next() % 7) as i64 - 3),
                _ => var(r),
            };
        }
        let sub = |r: &mut Rng| random_term_in(r, depth - 1, vars);
        match r.next() % 12 {
            0 => T::Op(Op::Not, vec![sub(r)]),
            1 => T::Op(Op::Neg, vec![sub(r)]),
            2 | 3 => T::Op(Op::Add, vec![sub(r), sub(r)]),
            4 => T::Op(Op::Sub, vec![sub(r), sub(r)]),
            5 => T::Op(Op::Mul, vec![T::Num((r.next() % 9) as i64 - 4), sub(r)]),
            6 => T::Op(Op::And, vec![sub(r), sub(r)]),
            7 => T::Op(Op::Or, vec![sub(r), sub(r)]),
            8 => T::Op(Op::Xor, vec![sub(r), sub(r)]),
            9 => T::Op(Op::Mul, vec![sub(r), sub(r)]),
            10 => T::Op(Op::Shl, vec![sub(r), T::Num((r.next() % 10) as i64)]),
            _ => T::Op(Op::Shr, vec![sub(r), T::Num((r.next() % 4) as i64)]),
        }
    }

    /// Terms with the shapes `unshift` and `halve` rewrite, over `x` and `y`.
    fn shifted_term(r: &mut Rng, depth: u32) -> T {
        let op = |o: Op, a: Vec<T>| T::Op(o, a);
        if depth == 0 {
            return match r.next() % 4 {
                0 => T::Num((r.next() % 9) as i64 - 4),
                1 => T::Var("x".into()),
                _ => T::Var("y".into()),
            };
        }
        let sub = |r: &mut Rng| shifted_term(r, depth - 1);
        let k = 1 + (r.next() % 3) as i64;
        let c = [1i64, -1, 3, -3, 5][(r.next() % 5) as usize];
        let even = |r: &mut Rng| match r.next() % 6 {
            0 => op(Op::Mul, vec![T::Num(c << k), sub(r)]),
            1 => op(Op::Add, vec![op(Op::Mul, vec![sub(r), T::Num(4)]), T::Num((r.next() % 4) as i64)]),
            2 => op(Op::Neg, vec![op(Op::Mul, vec![T::Num(2), sub(r)])]),
            3 => op(Op::Not, vec![op(Op::Shl, vec![sub(r), T::Num(k)])]),
            4 => op(Op::Sub, vec![op(Op::Mul, vec![T::Num(2), sub(r)]), op(Op::Mul, vec![sub(r), op(Op::Mul, vec![T::Num(2), sub(r)])])]),
            _ => T::Num((r.next() % 512) as i64 - 256),
        };
        let bit = [Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize];
        match r.next() % 8 {
            0 => op(Op::Mul, vec![T::Num(c << k), op(Op::Shr, vec![sub(r), T::Num(k)])]),
            1 => op(Op::Shl, vec![op(Op::Shr, vec![sub(r), T::Num(k)]), T::Num(k + (r.next() % 3) as i64)]),
            2 => op(Op::Mul, vec![op(Op::Not, vec![op(Op::Shr, vec![sub(r), T::Num(k)])]), T::Num(c << (k + 1))]),
            3 | 4 => op(bit, vec![even(r), even(r)]),
            5 => op(Op::Add, vec![sub(r), sub(r)]),
            6 => op(bit, vec![sub(r), sub(r)]),
            _ => op(Op::Mul, vec![sub(r), sub(r)]),
        }
    }

    #[test]
    fn unshift_and_halve_preserve_value() {
        let mut r = Rng(0x6a09e667f3bcc909);
        let (mut unshifted, mut halved) = (0, 0);
        for _ in 0..400 {
            let depth = 1 + (r.next() % 3) as u32;
            let t = shifted_term(&mut r, depth);
            for (bits, signed) in [(8, false), (8, true), (64, false), (64, true)] {
                let (w, ty) = (Ctx::new(bits), NumType { bits, signed });
                let (u, h) = (unshift(&t, &w), halve(&t, &w));
                unshifted += (u != t) as u32;
                halved += (h != t) as u32;
                let check = |x: u64, y: u64| {
                    let env = |v: &str| if v == "x" { x } else { y };
                    let want = eval(&t, ty, &env);
                    assert_eq!(want, eval(&u, ty, &env), "{}\n{}", show(&t), show(&u));
                    assert_eq!(want, eval(&h, ty, &env), "{}\n{}", show(&t), show(&h));
                };
                if bits == 8 {
                    (0..1u64 << 16).for_each(|p| check(p & 0xff, p >> 8));
                } else {
                    (0..256).for_each(|_| check(r.next(), r.next()));
                }
            }
        }
        assert!(unshifted > 200 && halved > 200, "unshifted {unshifted}, halved {halved}");
    }

    /// `a op b` written as a linear MBA in `a`, `b` and `a & b`, with `a_lin`
    /// (equal to `a`) where `a` is not under a bitwise operation.
    fn mba_op(r: &mut Rng, a: &T, a_lin: &T, b: &T) -> T {
        let op = |o: Op, x: Vec<T>| T::Op(o, x);
        let and = op(Op::And, vec![a.clone(), b.clone()]);
        let sum = op(Op::Add, vec![a_lin.clone(), b.clone()]);
        match r.next() % 3 {
            0 => op(Op::Sub, vec![sum, op(Op::Mul, vec![T::Num(2), and])]),
            1 => op(Op::Sub, vec![sum, and]),
            _ => op(Op::Sub, vec![op(Op::Mul, vec![T::Num(2), op(Op::Or, vec![a.clone(), b.clone()])]), sum]),
        }
    }

    #[test]
    fn relate_preserves_value() {
        let mut r = Rng(0x3c6ef372fe94f82b);
        let op = |o: Op, x: Vec<T>| T::Op(o, x);
        let mut changed = 0;
        for i in 0..60 {
            let vars: &[&str] = if i % 2 == 0 { &["x", "y"] } else { &VARS };
            let (p, q) = (random_term_in(&mut r, 1, vars), random_term_in(&mut r, 1, vars));
            let (l, l_lin) = match r.next() % 3 {
                0 => (op(Op::Add, vec![p.clone(), q.clone()]), op(Op::Sub, vec![p, op(Op::Neg, vec![q])])),
                1 => (op(Op::Sub, vec![p.clone(), q.clone()]), op(Op::Add, vec![p, op(Op::Neg, vec![q])])),
                _ => (op(Op::Mul, vec![p.clone(), q.clone()]), op(Op::Mul, vec![q, p])),
            };
            let depth = 1 + (r.next() % 2) as u32;
            let mut b = random_term_in(&mut r, depth, vars);
            if r.next() % 2 == 0 {
                b = op([Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize], vec![b, T::Num((r.next() % 200) as i64 - 100)]);
            }
            let t = mba_op(&mut r, &l, &l_lin, &b);
            for (bits, signed) in [(8, false), (64, true)] {
                let (wd, ty) = (Ctx::new(bits), NumType { bits, signed });
                let base = rewrite(&t, &wd);
                let alt = relate(&base, &wd);
                changed += (alt != base) as u32;
                fn check(t: &T, alt: &T, ty: NumType, env: &impl Fn(&str) -> u64) {
                    assert_eq!(eval(t, ty, env), eval(alt, ty, env), "{}\n{}", show(t), show(alt));
                }
                if bits == 8 && vars.len() == 2 {
                    (0..1u64 << 16).for_each(|p| check(&t, &alt, ty, &|v: &str| if v == "x" { p & 0xff } else { p >> 8 }));
                } else {
                    for _ in 0..256 {
                        let env: HashMap<String, u64> = VARS.iter().map(|v| (v.to_string(), r.next())).collect();
                        check(&t, &alt, ty, &|v: &str| env[v]);
                    }
                }
            }
        }
        assert!(changed > 20, "only {changed} relations fired");
    }

    #[test]
    fn sum_size_matches_build_sum() {
        let mut r = Rng(0x9e3779b97f4a7c15);
        for w in [8u32, 64] {
            let wd = Ctx::new(w);
            let coef = |r: &mut Rng| [1, wd.mask, 2, wd.mask - 1, 1 << (w - 1), r.next() & wd.mask][(r.next() % 6) as usize];
            for _ in 0..3000 {
                let mut terms = Vec::new();
                for _ in 0..r.next() % 4 {
                    let (c, depth) = (coef(&mut r), (r.next() % 3) as u32);
                    terms.push((c, random_term(&mut r, depth)));
                }
                let konst = match r.next() % 3 {
                    0 => 0,
                    1 => terms.first().map_or(1, |t| t.0),
                    _ => coef(&mut r),
                };
                assert_eq!(sum_size(&terms, konst, &wd), size(&build_sum(&terms, konst, &wd)), "{terms:?} {konst}");
            }
        }
    }

    #[test]
    fn split_bits_and_wide_regions_preserve_value() {
        let op = |o: Op, a: Vec<T>| T::Op(o, a);
        let mut r = Rng(0x0bad_5eed_1234_5678);
        let ty = NumType { bits: 8, signed: false };
        let mut changed = 0;
        for k in 0..30 {
            let t = if k % 3 == 2 {
                let wide = ["x", "y", "a", "b", "c", "d", "e"];
                let bit = random_term_in(&mut r, 3, &wide);
                op(Op::Add, vec![random_term_in(&mut r, 2, &["x", "y"]), op(Op::Mul, vec![T::Num(0x35), bit])])
            } else {
                (0..2 + r.next() % 2)
                    .map(|_| {
                        let a = random_term_in(&mut r, 1, &["x", "y"]);
                        let sel = match r.next() % 4 {
                            0 => op(Op::And, vec![a, T::Num(1)]),
                            1 => op(Op::And, vec![op(Op::Not, vec![a]), T::Num(1)]),
                            2 => op(Op::And, vec![a, T::Num(2)]),
                            _ => op(Op::Not, vec![op(Op::Or, vec![a, T::Num(-3)])]),
                        };
                        op(Op::Mul, vec![sel, random_term_in(&mut r, 2, &["x", "y"])])
                    })
                    .reduce(|a, b| op(Op::Add, vec![a, b]))
                    .unwrap()
            };
            let alt = parse(&simplify_linear(&show(&t), 8));
            if alt == t {
                continue;
            }
            changed += 1;
            let mut names = crate::eval::vars(&t);
            names.extend(crate::eval::vars(&alt));
            for p in (0..1u64 << 16).step_by(3) {
                let env = |v: &str| match v {
                    "x" => p & 0xff,
                    "y" => p >> 8,
                    _ => (p.wrapping_mul(0x9e37_79b9) >> (names.iter().position(|n| n == v).unwrap() * 3)) & 0xff,
                };
                assert_eq!(eval(&t, ty, &env), eval(&alt, ty, &env), "{}\n{}", show(&t), show(&alt));
            }
        }
        assert!(changed > 10, "changed {changed}");
    }

    #[test]
    fn recombined_products_preserve_value() {
        let mut r = Rng(0x1234_5678_9abc_def1);
        let mut changed = 0;
        for k in 0..300 {
            let bits = if k % 2 == 0 { 8 } else { 64 };
            let w = Ctx::new(bits);
            let op = |o: Op, a: Vec<T>| T::Op(o, a);
            let (a, b) = (random_term_in(&mut r, 2, &["x", "y", "z"]), random_term_in(&mut r, 2, &["x", "y", "z"]));
            let b = if k % 3 == 0 { op(Op::And, vec![b, T::Num((r.next() % 64) as i64)]) } else { b };
            let not = |t: &T| op(Op::Not, vec![t.clone()]);
            let t = op(
                Op::Add,
                vec![
                    op(Op::Mul, vec![op(Op::Or, vec![a.clone(), b.clone()]), op(Op::And, vec![a.clone(), b.clone()])]),
                    op(Op::Mul, vec![op(Op::And, vec![a.clone(), not(&b)]), op(Op::And, vec![not(&a), b.clone()])]),
                ],
            );
            let Some(alt) = recombine_products(&t, &w) else { continue };
            changed += 1;
            for _ in 0..64 {
                let env: HashMap<String, u64> = ["x", "y", "z"].iter().map(|v| (v.to_string(), r.next())).collect();
                assert_eq!(full_eval(&t, &w, &env), full_eval(&alt, &w, &env), "{t:?}\n{alt:?}");
            }
        }
        assert!(changed > 100, "changed {changed}");
    }

    #[test]
    fn rewrite_preserves_value() {
        let mut r = Rng(0x2545f4914f6cdd1d);
        let mut changed = 0;
        for w in [8u32, 16, 32, 64] {
            let wd = Ctx::new(w);
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
                    Op::And => x & y,
                    Op::Or => x | y,
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
