//! Subterms with variable left shifts, such as `(y << (y & 63)) & 1`, are not
//! T-functions, but their low `m` bits depend only on the low `m` bits of their
//! leaves once every shift amount is known to be below `2^m`. A subterm whose bits
//! from `m` up are known is then a function of `m` bits per leaf: it is replaced by
//! a constant when all of them give one value, and otherwise by one of its few
//! values when the enclosing expression is proved not to change (`tfunc::equal_low`).

use crate::eval::{Op, Term as T, size};
use crate::known_bits::{self as kb, lowmask};
use crate::linear_mba::Ctx;
use crate::sched::{Limit, limit, limit_u32};

/// The limits a `Pass` reads (`crate::sched::Limit`), read once when it starts.
#[derive(Clone, Copy)]
struct Lims {
    max_bits: u32,
    max_context_bits: u32,
    narrow_context_bits: u32,
    max_try: usize,
    max_values: usize,
    max_product_bits: u32,
    refine_bits: u32,
    max_refine_bits: u32,
    proof: crate::tfunc::Proof,
}

impl Lims {
    fn read() -> Lims {
        Lims {
            max_bits: limit_u32(Limit::LowbitsMaxBits),
            max_context_bits: limit_u32(Limit::LowbitsMaxContextBits),
            narrow_context_bits: limit_u32(Limit::LowbitsNarrowContextBits),
            max_try: limit(Limit::LowbitsMaxTry),
            max_values: limit(Limit::LowbitsMaxValues),
            max_product_bits: limit_u32(Limit::LowbitsMaxProductBits),
            refine_bits: limit_u32(Limit::LowbitsRefineBits),
            max_refine_bits: limit_u32(Limit::LowbitsMaxRefineBits),
            proof: crate::tfunc::Proof::read(),
        }
    }
}

#[derive(Clone, Copy)]
struct Info {
    /// Bits known to be 0 and known to be 1.
    k0: u64,
    k1: u64,
    /// The low `m` bits, for any `m >= need`, depend only on the low `m` bits of the
    /// leaves. A node that is not `det` is a leaf of its ancestors.
    need: u32,
    /// The whole value depends only on the low `full` bits of the leaves.
    full: u32,
    det: bool,
    shift: bool,
}

impl Info {
    fn bits(&self) -> kb::Bits {
        kb::Bits { k0: self.k0, k1: self.k1 }
    }
}

fn leaf_info(k0: u64, k1: u64, w: &Ctx) -> Info {
    let mut i = Info { k0, k1, need: 0, full: 0, det: true, shift: false };
    i.full = high(&i, w);
    i
}

/// A subterm that is not `det` as a leaf: enumerations give its bits from `m` up as 0, so
/// only its known high zeros lower `full`.
fn opaque_info(k0: u64, k1: u64, w: &Ctx) -> Info {
    Info { k0, k1, need: 0, full: 64 - (!k0 & w.mask).leading_zeros(), det: true, shift: false }
}

/// Bits from which on every bit is known.
fn high(i: &Info, w: &Ctx) -> u32 {
    64 - (!(i.k0 | i.k1) & w.mask).leading_zeros()
}

/// `square`: the operands of a product are the same term.
fn combine(op: Op, args: &[Info], square: bool, w: &Ctx) -> Info {
    // Leaf placeholders (`Op::Leaf`, `Op::Slot`) of the semi-linear search.
    if args.is_empty() {
        return leaf_info(0, 0, w);
    }
    let m = w.mask;
    let a: Vec<Info> = args.iter().map(|i| if i.det { *i } else { opaque_info(i.k0, i.k1, w) }).collect();
    let (x, y) = (a[0], a.get(1).copied().unwrap_or(a[0]));
    let (bx, by) = (x.bits(), y.bits());
    let need = a.iter().map(|i| i.need).max().unwrap();
    let shift = a.iter().any(|i| i.shift);
    let mut full = a.iter().map(|i| i.full).max().unwrap();
    let r = match op {
        Op::Not => kb::not(bx),
        Op::And => kb::and(bx, by),
        Op::Or => kb::or(bx, by),
        Op::Xor => kb::xor(bx, by),
        Op::Neg => kb::neg(bx, w.w),
        Op::Sub => kb::sub(bx, by, w.w),
        Op::Add => kb::add(bx, by, w.w),
        Op::Mul => {
            if let Some((c, o)) = bx.value(w.w).map(|c| (c, y)).or_else(|| by.value(w.w).map(|c| (c, x))) {
                full = full.min(o.need.max(w.w.saturating_sub(c.trailing_zeros())));
            }
            kb::mul(bx, by, square, w.w)
        }
        Op::Shl if let Some(s) = by.value(w.w) => {
            if s < w.w as u64 {
                full = full.min(x.need.max(w.w - s as u32));
            }
            kb::shl(bx, s, w.w)
        }
        Op::Shl => {
            let mut i = Info { k0: kb::shl_any(bx, w.w).k0, k1: 0, need: need.max(y.full), full, det: y.full <= limit_u32(Limit::LowbitsMaxBits), shift: true };
            i.full = i.full.min(i.need.max(high(&i, w)));
            return i;
        }
        // Not `det`: the low bits depend on higher bits of `a`, so it is a leaf with known bits.
        Op::Shr if let Some(s) = by.value(w.w).filter(|s| *s < w.w as u64) => {
            let r = kb::shr(bx, s, w.w, w.signed);
            return Info { k0: r.k0, k1: r.k1, need: 0, full: w.w, det: false, shift: false };
        }
        _ => return Info { k0: 0, k1: 0, need: 0, full: w.w, det: false, shift: false },
    };
    let mut i = Info { k0: r.k0 & m, k1: r.k1 & m, need, full, det: true, shift };
    i.full = i.full.min(need.max(high(&i, w)));
    i
}

fn info(t: &T, w: &Ctx) -> Info {
    match t {
        T::Var(_) => leaf_info(0, 0, w),
        T::Num(c) => leaf_info(!(*c as u64) & w.mask, *c as u64 & w.mask, w),
        T::Op(op, a) => combine(*op, &a.iter().map(|x| info(x, w)).collect::<Vec<_>>(), is_square(t), w),
    }
}

#[derive(Clone)]
enum Ins {
    Leaf(usize),
    Const(u64),
    Un(fn(u64) -> u64),
    Bin(fn(u64, u64, u32) -> u64),
}

/// `t` as a stack program over its leaves: variables and subterms that are not `det`.
#[derive(Clone)]
struct Prog {
    ops: Vec<Ins>,
    leaves: Vec<T>,
    mask: u64,
    w: u32,
}

impl Prog {
    fn new(t: &T, w: &Ctx) -> Prog {
        let mut p = Prog { ops: Vec::new(), leaves: Vec::new(), mask: w.mask, w: w.w };
        p.compile(t, w);
        p
    }

    fn leaf(&mut self, t: &T) {
        let i = self.leaves.iter().position(|l| l == t).unwrap_or_else(|| {
            self.leaves.push(t.clone());
            self.leaves.len() - 1
        });
        self.ops.push(Ins::Leaf(i));
    }

    fn compile(&mut self, t: &T, w: &Ctx) -> Info {
        let T::Op(op, a) = t else {
            if let T::Num(c) = t {
                self.ops.push(Ins::Const(*c as u64 & w.mask));
            } else {
                self.leaf(t);
            }
            return info(t, w);
        };
        let start = self.ops.len();
        let infos: Vec<Info> = a.iter().map(|x| self.compile(x, w)).collect();
        let i = combine(*op, &infos, is_square(t), w);
        if !i.det {
            self.ops.truncate(start);
            self.leaf(t);
            return i;
        }
        self.ops.push(match op {
            Op::Not => Ins::Un(|x| !x),
            Op::Neg => Ins::Un(u64::wrapping_neg),
            Op::Add => Ins::Bin(|x, y, _| x.wrapping_add(y)),
            Op::Sub => Ins::Bin(|x, y, _| x.wrapping_sub(y)),
            Op::Mul => Ins::Bin(|x, y, _| x.wrapping_mul(y)),
            Op::And => Ins::Bin(|x, y, _| x & y),
            Op::Or => Ins::Bin(|x, y, _| x | y),
            Op::Xor => Ins::Bin(|x, y, _| x ^ y),
            _ => Ins::Bin(|x, y, w| if y >= w as u64 { 0 } else { x << y }),
        });
        i
    }

    fn run(&self, leaves: &[u64], stack: &mut Vec<u64>) -> u64 {
        stack.clear();
        for op in &self.ops {
            let v = match *op {
                Ins::Leaf(i) => leaves[i],
                Ins::Const(c) => c,
                Ins::Un(f) => f(stack.pop().unwrap()),
                Ins::Bin(f) => {
                    let y = stack.pop().unwrap();
                    f(stack.pop().unwrap(), y, self.w)
                }
            };
            stack.push(v & self.mask);
        }
        stack[0]
    }
}

/// Values of every leaf assignment's low `m` bits, in leaf order.
fn assignments(n: usize, m: u32) -> impl Iterator<Item = Vec<u64>> {
    (0u64..1 << (n as u32 * m)).map(move |p| (0..n).map(|j| p >> (j as u32 * m) & lowmask(m)).collect())
}

/// `Pass::values` results of one pre-pass run, with the budget each one cost.
#[derive(Default)]
pub(crate) struct ValuesMemo(std::sync::Mutex<crate::eval::FastMap<(u32, T, u32, u64), (u64, Option<Vec<u64>>, Prog)>>);

fn distinct_values(prog: &Prog, n: usize, m: u32, max_values: usize) -> Option<Vec<u64>> {
    let mut out = Vec::new();
    let mut stack = Vec::new();
    for low in assignments(n, m) {
        let v = prog.run(&low, &mut stack);
        if !out.contains(&v) {
            if out.len() == max_values {
                return None;
            }
            out.push(v);
        }
    }
    Some(out)
}

struct Cand {
    m: u32,
    values: Vec<u64>,
    prog: Prog,
}

struct Pass<'a> {
    w: &'a Ctx,
    lim: Lims,
    cands: crate::eval::FastMap<T, Cand>,
    budget: u64,
    wide: u64,
    refine: u64,
    /// Whether constant multipliers are cut (`cut_multiplier`): on the input that breaks
    /// constants shared with equal subterms elsewhere.
    cut: bool,
}

impl<'a> Pass<'a> {
    fn new(w: &'a Ctx, cut: bool) -> Pass<'a> {
        let budget = |l| limit(l) as u64;
        Pass { w, lim: Lims::read(), cands: Default::default(), budget: budget(Limit::LowbitsBudget), wide: budget(Limit::LowbitsWideBudget), refine: budget(Limit::LowbitsRefineBudget), cut }
    }

    /// Distinct values of a `det` subterm whose bits from `m` up are known, if at most `max_values`.
    fn values(&mut self, t: &T, m: u32) -> Option<(Vec<u64>, Prog)> {
        let key = (self.w.w, t.clone(), m, crate::sched::limits_key());
        // A hit draws the same budget as computing it again, so later calls see the same budget.
        if let Some((cost, vals, prog)) = self.w.low_values().0.lock().unwrap().get(&key) {
            self.budget = self.budget.checked_sub(*cost)?;
            return vals.clone().map(|v| (v, prog.clone()));
        }
        let prog = Prog::new(t, self.w);
        let n = prog.leaves.len();
        let (cost, vals) = if n as u32 * m > self.lim.max_bits {
            (0, None)
        } else {
            let cost = (1u64 << (n as u32 * m)) * prog.ops.len() as u64;
            self.budget = self.budget.checked_sub(cost)?;
            (cost, distinct_values(&prog, n, m, self.lim.max_values))
        };
        self.w.low_values().0.lock().unwrap().insert(key, (cost, vals.clone(), prog.clone()));
        vals.map(|v| (v, prog))
    }

    fn fold(&mut self, t: &T) -> (T, Info) {
        let w = self.w;
        let T::Op(op, a) = t else { return (t.clone(), info(t, w)) };
        let (args, infos): (Vec<T>, Vec<Info>) = a.iter().map(|x| self.fold(x)).unzip();
        let node = T::Op(*op, args);
        let mut infos = infos;
        let konst = |v: u64| (T::Num(w.signed(v)), info(&T::Num(w.signed(v)), w));
        if let Some(j) = const_operand(*op, &node) {
            infos[j] = self.refine_low(&a_of(&node)[j], infos[j]);
        }
        if self.cut && let Some(r) = self.cut_multiplier(*op, &node, &mut infos) {
            let i = info(&r, w);
            return (r, i);
        }
        let i = combine(*op, &infos, is_square(&node), w);
        let node = if *op == Op::Mul { low_factor(node, &infos, w) } else { node };
        if (i.k0 | i.k1) & w.mask == w.mask {
            return konst(i.k1);
        }
        if let Some(r) = neg_xor(&node, &infos, w) {
            let i = info(&r, w);
            return (r, i);
        }
        if let Some(r) = known_bitwise(*op, &node, &infos, w) {
            return (r, i);
        }
        // `a ^ b = a + b - 2·(a & b)`, and `2·(a & b) = 0` when `b` has only the top bit. Only
        // for a product `b`: a shifted `b` (Loki) rebuilds better as it is.
        if let T::Op(Op::Xor, a) = &node
            && a.iter().zip(&infos).any(|(x, i)| matches!(x, T::Op(Op::Mul, _)) && i.k0 & w.mask >> 1 == w.mask >> 1)
        {
            return (T::Op(Op::Add, a.clone()), i);
        }
        let node = masked_add_as_or(node, w);
        if i.det && (i.shift || i.full <= self.lim.max_product_bits && has_product(&node)) && size(&node) <= self.lim.max_try {
            let m = i.full;
            if let Some((values, prog)) = self.values(&node, m) {
                if values.len() == 1 {
                    return konst(values[0]);
                }
                if prog.leaves.iter().all(|l| matches!(l, T::Var(_))) {
                    self.cands.insert(node.clone(), Cand { m, values, prog });
                }
            }
        }
        (node, i)
    }

    /// `i` with the lowest unknown bits of the `det` term `t` made known where every
    /// assignment of the leaves' low bits gives one value (`(x*y) & (x + y)` has bit 0 clear).
    fn refine_low(&mut self, t: &T, i: Info) -> Info {
        let w = self.w;
        let b = (i.k0 | i.k1).trailing_ones();
        if !i.det || b >= w.w || !small(t, self.lim.max_try) || !has_product(t) {
            return i;
        }
        let prog = Prog::new(t, w);
        let n = prog.leaves.len() as u32;
        let m = b.saturating_add(self.lim.refine_bits).min(w.w).min(self.lim.max_refine_bits / n.max(1));
        if m <= b || m < i.need {
            return i;
        }
        let Some(budget) = self.refine.checked_sub((1u64 << (n * m)) * prog.ops.len() as u64) else { return i };
        self.refine = budget;
        let (mut all, mut any) = (lowmask(m), 0);
        let mut stack = Vec::new();
        for low in assignments(n as usize, m) {
            let v = prog.run(&low, &mut stack) & lowmask(m);
            (all, any) = (all & v, any | v);
        }
        Info { k0: i.k0 | !any & lowmask(m), k1: i.k1 | all, ..i }
    }

    /// A product `c*a` (`a` possibly several factors) with `c` cut to its low `w - k` bits,
    /// sign-extended, when `a` has `k` known trailing zeros and that leaves `0` or `±1`
    /// (`0x80000001*a` with `a` even is `a`).
    fn cut_multiplier(&mut self, op: Op, node: &T, infos: &mut [Info]) -> Option<T> {
        let w = self.w;
        let a = a_of(node);
        if op != Op::Mul || a.len() != 2 || !small(node, self.lim.max_try) {
            return None;
        }
        let mut fs = Vec::new();
        factors(node, &mut fs);
        let mut consts = fs.iter().filter_map(|f| if let T::Num(c) = f { Some(*c) } else { None });
        let (Some(c), None) = (consts.next(), consts.next()) else { return None };
        let rest = fs.iter().filter(|f| !matches!(f, T::Num(_))).map(|f| (*f).clone()).reduce(|x, y| T::Op(Op::Mul, vec![x, y]))?;
        let direct = a.iter().position(|x| matches!(x, T::Num(_)));
        let ri = match direct {
            Some(j) => {
                infos[1 - j] = self.refine_low(&a[1 - j], infos[1 - j]);
                infos[1 - j]
            }
            None => self.refine_low(&rest, info(&rest, w)),
        };
        let k = ri.k0.trailing_ones().min(w.w);
        if k == 0 {
            return None;
        }
        let r = w.w - k;
        let low = c as u64 & lowmask(r);
        let d = [low, low.wrapping_sub(1u64 << r.min(63))].into_iter().map(|v| w.signed(v & w.mask)).min_by_key(|v| v.unsigned_abs())?;
        // Only cuts that drop the multiplier: others break constants shared with other
        // products (`(a | K)·(c·(a & K)) + (a & ~K)·(c·(~a & K))` for `split_bits`).
        if d.unsigned_abs() > 1 || d.unsigned_abs() >= w.signed(c as u64 & w.mask).unsigned_abs() {
            return None;
        }
        Some(match d {
            0 => T::Num(0),
            1 => rest,
            _ => replace_factor(node, &T::Num(d)),
        })
    }

    fn collect(&self, t: &T, out: &mut Vec<T>) {
        if self.cands.contains_key(t) {
            if !out.contains(t) {
                out.push(t.clone());
            }
        } else if let T::Op(_, a) = t {
            a.iter().for_each(|x| self.collect(x, out));
        }
    }

    /// `t` with candidate subterms replaced by one of their values where `t` is
    /// proved unchanged; tried in the children when the proof cannot be run on `t`.
    fn context(&mut self, t: &T) -> T {
        let T::Op(op, a) = t else { return t.clone() };
        let mut found = Vec::new();
        a.iter().for_each(|x| self.collect(x, &mut found));
        if found.is_empty() {
            return t.clone();
        }
        let mut vars = Vec::new();
        crate::tfunc::var_names(t, &mut vars);
        let n = vars.len();
        let m = found.iter().map(|c| self.cands[c].m).max().unwrap();
        let mut unknown = n as u32 * m > self.lim.max_context_bits || size(t) > self.lim.max_try;
        if !unknown {
            let names: Vec<String> = (0..found.len()).map(|i| format!("\u{4}{i}")).collect();
            let holes: Vec<T> = names.iter().map(|s| T::Var(s.clone())).collect();
            let abs = replace(t, &found, &holes);
            let maps: Vec<Vec<usize>> = found
                .iter()
                .map(|c| self.cands[c].prog.leaves.iter().map(|l| vars.iter().position(|v| T::Var(v.clone()) == *l).unwrap()).collect())
                .collect();
            let progs: Vec<&Prog> = found.iter().map(|c| &self.cands[c].prog).collect();
            let extra = |low: &[u64]| -> Vec<u64> {
                let mut stack = Vec::new();
                progs.iter().zip(&maps).map(|(p, mp)| p.run(&mp.iter().map(|&j| low[j]).collect::<Vec<_>>(), &mut stack)).collect()
            };
            let all: Vec<String> = vars.iter().chain(&names).cloned().collect();
            let cost = (1u64 << (n as u32 * m)) * size(t) as u64;
            for (i, c) in found.iter().enumerate() {
                for &v in &self.cands[c].values {
                    let wide = if n as u32 * m > self.lim.narrow_context_bits { self.wide.checked_sub(cost) } else { Some(self.wide) };
                    let (Some(budget), Some(wide)) = (self.budget.checked_sub(cost), wide) else {
                        unknown = true;
                        break;
                    };
                    (self.budget, self.wide) = (budget, wide);
                    let num = T::Num(self.w.signed(v));
                    let g = replace(&abs, &[T::Var(names[i].clone())], std::slice::from_ref(&num));
                    match crate::tfunc::equal_low(&abs, &g, &all, n, m, &extra, self.lim.proof, self.w) {
                        // Only the occurrences `abs` abstracted: `c` inside another candidate was not proved.
                        Some(true) => return self.context(&replace(&g, &holes, &found)),
                        Some(false) => {}
                        None => unknown = true,
                    }
                }
            }
        }
        if !unknown {
            return t.clone();
        }
        T::Op(*op, a.iter().map(|x| self.context(x)).collect())
    }
}

/// `size(t) <= limit`, without walking past `limit` nodes.
fn small(t: &T, limit: usize) -> bool {
    fn go(t: &T, left: &mut usize) -> bool {
        if *left == 0 {
            return false;
        }
        *left -= 1;
        match t {
            T::Op(_, a) => a.iter().all(|x| go(x, left)),
            _ => true,
        }
    }
    let mut left = limit;
    go(t, &mut left)
}

fn factors<'t>(t: &'t T, out: &mut Vec<&'t T>) {
    match t {
        T::Op(Op::Mul, a) => a.iter().for_each(|x| factors(x, out)),
        _ => out.push(t),
    }
}

/// `t` with its constant factor (reached through products only) replaced by `d`.
fn replace_factor(t: &T, d: &T) -> T {
    match t {
        T::Op(Op::Mul, a) => T::Op(Op::Mul, a.iter().map(|x| replace_factor(x, d)).collect()),
        T::Num(_) => d.clone(),
        _ => t.clone(),
    }
}

fn a_of(t: &T) -> &[T] {
    match t {
        T::Op(_, a) => a,
        _ => &[],
    }
}

/// The non-constant operand of a bitwise operation with a constant.
fn const_operand(op: Op, t: &T) -> Option<usize> {
    let a = a_of(t);
    if !matches!(op, Op::And | Op::Or | Op::Xor) || a.len() != 2 {
        return None;
    }
    match (&a[0], &a[1]) {
        (T::Num(_), T::Num(_)) => None,
        (_, T::Num(_)) => Some(0),
        (T::Num(_), _) => Some(1),
        _ => None,
    }
}

fn is_square(t: &T) -> bool {
    matches!(t, T::Op(Op::Mul, a) if a.len() == 2 && a[0] == a[1])
}

fn split_add(t: &T) -> Option<(&T, i64)> {
    match t {
        T::Op(Op::Add, a) => match (&a[0], &a[1]) {
            (q, T::Num(c)) | (T::Num(c), q) => Some((q, *c)),
            _ => None,
        },
        _ => None,
    }
}

/// A product with a factor of `t` known trailing zeros only sees the low `w - t` bits of
/// the other factor: that factor becomes a subterm `q + K` of the first one that agrees
/// with it there (`(A & -2^32)*(q + c)` with `A = q + K` is `(A & -2^32)*A`), or else
/// has a constant operand cut to `w - t` bits where that gives a constant of the first
/// factor (`(a & -8)*(K ^ s)` with `K = 2^63 + 7` is `(a & -8)*(7 ^ s)`).
fn low_factor(node: T, infos: &[Info], w: &Ctx) -> T {
    let T::Op(op, a) = &node else { return node };
    for j in 0..2 {
        let t = infos[j].k0.trailing_ones().min(w.w);
        if t == 0 || t >= w.w || a.iter().any(|x| matches!(x, T::Num(_))) {
            continue;
        }
        let r = w.w - t;
        let q = &a[1 - j];
        let mut same = None;
        if let Some((s, c)) = split_add(q) {
            let mut found = |x: &T| {
                if same.is_none() && x != q && split_add(x).is_some_and(|(s2, k)| s2 == s && (k.wrapping_sub(c) as u64) & lowmask(r) == 0) {
                    same = Some(x.clone());
                }
            };
            visit(&a[j], &mut found);
        }
        // Only direct constant operands, and only to a constant (or complement) of the first
        // factor: other cuts break what `q` shares, as `K` in `(a & ~K)*(~a & K)`.
        let mut consts = Vec::new();
        visit(&a[j], &mut |x: &T| {
            if let T::Num(c) = x {
                consts.extend([*c as u64 & w.mask, !*c as u64 & w.mask]);
            }
        });
        let cut = |x: &T| match (x, crate::linear_mba::low_consts(x, r)) {
            (T::Num(c), T::Num(d)) if consts.contains(&(d as u64 & w.mask)) && !consts.contains(&(*c as u64 & w.mask)) => T::Num(d),
            _ => x.clone(),
        };
        let next = same.unwrap_or_else(|| match q {
            T::Op(o, b) if matches!(o, Op::Add | Op::Sub | Op::Mul | Op::And | Op::Or | Op::Xor) => T::Op(*o, b.iter().map(cut).collect()),
            _ => q.clone(),
        });
        if next != *q {
            let mut b = a.clone();
            b[1 - j] = next;
            return T::Op(*op, b);
        }
    }
    node
}

/// `t` with the factor of each product beside a factor with `k` known trailing zeros
/// shortened by `shorter_low`. Run on rebuilt terms: on the input, the cut factor no
/// longer shares its constants with equal subterms elsewhere.
pub(crate) fn cut_products(t: &T, w: &Ctx) -> T {
    fn go(t: &T, w: &Ctx) -> (T, Info) {
        let T::Op(op, a) = t else { return (t.clone(), info(t, w)) };
        let (mut args, infos): (Vec<T>, Vec<Info>) = a.iter().map(|x| go(x, w)).unzip();
        let i = combine(*op, &infos, is_square(&T::Op(*op, args.clone())), w);
        if *op == Op::Mul && !args.iter().any(|x| matches!(x, T::Num(_))) {
            for j in 0..2 {
                let k = infos[j].k0.trailing_ones().min(w.w);
                if k > 0 && k < w.w {
                    if let Some(q) = shorter_low(&args[1 - j], w.w - k, w) {
                        args[1 - j] = q;
                        break;
                    }
                }
            }
        }
        // A constant factor with `k` trailing zeros also only sees the low `w - k` bits of
        // the other, cut only where that drops an operand (`-2*(a & (0x80000001*b))`).
        if let (Op::Mul, [T::Num(c), q] | [q, T::Num(c)]) = (*op, args.as_slice()) {
            let k = (*c as u64 & w.mask).trailing_zeros();
            if k > 0 && k < w.w && !matches!(q, T::Num(_)) {
                let folded = drop_identities(&crate::linear_mba::low_consts(q, w.w - k), w);
                if size(&folded) < size(q) {
                    return (T::Op(Op::Mul, vec![T::Num(*c), folded]), i);
                }
            }
        }
        (T::Op(*op, args), i)
    }
    go(t, w).0
}

/// `q` with every constant cut to its low `r` bits, when that drops an operand
/// (`(x + z)*0x10000001` with `r = 24` is `x + z`) or a small `q` then rebuilds smaller.
fn shorter_low(q: &T, r: u32, w: &Ctx) -> Option<T> {
    let cut = crate::linear_mba::low_consts(q, r);
    if cut == *q {
        return None;
    }
    let folded = drop_identities(&cut, w);
    if size(&folded) < size(q) {
        return Some(folded);
    }
    if size(q) > limit(Limit::LowbitsMaxLowRebuild) {
        return None;
    }
    let low = crate::linear_mba::sub_index("low_factor");
    let rebuilt = crate::linear_mba::sub(low, &folded, w);
    (size(&rebuilt) < size(q) && size(&rebuilt) < size(&crate::linear_mba::sub(low, q, w))).then_some(rebuilt)
}

/// `t` without operations whose constant operand leaves the other unchanged (`a*1`, `a + 0`, `a & -1`, ...).
fn drop_identities(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| drop_identities(x, w)).collect();
    if a.len() == 2 {
        let unit = |x: &T| match x {
            T::Num(c) => {
                let c = *c as u64 & w.mask;
                match op {
                    Op::Mul => c == 1,
                    Op::Add | Op::Or | Op::Xor => c == 0,
                    Op::And => c == w.mask,
                    _ => false,
                }
            }
            _ => false,
        };
        if unit(&a[1]) || (*op == Op::Sub && matches!(&a[1], T::Num(c) if *c as u64 & w.mask == 0)) {
            return a[0].clone();
        }
        if unit(&a[0]) && *op != Op::Sub {
            return a[1].clone();
        }
    }
    T::Op(*op, a)
}

fn visit(t: &T, f: &mut impl FnMut(&T)) {
    f(t);
    if let T::Op(_, a) = t {
        a.iter().for_each(|x| visit(x, f));
    }
}

fn has_product(t: &T) -> bool {
    match t {
        T::Op(op, a) if *op == Op::Mul && !a.iter().any(|x| matches!(x, T::Num(_))) => true,
        T::Op(_, a) => a.iter().any(has_product),
        _ => false,
    }
}

/// `-(a ^ K)` as `a ^ -K` when `a` has `t` known trailing zeros and `K mod 2^t` is not 0:
/// negating `2^t·(a' ^ Kh) + Kl` gives `2^t·(a' ^ ~Kh) + (2^t - Kl)` without a carry.
fn neg_xor(node: &T, infos: &[Info], w: &Ctx) -> Option<T> {
    let T::Op(Op::Neg, a) = node else { return None };
    let T::Op(Op::Xor, b) = &a[0] else { return None };
    let (x, k) = match (&b[0], &b[1]) {
        (x, T::Num(k)) | (T::Num(k), x) if !matches!(x, T::Num(_)) => (x, *k as u64 & w.mask),
        _ => return None,
    };
    // The low bits of `a` known from those of `a ^ K`.
    let i = infos[0];
    let kn = (i.k0 | i.k1).trailing_ones().min(w.w);
    let low = (i.k1 ^ k) & lowmask(kn);
    let t = if low == 0 { kn } else { low.trailing_zeros() };
    (t > 0 && k & lowmask(t) != 0).then(|| T::Op(Op::Xor, vec![x.clone(), T::Num(w.signed(k.wrapping_neg() & w.mask))]))
}

/// An arithmetic operand `a` and a constant `c` whose bitwise operation only touches
/// known bits of `a`, written as `a + d`: `(2*x + 4) ^ 1` is `(2*x + 4) + 1`, which
/// joins the enclosing linear region (Tigress EncodeData).
fn known_bitwise(op: Op, node: &T, infos: &[Info], w: &Ctx) -> Option<T> {
    let T::Op(_, a) = node else { return None };
    if !matches!(op, Op::And | Op::Or | Op::Xor) {
        return None;
    }
    let (j, c) = match (&a[0], &a[1]) {
        (_, T::Num(c)) => (0, *c as u64 & w.mask),
        (T::Num(c), _) => (1, *c as u64 & w.mask),
        _ => return None,
    };
    if !matches!(&a[j], T::Op(o, _) if matches!(o, Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Shl)) {
        return None;
    }
    let (k0, k1) = (infos[j].k0, infos[j].k1);
    let touched = if op == Op::And { !c & w.mask } else { c };
    if touched & !(k0 | k1) != 0 {
        return None;
    }
    let d = match op {
        Op::Xor => (c & k0).wrapping_sub(c & k1),
        Op::Or => c & k0,
        _ => (touched & k1).wrapping_neg(),
    } & w.mask;
    Some(if d == 0 { a[j].clone() } else { T::Op(Op::Add, vec![a[j].clone(), T::Num(w.signed(d))]) })
}

/// The bitwise operation `node` with each operand `(a & M) + K` (`M & K = 0`) written as
/// `(a & M) | K`, so that the operand joins the bitwise region instead of being a leaf.
fn masked_add_as_or(node: T, w: &Ctx) -> T {
    let T::Op(op, a) = node else { return node };
    if !matches!(op, Op::And | Op::Or | Op::Xor) {
        return T::Op(op, a);
    }
    let or = |x: T| match &x {
        T::Op(Op::Add, b) => match (&b[0], &b[1]) {
            (m @ T::Op(Op::And, c), T::Num(k)) | (T::Num(k), m @ T::Op(Op::And, c)) => match (&c[0], &c[1]) {
                (_, T::Num(mm)) | (T::Num(mm), _) if *mm as u64 & *k as u64 & w.mask == 0 => T::Op(Op::Or, vec![m.clone(), T::Num(*k)]),
                _ => x,
            },
            _ => x,
        },
        _ => x,
    };
    T::Op(op, a.into_iter().map(or).collect())
}

/// `t` with each `2^k·(a ^ K) + c` (`0 < c < 2^k`) written as `(2^k·a) ^ (2^k·K + c)`:
/// the low `k` bits of `2^k·(a ^ K)` are 0, so adding `c` sets them.
pub(crate) fn shifted_xor(t: &T, w: &Ctx) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| shifted_xor(x, w)).collect();
    if *op == Op::Add {
        if let (T::Op(Op::Mul, m), T::Num(c)) | (T::Num(c), T::Op(Op::Mul, m)) = (&a[0], &a[1]) {
            if let (T::Num(p), T::Op(Op::Xor, b)) | (T::Op(Op::Xor, b), T::Num(p)) = (&m[0], &m[1]) {
                if let (x, T::Num(k)) | (T::Num(k), x) = (&b[0], &b[1]) {
                    let (p, c, k) = (*p as u64 & w.mask, *c as u64 & w.mask, *k as u64 & w.mask);
                    if p > 1 && p.is_power_of_two() && c != 0 && c < p {
                        let scaled = T::Op(Op::Mul, vec![T::Num(w.signed(p)), x.clone()]);
                        return T::Op(Op::Xor, vec![scaled, T::Num(w.signed(k.wrapping_mul(p).wrapping_add(c) & w.mask))]);
                    }
                }
            }
        }
    }
    T::Op(*op, a)
}

/// Bits of `t` not known to be 0.
pub(crate) fn possible_bits(t: &T, w: &Ctx) -> u64 {
    !info(t, w).k0 & w.mask
}

/// Bits of `t` known neither 0 nor 1.
pub(crate) fn unknown_bits(t: &T, w: &Ctx) -> u64 {
    let i = info(t, w);
    !(i.k0 | i.k1) & w.mask
}

pub(crate) fn replace(t: &T, from: &[T], to: &[T]) -> T {
    if let Some(i) = from.iter().position(|f| f == t) {
        return to[i].clone();
    }
    match t {
        T::Op(op, a) => T::Op(*op, a.iter().map(|x| replace(x, from, to)).collect()),
        _ => t.clone(),
    }
}

/// `t` with subterms determined by the low bits of their leaves folded, where that
/// needs a variable left shift or a product (or is a constant by known bits).
pub(crate) fn simplify(t: &T, w: &Ctx) -> T {
    simplify_with(t, w, false)
}

/// `simplify` for a rebuilt term, also cutting constant multipliers.
pub(crate) fn simplify_rebuilt(t: &T, w: &Ctx) -> T {
    simplify_with(t, w, true)
}

fn simplify_with(t: &T, w: &Ctx, cut: bool) -> T {
    let mut p = Pass::new(w, cut);
    let (r, _) = p.fold(t);
    if p.cands.is_empty() { r } else { p.context(&r) }
}

/// `rebuild` applied with each product of two non-constant factors first replaced by a
/// fresh variable: an identity that holds for every value of the variable holds for the
/// product, and `simplify` only follows a few low bits through products. Factors that
/// are sums are multiplied out first, so `y*(x - 1)` and `x*y` share the variable of
/// `x*y`. The result is kept when smaller.
pub(crate) fn over_products(t: &T, w: &Ctx, rebuild: impl Fn(&T) -> T) -> T {
    let mut monos = Vec::new();
    let a = abstract_products(t, w, limit(Limit::LowbitsMaxFactorTerms), &mut monos);
    if monos.is_empty() {
        return t.clone();
    }
    let r = rebuild(&a);
    if r == a {
        return t.clone();
    }
    let vars: Vec<T> = (0..monos.len()).map(product_var).collect();
    // A product's factors can hold the variables of earlier products.
    let mut back = r;
    for _ in 0..=monos.len() {
        let next = replace(&back, &vars, &monos);
        if next == back {
            break;
        }
        back = next;
    }
    if size(&back) < size(t) { back } else { t.clone() }
}

fn product_var(i: usize) -> T {
    T::Var(format!("%p{i}"))
}

/// `t` with products of non-constant factors replaced by `product_var`s; `monos[i]` is
/// the product variable `i` stands for, its factors in a fixed order. Factors of at most
/// `most` terms are multiplied out.
fn abstract_products(t: &T, w: &Ctx, most: usize, monos: &mut Vec<T>) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    let a: Vec<T> = a.iter().map(|x| abstract_products(x, w, most, monos)).collect();
    if *op != Op::Mul || a.iter().any(|x| matches!(x, T::Num(_))) {
        return T::Op(*op, a);
    }
    let mut var = |x: &T, y: &T| {
        let key = |t: &T| crate::eval::show(t);
        let m = if key(x) <= key(y) { T::Op(Op::Mul, vec![x.clone(), y.clone()]) } else { T::Op(Op::Mul, vec![y.clone(), x.clone()]) };
        let i = monos.iter().position(|n| *n == m).unwrap_or_else(|| {
            monos.push(m);
            monos.len() - 1
        });
        product_var(i)
    };
    let (mut ta, mut ka, mut tb, mut kb) = (Vec::new(), 0, Vec::new(), 0);
    crate::linear_mba::sum_terms(&a[0], 1, w, &mut ta, &mut ka);
    crate::linear_mba::sum_terms(&a[1], 1, w, &mut tb, &mut kb);
    if ta.len() > most || tb.len() > most {
        return var(&a[0], &a[1]);
    }
    let mut terms: Vec<(u64, T)> = Vec::new();
    for (ca, xa) in &ta {
        for (cb, xb) in &tb {
            terms.push((ca.wrapping_mul(*cb), var(xa, xb)));
        }
        terms.push((ca.wrapping_mul(kb), xa.clone()));
    }
    terms.extend(tb.iter().map(|(cb, xb)| (cb.wrapping_mul(ka), xb.clone())));
    let konst = ka.wrapping_mul(kb) & w.mask;
    terms
        .into_iter()
        .filter(|(c, _)| c & w.mask != 0)
        .map(|(c, x)| if c & w.mask == 1 { x } else { T::Op(Op::Mul, vec![T::Num(w.signed(c & w.mask)), x]) })
        .chain((konst != 0).then(|| T::Num(w.signed(konst))))
        .reduce(|s, x| T::Op(Op::Add, vec![s, x]))
        .unwrap_or(T::Num(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval::{NumType, eval};

    fn random_term(h: &mut u64, depth: u32) -> T {
        *h ^= *h << 13;
        *h ^= *h >> 7;
        *h ^= *h << 17;
        let r = *h;
        if depth == 0 || r % 9 == 0 {
            return match r >> 8 & 3 {
                0 => T::Num((r >> 40) as i64 % 5 - 2),
                1 => T::Var("x".into()),
                _ => T::Var("y".into()),
            };
        }
        let sub = |h: &mut u64| random_term(h, depth - 1);
        let op = [Some(Op::Add), Some(Op::Sub), Some(Op::And), Some(Op::Or), Some(Op::Xor), Some(Op::Not), Some(Op::Neg), Some(Op::Mul), Some(Op::Shl), Some(Op::Shl), None, Some(Op::Shr)][(r >> 16) as usize % 12];
        match op {
            None => T::Op(Op::And, vec![sub(h), T::Num((r >> 24) as i64 % 4 + 1)]),
            Some(op @ (Op::Not | Op::Neg)) => T::Op(op, vec![sub(h)]),
            Some(Op::Mul) if r >> 31 & 3 == 0 => {
                let s = sub(h);
                T::Op(Op::Mul, vec![s.clone(), s])
            }
            Some(Op::Shl) if r >> 30 & 1 == 0 => T::Op(Op::Shl, vec![sub(h), T::Op(Op::And, vec![sub(h), T::Num(7)])]),
            Some(Op::Shr) if r >> 30 & 1 == 0 => T::Op(Op::Shr, vec![sub(h), T::Num((r >> 33) as i64 % 8)]),
            Some(op) => T::Op(op, vec![sub(h), sub(h)]),
        }
    }

    /// A linear expression of `x`, `y` and a masked variable shift of random terms.
    fn context_term(h: &mut u64) -> T {
        let op = |o: Op, a: T, b: T| T::Op(o, vec![a, b]);
        let var = |r: u64| T::Var(if r & 1 == 0 { "x" } else { "y" }.into());
        let s = random_term(h, 2);
        let amount = match *h >> 40 & 3 {
            0 => s.clone(),
            1 => T::Op(Op::Neg, vec![s.clone()]),
            2 => T::Op(Op::Not, vec![s.clone()]),
            _ => random_term(h, 2),
        };
        let shifted = op(Op::Shl, s, op(Op::And, amount, T::Num(7)));
        let t = op(Op::And, shifted, T::Num((*h >> 20) as i64 % 3 + 1));
        let ops = [Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor];
        let inner = op(ops[(*h >> 24) as usize % 5], var(*h >> 28), t);
        op(ops[(*h >> 32) as usize % 5], var(*h >> 36), inner)
    }

    #[test]
    fn known_bits_match_evaluation() {
        crate::sched::in_default_run(|| {
            let mut h = 0x2545_f491_4f6c_dd1du64;
            for k in 0..600 {
                let ty = NumType { bits: 8, signed: k % 2 == 1 };
                let t = random_term(&mut h, 4);
                for w in [Ctx::new(8), Ctx::typed(8, Some(ty.signed))] {
                    let i = info(&t, &w);
                    for p in 0u64..1 << 16 {
                        let v = eval(&t, ty, &|n: &str| if n == "x" { p & 0xff } else { p >> 8 }).unwrap() & 0xff;
                        assert!(v & i.k0 == 0 && !v & i.k1 & 0xff == 0, "{t:?} at {p:#x}: {v:#x}");
                    }
                }
            }
        })
    }

    /// Known zeros as the egglog `kz` rules derive them: every rule that matches, joined by `|`.
    fn kz(t: &T, w: i64, signed: bool) -> i64 {
        use crate::known_bits::*;
        let T::Op(op, a) = t else { return if let T::Num(c) = t { !c } else { 0 } };
        let z: Vec<i64> = a.iter().map(|x| kz(x, w, signed)).collect();
        let k = match a.get(1) {
            Some(T::Num(k)) => Some(*k),
            _ => None,
        };
        match op {
            Op::And => z[0] | z[1],
            Op::Or | Op::Xor => z[0] & z[1],
            Op::Neg => kz_low(z[0], w),
            Op::Add | Op::Sub => kz_add(z[0], z[1], w),
            Op::Mul => kz_low(z[0], w) | kz_low(z[1], w) | kz_mul(z[0], z[1], w),
            Op::Shl => {
                let c = k.and_then(|k| Some(kz_shl(0, k, w)? | kz_shl(z[0], k, w)?)).unwrap_or(0);
                c | kz_low(z[0], w)
            }
            Op::Shr => k.and_then(|k| kz_shr(z[0], k, w, signed)).unwrap_or(0),
            _ => 0,
        }
    }

    /// The `kz` rules and `info` agree with evaluation, and `info` knows every zero `kz` knows.
    #[test]
    fn known_bits_refine_egglog_kz() {
        crate::sched::in_default_run(|| {
            let mut h = 0x6a09_e667_f3bc_c908u64;
            let mut finer = 0;
            for k in 0..600 {
                let signed = k % 2 == 1;
                let ty = NumType { bits: 8, signed };
                let t = random_term(&mut h, 4);
                let z = kz(&t, 8, signed) as u64 & 0xff;
                for p in 0u64..1 << 16 {
                    let v = eval(&t, ty, &|n: &str| if n == "x" { p & 0xff } else { p >> 8 }).unwrap() & 0xff;
                    assert!(v & z == 0, "{t:?} at {p:#x}: {v:#x}, kz {z:#x}");
                }
                let i = info(&t, &Ctx::typed(8, Some(signed)));
                assert!(z & !i.k0 == 0, "{t:?}: kz {z:#x}, k0 {:#x}", i.k0);
                finer += (i.k0 != z) as u32;
            }
            assert!(finer > 15, "finer {finer}");
        })
    }

    #[test]
    fn matches_exhaustive_check_at_8_bits() {
        crate::sched::in_default_run(|| {
            let w = Ctx::new(8);
            let mut h = 0x9e37_79b9_7f4a_7c15u64;
            let (mut changed, mut in_context) = (0, 0);
            for k in 0..500 {
                let ty = NumType { bits: 8, signed: k % 2 == 1 };
                let t = if k < 200 { random_term(&mut h, 4) } else { context_term(&mut h) };
                let mut p = Pass::new(&w, true);
                let folded = p.fold(&t).0;
                let r = p.context(&folded);
                if r == t {
                    continue;
                }
                changed += 1;
                in_context += (r != folded) as u32;
                for x in 0..256u64 {
                    for y in 0..256u64 {
                        let env = |v: &str| if v == "x" { x } else { y };
                        assert_eq!(eval(&t, ty, &env), eval(&r, ty, &env), "{t:?}\n{r:?}");
                    }
                }
            }
            assert!(changed > 100 && in_context > 5, "changed {changed}, in context {in_context}");
        })
    }

    /// Polynomials of `x` and `y` under a small mask or a multiplier with trailing zeros.
    fn noise_term(h: &mut u64) -> T {
        let op = |o: Op, a: T, b: T| T::Op(o, vec![a, b]);
        let mut next = || {
            *h ^= *h << 13;
            *h ^= *h >> 7;
            *h ^= *h << 17;
            *h
        };
        let r = next();
        let var = |r: u64| T::Var(if r & 1 == 0 { "x" } else { "y" }.into());
        let lin = |r: u64| op(Op::Add, op(Op::Mul, T::Num((r >> 8) as i64), var(r)), T::Num((r >> 20) as i64));
        let p = op(Op::Add, op(Op::Mul, var(r >> 1), lin(next())), T::Num((next() >> 3) as i64));
        let p = if r >> 5 & 1 == 0 { p } else { op([Op::Mul, Op::Xor, Op::Or][(r >> 6) as usize % 3], p, lin(next())) };
        match r >> 9 & 3 {
            0 => op(Op::And, p, T::Num(1)),
            1 => op(Op::And, T::Num(3), p),
            2 => op(Op::Mul, T::Num((next() << (60 + (r >> 12) % 4)) as i64), p),
            _ => op(Op::Add, var(r >> 14), op(Op::Mul, T::Num(next() as i64), op(Op::And, p, T::Num(1)))),
        }
    }

    #[test]
    fn product_noise_matches_evaluation() {
        crate::sched::in_default_run(|| {
            let mut h = 0x3c6e_f372_fe94_f82bu64;
            let mut changed = 0;
            for k in 0..400 {
                let t = noise_term(&mut h);
                for (bits, signed) in [(8, k % 2 == 1), (64, k % 2 == 1)] {
                    let (w, ty) = (Ctx::new(bits), NumType { bits, signed });
                    let r = simplify(&t, &w);
                    changed += (r != t) as u32;
                    let check = |x: u64, y: u64| {
                        let env = |v: &str| if v == "x" { x } else { y };
                        assert_eq!(eval(&t, ty, &env), eval(&r, ty, &env), "{t:?}\n{r:?}");
                    };
                    if bits == 8 {
                        (0..1u64 << 16).for_each(|p| check(p & 0xff, p >> 8));
                    } else {
                        for _ in 0..256 {
                            h ^= h << 13;
                            h ^= h >> 7;
                            h ^= h << 17;
                            check(h, h.rotate_left(29));
                        }
                    }
                }
            }
            assert!(changed > 200, "changed {changed}");
        })
    }

    /// A sum of a small product term `p`, used both alone and inside a larger candidate.
    fn nested_term(h: &mut u64) -> T {
        let op = |o: Op, a: T, b: T| T::Op(o, vec![a, b]);
        let mut next = || {
            *h ^= *h << 13;
            *h ^= *h >> 7;
            *h ^= *h << 17;
            *h
        };
        let r = next();
        let var = |r: u64| T::Var(if r & 1 == 0 { "x" } else { "y" }.into());
        let bit = |r: u64| {
            let v = if r >> 1 & 1 == 0 { var(r) } else { T::Op(Op::Not, vec![var(r)]) };
            let c = [1, 4, 5, -5, -2][(r >> 2) as usize % 5];
            op([Op::And, Op::Or][(r >> 5) as usize % 2], v, T::Num(c))
        };
        let p = op([Op::Sub, Op::Add][r as usize % 2], op(Op::Mul, bit(next()), bit(next())), op(Op::Mul, bit(next()), bit(next())));
        let ops = [Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor];
        let wrap = op(ops[(r >> 8) as usize % 5], p.clone(), [T::Num(0), T::Num(1), var(r >> 11)][(r >> 12) as usize % 3].clone());
        let inner = op(ops[(r >> 16) as usize % 5], op(ops[(r >> 20) as usize % 5], var(r >> 24), wrap), p.clone());
        op(ops[(r >> 28) as usize % 5], p, inner)
    }

    #[test]
    fn nested_candidates_match_exhaustive_check_at_8_bits() {
        crate::sched::in_default_run(|| {
            let w = Ctx::new(8);
            let mut h = 0x6a09_e667_f3bc_c908u64;
            let mut changed = 0;
            for k in 0..3000 {
                let ty = NumType { bits: 8, signed: k % 2 == 1 };
                let t = nested_term(&mut h);
                let r = simplify(&t, &w);
                if r == t {
                    continue;
                }
                changed += 1;
                for p in 0..1u64 << 16 {
                    let env = |v: &str| if v == "x" { p & 0xff } else { p >> 8 };
                    assert_eq!(eval(&t, ty, &env), eval(&r, ty, &env), "{t:?}\n{r:?}");
                }
            }
            assert!(changed > 300, "changed {changed}");
        })
    }

    /// Products whose low bits are fixed only by evaluation, under constant masks,
    /// constant multipliers and negated xors, at 8 bits on every input.
    #[test]
    fn evaluated_low_bits_match_exhaustive_check() {
        crate::sched::in_default_run(|| {
            let w = Ctx::new(8);
            let op = |o: Op, a: T, b: T| T::Op(o, vec![a, b]);
            let mut h = 0x5851_f42d_4c95_7f2du64;
            let mut changed = 0;
            for k in 0..600 {
                let mut next = || {
                    h ^= h << 13;
                    h ^= h >> 7;
                    h ^= h << 17;
                    h
                };
                let r = next();
                let var = |r: u64| T::Var(if r & 1 == 0 { "x" } else { "y" }.into());
                let lin = |r: u64| op([Op::Add, Op::Sub, Op::Xor, Op::And][(r >> 3) as usize % 4], var(r), op(Op::Mul, T::Num((r >> 8) as i64 % 5 - 2), var(r >> 1)));
                let p = op(Op::Mul, lin(next()), lin(next()));
                let p = if r >> 4 & 1 == 0 { p } else { op(Op::And, p, lin(next())) };
                let c = T::Num((next() >> 20) as i64 % 256 - 128);
                let t = match r >> 6 & 7 {
                    0 => op(Op::And, T::Op(Op::Neg, vec![p]), T::Num(-2)),
                    1 => op(Op::Xor, op(Op::Add, p, T::Num(1)), T::Num(1)),
                    2 => op(Op::Mul, c, p),
                    3 => op(Op::Mul, op(Op::Mul, c, lin(next())), p),
                    4 => T::Op(Op::Neg, vec![op(Op::Xor, op(Op::Mul, T::Num(1 << (r >> 9) % 4), p), c)]),
                    5 => op(Op::Or, p, T::Num(1)),
                    _ => op(Op::Add, var(r >> 12), op(Op::Mul, c, op(Op::And, p, T::Num(-2)))),
                };
                let ty = NumType { bits: 8, signed: k % 2 == 1 };
                let s = simplify_rebuilt(&t, &w);
                if s == t {
                    continue;
                }
                changed += 1;
                for q in 0..1u64 << 16 {
                    let env = |v: &str| if v == "x" { q & 0xff } else { q >> 8 };
                    assert_eq!(eval(&t, ty, &env), eval(&s, ty, &env), "{t:?}\n{s:?}");
                }
            }
            assert!(changed > 100, "changed {changed}");
        })
    }
}
