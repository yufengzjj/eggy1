//! Subterms with variable left shifts, such as `(y << (y & 63)) & 1`, are not
//! T-functions, but their low `m` bits depend only on the low `m` bits of their
//! leaves once every shift amount is known to be below `2^m`. A subterm whose bits
//! from `m` up are known is then a function of `m` bits per leaf: it is replaced by
//! a constant when all of them give one value, and otherwise by one of its few
//! values when the enclosing expression is proved not to change (`tfunc::equal_low`).

use crate::eval::{Term as T, size};
use crate::linear_mba::Width;
use std::collections::HashMap;

/// Most leaf bits enumerated for one subterm, and for a proof in context.
const MAX_BITS: u32 = 18;
const MAX_CONTEXT_BITS: u32 = 12;
const MAX_TRY: usize = 256;
const MAX_VALUES: usize = 4;
/// Evaluation steps per call, over all enumerations.
const BUDGET: u64 = 1 << 26;

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

fn lowmask(k: u32) -> u64 {
    if k >= 64 { u64::MAX } else { (1u64 << k) - 1 }
}

fn leaf_info(k0: u64, k1: u64, w: &Width) -> Info {
    let mut i = Info { k0, k1, need: 0, full: 0, det: true, shift: false };
    i.full = high(&i, w);
    i
}

/// Bits from which on every bit is known.
fn high(i: &Info, w: &Width) -> u32 {
    64 - (!(i.k0 | i.k1) & w.mask).leading_zeros()
}

fn known_low(a: &Info, b: &Info, f: impl Fn(u64, u64) -> u64, w: &Width) -> (u64, u64) {
    let l = (a.k0 | a.k1).trailing_ones().min((b.k0 | b.k1).trailing_ones()).min(w.w);
    let r = f(a.k1, b.k1) & lowmask(l);
    (!r & lowmask(l), r)
}

fn combine(op: &str, args: &[Info], w: &Width) -> Info {
    let m = w.mask;
    let a: Vec<Info> = args.iter().map(|i| if i.det { *i } else { leaf_info(i.k0, i.k1, w) }).collect();
    let tz = |i: &Info| lowmask(i.k0.trailing_ones().min(w.w));
    let max = |i: &Info| !i.k0 & m;
    let bound = |v: Option<u64>| v.filter(|v| *v <= m).map_or(0, |v| m & !lowmask(64 - v.leading_zeros()));
    let (x, y) = (a[0], a.get(1).copied().unwrap_or(a[0]));
    let need = a.iter().map(|i| i.need).max().unwrap();
    let shift = a.iter().any(|i| i.shift);
    let mut full = a.iter().map(|i| i.full).max().unwrap();
    let konst = |i: &Info| ((i.k0 | i.k1) & m == m).then_some(i.k1);
    let (k0, k1) = match op {
        "Not" => (x.k1, x.k0),
        "And" => (x.k0 | y.k0, x.k1 & y.k1),
        "Or" => (x.k0 & y.k0, x.k1 | y.k1),
        "Xor" => (x.k0 & y.k0 | x.k1 & y.k1, x.k0 & y.k1 | x.k1 & y.k0),
        "Neg" => known_low(&x, &x, |p, _| p.wrapping_neg(), w),
        "Sub" => {
            let (k0, k1) = known_low(&x, &y, u64::wrapping_sub, w);
            (k0 | bound((x.k1 >= max(&y)).then(|| max(&x) - y.k1)), k1)
        }
        "Add" => {
            let (k0, k1) = known_low(&x, &y, u64::wrapping_add, w);
            (k0 | bound(max(&x).checked_add(max(&y))), k1)
        }
        "Mul" => {
            let (k0, k1) = known_low(&x, &y, u64::wrapping_mul, w);
            let tzs = lowmask((tz(&x).trailing_ones() + tz(&y).trailing_ones()).min(w.w));
            if let Some((c, o)) = konst(&x).map(|c| (c, y)).or_else(|| konst(&y).map(|c| (c, x))) {
                full = full.min(o.need.max(w.w.saturating_sub(c.trailing_zeros())));
            }
            (k0 | tzs | bound(max(&x).checked_mul(max(&y))), k1)
        }
        "Shl" if (y.k0 | y.k1) & m == m => match y.k1 {
            s if s >= w.w as u64 => (m, 0),
            s => {
                full = full.min(x.need.max(w.w - s as u32));
                ((x.k0 << s | lowmask(s as u32)) & m, x.k1 << s & m)
            }
        },
        "Shl" => {
            let mut i = Info { k0: tz(&x), k1: 0, need: need.max(y.full), full, det: y.full <= MAX_BITS, shift: true };
            i.full = i.full.min(i.need.max(high(&i, w)));
            return i;
        }
        _ => return Info { k0: 0, k1: 0, need: 0, full: w.w, det: false, shift: false },
    };
    let mut i = Info { k0: k0 & m, k1: k1 & m, need, full, det: true, shift };
    i.full = i.full.min(need.max(high(&i, w)));
    i
}

fn info(t: &T, w: &Width) -> Info {
    match t {
        T::Var(_) => leaf_info(0, 0, w),
        T::Num(c) => leaf_info(!(*c as u64) & w.mask, *c as u64 & w.mask, w),
        T::Op(op, a) => combine(op, &a.iter().map(|x| info(x, w)).collect::<Vec<_>>(), w),
    }
}

enum Op {
    Leaf(usize),
    Const(u64),
    Un(fn(u64) -> u64),
    Bin(fn(u64, u64, u32) -> u64),
}

/// `t` as a stack program over its leaves: variables and subterms that are not `det`.
struct Prog {
    ops: Vec<Op>,
    leaves: Vec<T>,
    mask: u64,
    w: u32,
}

impl Prog {
    fn new(t: &T, w: &Width) -> Prog {
        let mut p = Prog { ops: Vec::new(), leaves: Vec::new(), mask: w.mask, w: w.w };
        p.compile(t, w);
        p
    }

    fn leaf(&mut self, t: &T) {
        let i = self.leaves.iter().position(|l| l == t).unwrap_or_else(|| {
            self.leaves.push(t.clone());
            self.leaves.len() - 1
        });
        self.ops.push(Op::Leaf(i));
    }

    fn compile(&mut self, t: &T, w: &Width) -> Info {
        let T::Op(op, a) = t else {
            if let T::Num(c) = t {
                self.ops.push(Op::Const(*c as u64 & w.mask));
            } else {
                self.leaf(t);
            }
            return info(t, w);
        };
        let start = self.ops.len();
        let infos: Vec<Info> = a.iter().map(|x| self.compile(x, w)).collect();
        let i = combine(op, &infos, w);
        if !i.det {
            self.ops.truncate(start);
            self.leaf(t);
            return i;
        }
        self.ops.push(match op.as_str() {
            "Not" => Op::Un(|x| !x),
            "Neg" => Op::Un(u64::wrapping_neg),
            "Add" => Op::Bin(|x, y, _| x.wrapping_add(y)),
            "Sub" => Op::Bin(|x, y, _| x.wrapping_sub(y)),
            "Mul" => Op::Bin(|x, y, _| x.wrapping_mul(y)),
            "And" => Op::Bin(|x, y, _| x & y),
            "Or" => Op::Bin(|x, y, _| x | y),
            "Xor" => Op::Bin(|x, y, _| x ^ y),
            _ => Op::Bin(|x, y, w| if y >= w as u64 { 0 } else { x << y }),
        });
        i
    }

    fn run(&self, leaves: &[u64], stack: &mut Vec<u64>) -> u64 {
        stack.clear();
        for op in &self.ops {
            let v = match *op {
                Op::Leaf(i) => leaves[i],
                Op::Const(c) => c,
                Op::Un(f) => f(stack.pop().unwrap()),
                Op::Bin(f) => {
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

struct Cand {
    m: u32,
    values: Vec<u64>,
    prog: Prog,
}

struct Pass<'a> {
    w: &'a Width,
    cands: HashMap<T, Cand>,
    budget: u64,
}

impl Pass<'_> {
    /// Distinct values of a `det` subterm whose bits from `m` up are known, if at most `MAX_VALUES`.
    fn values(&mut self, t: &T, m: u32) -> Option<(Vec<u64>, Prog)> {
        let prog = Prog::new(t, self.w);
        let n = prog.leaves.len();
        if n as u32 * m > MAX_BITS {
            return None;
        }
        let cost = (1u64 << (n as u32 * m)) * prog.ops.len() as u64;
        self.budget = self.budget.checked_sub(cost)?;
        let mut out = Vec::new();
        let mut stack = Vec::new();
        for low in assignments(n, m) {
            let v = prog.run(&low, &mut stack);
            if !out.contains(&v) {
                if out.len() == MAX_VALUES {
                    return None;
                }
                out.push(v);
            }
        }
        Some((out, prog))
    }

    fn fold(&mut self, t: &T) -> (T, Info) {
        let w = self.w;
        let T::Op(op, a) = t else { return (t.clone(), info(t, w)) };
        let (args, infos): (Vec<T>, Vec<Info>) = a.iter().map(|x| self.fold(x)).unzip();
        let node = T::Op(op.clone(), args);
        let i = combine(op, &infos, w);
        let konst = |v: u64| (T::Num(w.signed(v)), info(&T::Num(w.signed(v)), w));
        if (i.k0 | i.k1) & w.mask == w.mask {
            return konst(i.k1);
        }
        if i.det && i.shift && size(&node) <= MAX_TRY {
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
        let mut unknown = n as u32 * m > MAX_CONTEXT_BITS || size(t) > MAX_TRY;
        if !unknown {
            let names: Vec<String> = (0..found.len()).map(|i| format!("\u{4}{i}")).collect();
            let abs = replace(t, &found, &names.iter().map(|s| T::Var(s.clone())).collect::<Vec<_>>());
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
                    let Some(budget) = self.budget.checked_sub(cost) else {
                        unknown = true;
                        break;
                    };
                    self.budget = budget;
                    let num = T::Num(self.w.signed(v));
                    let g = replace(&abs, &[T::Var(names[i].clone())], std::slice::from_ref(&num));
                    match crate::tfunc::equal_low(&abs, &g, &all, n, m, &extra, self.w) {
                        Some(true) => return self.context(&replace(t, std::slice::from_ref(c), &[num])),
                        Some(false) => {}
                        None => unknown = true,
                    }
                }
            }
        }
        if !unknown {
            return t.clone();
        }
        T::Op(op.clone(), a.iter().map(|x| self.context(x)).collect())
    }
}

fn replace(t: &T, from: &[T], to: &[T]) -> T {
    if let Some(i) = from.iter().position(|f| f == t) {
        return to[i].clone();
    }
    match t {
        T::Op(op, a) => T::Op(op.clone(), a.iter().map(|x| replace(x, from, to)).collect()),
        _ => t.clone(),
    }
}

/// `t` with subterms determined by the low bits of their leaves folded, where that
/// needs a variable left shift (or is a constant by known bits).
pub(crate) fn simplify(t: &T, w: &Width) -> T {
    let mut p = Pass { w, cands: HashMap::new(), budget: BUDGET };
    let (r, _) = p.fold(t);
    if p.cands.is_empty() { r } else { p.context(&r) }
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
        let op = ["Add", "Sub", "And", "Or", "Xor", "Not", "Neg", "Mul", "Shl", "Shl", "Mask", "Shr"][(r >> 16) as usize % 12];
        match op {
            "Not" | "Neg" => T::Op(op.into(), vec![sub(h)]),
            "Shl" if r >> 30 & 1 == 0 => T::Op(op.into(), vec![sub(h), T::Op("And".into(), vec![sub(h), T::Num(7)])]),
            "Mask" => T::Op("And".into(), vec![sub(h), T::Num((r >> 24) as i64 % 4 + 1)]),
            _ => T::Op(op.into(), vec![sub(h), sub(h)]),
        }
    }

    /// A linear expression of `x`, `y` and a masked variable shift of random terms.
    fn context_term(h: &mut u64) -> T {
        let op = |o: &str, a: T, b: T| T::Op(o.into(), vec![a, b]);
        let var = |r: u64| T::Var(if r & 1 == 0 { "x" } else { "y" }.into());
        let s = random_term(h, 2);
        let amount = match *h >> 40 & 3 {
            0 => s.clone(),
            1 => T::Op("Neg".into(), vec![s.clone()]),
            2 => T::Op("Not".into(), vec![s.clone()]),
            _ => random_term(h, 2),
        };
        let shifted = op("Shl", s, op("And", amount, T::Num(7)));
        let t = op("And", shifted, T::Num((*h >> 20) as i64 % 3 + 1));
        let ops = ["Add", "Sub", "And", "Or", "Xor"];
        let inner = op(ops[(*h >> 24) as usize % 5], var(*h >> 28), t);
        op(ops[(*h >> 32) as usize % 5], var(*h >> 36), inner)
    }

    #[test]
    fn matches_exhaustive_check_at_8_bits() {
        let w = Width::new(8);
        let mut h = 0x9e37_79b9_7f4a_7c15u64;
        let (mut changed, mut in_context) = (0, 0);
        for k in 0..500 {
            let ty = NumType { bits: 8, signed: k % 2 == 1 };
            let t = if k < 200 { random_term(&mut h, 4) } else { context_term(&mut h) };
            let mut p = Pass { w: &w, cands: HashMap::new(), budget: BUDGET };
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
    }
}
