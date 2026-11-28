//! Differential fuzzer: simplifies random and MBA-obfuscated expressions and checks each
//! output against its input by evaluation (exhaustive where the input space is at most
//! 2^16 points). Each case runs in a child process (this binary with `--one`), so panics,
//! stack overflows, hangs and memory blow-ups only fail that case; failures are shrunk
//! and written to `-o` as `kind<TAB>type<TAB>status<TAB>infix<TAB>detail` lines, which
//! `--replay` reruns.

use clap::Parser;
use eggy1::eval::{self, NumType, Op, Term};
use eggy1::expr_convert::{egglog_to_infix, infix_to_egglog};
use eggy1::lang::lexer::quoted;
use eggy1::{Cli, simplify};
use std::collections::BTreeMap;
use std::io::{BufRead, Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const TYPES: [&str; 8] = ["i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8"];
/// Largest term `obfuscate` builds.
const MAX_OBF_SIZE: usize = 500;
/// `mutate` needs `--corpus` and is only run when named.
const KINDS: [&str; 13] = ["rand", "big", "chain", "mba", "linear", "shift", "select", "wide", "small8", "magic", "poly", "semi", "shared"];

#[derive(Parser, Clone)]
struct Args {
    /// Numeric types, comma-separated, or `all`.
    #[arg(short, long, default_value = "all")]
    num_type: String,
    /// Generator kinds, comma-separated, or `all` (see `KINDS`).
    #[arg(short, long, default_value = "all")]
    kind: String,
    /// Number of cases.
    #[arg(short, long, default_value_t = 1000)]
    cases: usize,
    #[arg(short, long, default_value_t = 1)]
    seed: u64,
    /// Parallel cases (default: number of CPUs).
    #[arg(short, long)]
    jobs: Option<usize>,
    /// Seconds per case.
    #[arg(short, long, default_value_t = 10.0)]
    timeout: f64,
    /// Resident memory limit per case in MB (Linux only).
    #[arg(long, default_value_t = 1500)]
    mem_mb: u64,
    /// Failure log (appended).
    #[arg(short, long, default_value = "fuzz-fails.txt")]
    out: String,
    /// Child runs spent shrinking each failure.
    #[arg(long, default_value_t = 200)]
    shrink: usize,
    /// Do not report timeouts of inputs larger than this (large random terms often time out).
    #[arg(long, default_value_t = 80)]
    report_timeout_size: usize,
    /// Rerun the cases of a failure log (or lines `type<TAB>infix`) instead of generating.
    #[arg(long)]
    replay: Option<String>,
    /// Dataset files (`input, groundtruth` lines, as for the benchmark) whose inputs kind
    /// `mutate` mutates, comma-separated.
    #[arg(long, default_value = "")]
    corpus: String,
    /// Check only the pre-pass rebuilds (`(parse s) | (prepass prepass_steps)` and `polish`), without the rules.
    #[arg(long)]
    prepass: bool,
    /// Child mode: read the type and an egglog term from stdin, print one result line.
    #[arg(long, hide = true)]
    one: bool,
}

fn main() {
    let args = Args::parse();
    if args.one {
        run_one();
    } else {
        run_all(&args);
    }
}

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        let mut r = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0xd1b5_4a32_d192_ed03);
        r.next();
        r
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
    fn chance(&mut self, p: f64) -> bool {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64 <= p
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

fn op2(op: Op, a: Term, b: Term) -> Term {
    Term::Op(op, vec![a, b])
}
fn op1(op: Op, a: Term) -> Term {
    Term::Op(op, vec![a])
}
fn num(v: i64) -> Term {
    Term::Num(v)
}

struct Gen {
    ty: NumType,
    vars: Vec<String>,
    r: Rng,
    /// Allow `/ % >> <<` and mulhi.
    opaque: bool,
}

impl Gen {
    fn w(&self) -> u32 {
        self.ty.bits
    }

    /// A value of the type in one of its representations (sign- or zero-extended).
    fn repr(&mut self, v: u64) -> Term {
        let v = v & self.ty.mask();
        let sh = 64 - self.w();
        let s = ((v << sh) as i64) >> sh;
        match self.r.below(10) {
            0..=5 => num(s),
            6..=8 => num(v as i64),
            // garbage above the width
            _ => num((v | (self.r.next() << (self.w() % 64)) * (self.w() < 64) as u64) as i64),
        }
    }

    fn edge(&mut self) -> u64 {
        let w = self.w();
        let k = self.r.below(w as usize) as u32;
        let p = 1u64 << k;
        let min = 1u64 << (w - 1);
        let runs = {
            let lo = self.r.below(w as usize) as u32;
            let len = 1 + self.r.below((w - lo) as usize) as u32;
            (if len == 64 { u64::MAX } else { (1u64 << len) - 1 }) << lo
        };
        match self.r.below(17) {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            3 => 2,
            4 => min,
            5 => min - 1,
            6 => min + 1,
            7 => p,
            8 => p.wrapping_sub(1),
            9 => p + 1,
            10 => p.wrapping_neg(),
            11 => runs,
            12 => !runs,
            13 => 0x5555_5555_5555_5555,
            14 => self.r.below(16) as u64,
            15 => (self.r.below(16) as u64).wrapping_neg(),
            _ => self.r.next(),
        }
    }

    fn konst(&mut self) -> Term {
        let v = self.edge();
        self.repr(v)
    }

    fn var(&mut self) -> Term {
        let i = self.r.below(self.vars.len());
        Term::Var(self.vars[i].clone())
    }

    fn leaf(&mut self) -> Term {
        if self.r.chance(0.7) {
            self.var()
        } else if (self.opaque || self.r.chance(0.2)) && self.r.chance(0.1) {
            // A constant whose value depends on the signedness.
            let op = *self.r.pick(&[Op::Div, Op::Mod, Op::Shr, Op::Mulhi]);
            let a = self.konst();
            let b = if op == Op::Shr { num(self.r.below(self.w() as usize) as i64) } else { self.konst() };
            op2(op, a, if matches!(b, Term::Num(0)) { num(3) } else { b })
        } else {
            self.konst()
        }
    }

    /// A shift amount: a constant (possibly at least the width), a variable, or a masked one.
    fn amount(&mut self, size: usize) -> Term {
        let w = self.w() as i64;
        match self.r.below(9) {
            0 | 1 => num(self.r.below(w as usize) as i64),
            2 => num(w + self.r.below(3) as i64 - 1),
            3 => {
                let d = self.r.below(3) as u64;
                self.repr((w as u64).wrapping_neg().wrapping_add(d))
            }
            4 => {
                let a = self.random(size.max(1));
                op2(Op::And, a, num(w - 1))
            }
            5 => {
                let a = self.var();
                op1(Op::Not, a)
            }
            6 => {
                let a = self.var();
                op2(Op::And, op1(Op::Not, a), num(w - 1))
            }
            _ => self.random(size.max(1)),
        }
    }

    /// A random term of about `size` nodes over all operations.
    fn random(&mut self, size: usize) -> Term {
        if size <= 1 {
            return self.leaf();
        }
        let unary = self.r.chance(0.15);
        if unary || size == 2 {
            let a = self.random(size - 1);
            return op1(if self.r.chance(0.5) { Op::Not } else { Op::Neg }, a);
        }
        let ops: &[Op] = if self.opaque {
            &[Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor, Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor, Op::Mul, Op::Shl, Op::Shr, Op::Div, Op::Mod, Op::Mulhi]
        } else {
            &[Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor]
        };
        let op = *self.r.pick(ops);
        let left = 1 + self.r.below(size - 2);
        let right = size - 1 - left;
        match op {
            Op::Shl | Op::Shr => {
                let a = self.random(left);
                let b = self.amount(right);
                op2(op, a, b)
            }
            Op::Div | Op::Mod if self.r.chance(0.5) => {
                let a = self.random(left);
                let mut d = self.konst();
                if let Term::Num(0) = d {
                    d = num(3);
                }
                op2(op, a, d)
            }
            _ => {
                let a = self.random(left);
                let b = self.random(right);
                op2(op, a, b)
            }
        }
    }

    /// A deep left- or right-leaning chain.
    fn chain(&mut self, depth: usize) -> Term {
        let mut t = self.leaf();
        for _ in 0..depth {
            let other = if self.r.chance(0.8) { self.leaf() } else { self.random(3) };
            t = match self.r.below(10) {
                0 => op1(Op::Not, t),
                1 => op1(Op::Neg, t),
                2 if self.opaque => op2(Op::Shl, t, num(self.r.below(3) as i64)),
                _ => {
                    let op = *self.r.pick(&[Op::Add, Op::Sub, Op::Xor, Op::And, Op::Or, Op::Mul, Op::Add, Op::Xor]);
                    if self.r.chance(0.5) { op2(op, t, other) } else { op2(op, other, t) }
                }
            };
        }
        t
    }

    /// A term that is zero for every value of its variables.
    fn zero(&mut self) -> Term {
        let p = if self.r.chance(0.8) { self.var() } else { self.random(3) };
        let q = if self.r.chance(0.8) { self.var() } else { self.random(3) };
        let (a, o, x) = (op2(Op::And, p.clone(), q.clone()), op2(Op::Or, p.clone(), q.clone()), op2(Op::Xor, p.clone(), q.clone()));
        match self.r.below(6) {
            0 => op2(Op::Sub, op2(Op::Sub, o, a), x),
            1 => op2(Op::Sub, op2(Op::Sub, op2(Op::Add, p, q), o), a),
            2 => op2(Op::Sub, op2(Op::Sub, p.clone(), a), op2(Op::And, p, op1(Op::Not, q))),
            3 => op2(Op::Add, op2(Op::Sub, x, o), a),
            4 => op2(Op::Add, op2(Op::Add, op1(Op::Not, p.clone()), p), num(1)),
            _ => op2(Op::Sub, op2(Op::Add, op2(Op::And, p.clone(), op1(Op::Not, q.clone())), op2(Op::And, op1(Op::Not, p), q)), x),
        }
    }

    /// `t` with one MBA identity applied at its root.
    fn obf_node(&mut self, t: Term) -> Term {
        use Op::*;
        let not = |x: &Term| op1(Not, x.clone());
        if self.r.chance(0.15) {
            let c = self.konst();
            let z = self.zero();
            return op2(Add, t, op2(Mul, c, z));
        }
        if self.r.chance(0.08) {
            let k = self.konst();
            return match self.r.below(3) {
                0 => op2(Xor, op2(Xor, t, k.clone()), k),
                1 => op2(Sub, op2(Add, t, k.clone()), k),
                _ => {
                    let k = (self.r.next() | 1) & self.ty.mask();
                    let inv = inverse(k) & self.ty.mask();
                    op2(Mul, self.repr(inv), op2(Mul, t, self.repr(k)))
                }
            };
        }
        let Term::Op(op, a) = &t else { return t };
        let x = a[0].clone();
        let y = a.get(1).cloned().unwrap_or(num(0));
        let two = || num(2);
        match (op, self.r.below(4)) {
            (Add, 0) => op2(Add, op2(Xor, x.clone(), y.clone()), op2(Mul, two(), op2(And, x, y))),
            (Add, 1) => op2(Add, op2(Or, x.clone(), y.clone()), op2(And, x, y)),
            (Add, 2) => op2(Sub, op2(Mul, two(), op2(Or, x.clone(), y.clone())), op2(Xor, x, y)),
            (Add, _) => op2(Sub, op2(Sub, x, not(&y)), num(1)),
            (Sub, 0) => op2(Sub, op2(Xor, x.clone(), y.clone()), op2(Mul, two(), op2(And, not(&x), y))),
            (Sub, 1) => op2(Sub, op2(And, x.clone(), not(&y)), op2(And, not(&x), y)),
            (Sub, 2) => op2(Add, op2(Add, x, not(&y)), num(1)),
            (Sub, _) => op2(Add, op2(Xor, x.clone(), op1(Neg, y.clone())), op2(Mul, two(), op2(And, x, op1(Neg, y)))),
            (Xor, 0) => op2(Sub, op2(Or, x.clone(), y.clone()), op2(And, x, y)),
            (Xor, 1) => op2(Sub, op2(Add, x.clone(), y.clone()), op2(Mul, two(), op2(And, x, y))),
            (Xor, _) => op2(Or, op2(And, x.clone(), not(&y)), op2(And, not(&x), y)),
            (And, 0) => op2(Sub, op2(Add, x.clone(), y.clone()), op2(Or, x, y)),
            (And, 1) => op1(Not, op2(Or, not(&x), not(&y))),
            (And, 2) => op2(Sub, op2(Or, not(&x), y), not(&x)),
            (And, _) => op2(Sub, op2(Or, x.clone(), y.clone()), op2(Xor, x, y)),
            (Or, 0) => op2(Sub, op2(Add, x.clone(), y.clone()), op2(And, x, y)),
            (Or, 1) => op2(Add, op2(Xor, x.clone(), y.clone()), op2(And, x, y)),
            (Or, 2) => op1(Not, op2(And, not(&x), not(&y))),
            (Or, _) => op2(Add, op2(And, x, not(&y)), y),
            (Not, 0 | 1) => op2(Sub, op1(Neg, x), num(1)),
            (Not, _) => op2(Sub, num(-1), x),
            (Neg, 0 | 1) => op2(Add, not(&x), num(1)),
            (Neg, _) => op1(Not, op2(Sub, x, num(1))),
            (Mul, 0 | 1) => op2(
                Add,
                op2(Mul, op2(And, x.clone(), y.clone()), op2(Or, x.clone(), y.clone())),
                op2(Mul, op2(And, x.clone(), not(&y)), op2(And, not(&x), y)),
            ),
            (Shl, 0) if matches!(y, Term::Num(k) if (0..self.w() as i64).contains(&k)) => {
                let Term::Num(k) = y else { unreachable!() };
                op2(Mul, x, num(1i64.wrapping_shl(k as u32)))
            }
            _ => t,
        }
    }

    /// Applies identities at random nodes, bottom up, `rounds` times.
    fn obfuscate(&mut self, t: Term, p: f64, rounds: usize) -> Term {
        let mut t = t;
        for _ in 0..rounds {
            let mut room = MAX_OBF_SIZE as isize - eval::size(&t) as isize;
            t = self.obf_walk(t, p, &mut room);
        }
        t
    }

    /// Identities duplicate operands, so `room` (nodes that may still be added) bounds the growth.
    fn obf_walk(&mut self, t: Term, p: f64, room: &mut isize) -> Term {
        let t = match t {
            Term::Op(op, a) => Term::Op(op, a.into_iter().map(|x| self.obf_walk(x, p, room)).collect()),
            other => other,
        };
        if *room <= 0 || !self.r.chance(p) {
            return t;
        }
        let before = eval::size(&t) as isize;
        let r = self.obf_node(t.clone());
        let grow = eval::size(&r) as isize - before;
        if grow > *room {
            return t;
        }
        *room -= grow;
        r
    }

    fn small_target(&mut self) -> Term {
        let size = 1 + self.r.below(8);
        self.random(size)
    }

    /// A random purely bitwise term over the variables.
    fn bitwise(&mut self, size: usize, consts: bool) -> Term {
        if size <= 1 {
            return if consts && self.r.chance(0.15) { self.konst() } else { self.var() };
        }
        if size == 2 || self.r.chance(0.15) {
            let a = self.bitwise(size - 1, consts);
            return op1(Op::Not, a);
        }
        let op = *self.r.pick(&[Op::And, Op::Or, Op::Xor]);
        let left = 1 + self.r.below(size - 2);
        let a = self.bitwise(left, consts);
        let b = self.bitwise(size - 1 - left, consts);
        op2(op, a, b)
    }

    /// A sum of constant multiples of terms.
    fn linear(&mut self, terms: Vec<Term>) -> Term {
        let mut t: Option<Term> = None;
        for b in terms {
            let c = if self.r.chance(0.6) { num(self.r.below(9) as i64 - 4) } else { self.konst() };
            let term = op2(Op::Mul, c, b);
            t = Some(match t {
                None => term,
                Some(s) if self.r.chance(0.5) => op2(Op::Sub, s, term),
                Some(s) => op2(Op::Add, s, term),
            });
        }
        let t = t.unwrap_or(num(0));
        if self.r.chance(0.4) {
            let k = self.konst();
            op2(Op::Add, t, k)
        } else {
            t
        }
    }

    fn case(&mut self, kind: &str) -> Term {
        let w = self.w() as i64;
        match kind {
            "rand" | "small8" => {
                let cap = if self.r.chance(0.7) { 12 } else { 40 };
                let size = 1 + self.r.below(cap);
                self.random(size)
            }
            "big" => {
                let size = 60 + self.r.below(240);
                self.random(size)
            }
            "chain" => {
                let depth = 20 + self.r.below(180);
                self.chain(depth)
            }
            "mba" => {
                let t = self.small_target();
                let p = 0.2 + 0.6 * self.r.below(4) as f64 / 4.0;
                let rounds = 1 + self.r.below(3);
                self.obfuscate(t, p, rounds)
            }
            "linear" => {
                let n = 1 + self.r.below(5);
                let terms: Vec<Term> = (0..n).map(|_| {
                    let s = 1 + self.r.below(6);
                    { let c = self.r.chance(0.3); self.bitwise(s, c) }
                }).collect();
                let target = self.linear(terms);
                let zeros = self.r.below(4);
                let mut t = target;
                for _ in 0..zeros {
                    let c = num(self.r.below(7) as i64 - 3);
                    let z = self.zero();
                    t = op2(Op::Add, t, op2(Op::Mul, c, z));
                }
                if self.r.chance(0.5) { self.obfuscate(t, 0.3, 1) } else { t }
            }
            "shift" => {
                let x = if self.r.chance(0.6) { self.var() } else { self.random(4) };
                let y = self.var();
                let s = match self.r.below(8) {
                    0 => op2(Op::And, y, num(w - 1)),
                    1 => op1(Op::Not, y),
                    2 => op2(Op::And, op1(Op::Not, y), num(w - 1)),
                    3 => num(self.r.below(w as usize + 2) as i64),
                    4 => op2(Op::Add, op2(Op::And, y, num(w / 2 - 1)), num(self.r.below(w as usize / 2) as i64)),
                    5 => op2(Op::Sub, num(w - 1), op2(Op::And, y, num(w - 1))),
                    6 => op2(Op::And, y, num(self.r.below(2 * w as usize) as i64)),
                    _ => self.amount(3),
                };
                let sh = if self.r.chance(0.5) { Op::Shl } else { Op::Shr };
                let mut t = op2(sh, x.clone(), s.clone());
                match self.r.below(6) {
                    0 => {
                        let back = if sh == Op::Shl { Op::Shr } else { Op::Shl };
                        t = op2(back, t, s);
                    }
                    1 => t = op2(Op::And, t, self.konst()),
                    2 => {
                        let z = self.random(3);
                        t = op2(*self.r.pick(&[Op::Add, Op::Xor, Op::Or, Op::Sub]), t, z);
                    }
                    3 => {
                        let u = self.random(3);
                        let s2 = self.amount(2);
                        t = op2(Op::Add, t, op2(*self.r.pick(&[Op::Shl, Op::Shr]), u, s2));
                    }
                    _ => {}
                }
                if self.r.chance(0.5) { { let n = 1 + self.r.below(2); self.obfuscate(t, 0.4, n) } } else { t }
            }
            "select" => {
                let v = self.var();
                let k = self.r.below(w as usize) as i64;
                let bit = match self.r.below(4) {
                    0 => op2(Op::And, v.clone(), num(1)),
                    1 => op2(Op::And, op2(Op::Shr, v.clone(), num(k)), num(1)),
                    2 => op2(Op::And, v.clone(), num(1i64.wrapping_shl(k as u32))),
                    _ => {
                        let c = self.konst();
                        op2(Op::And, op2(Op::Add, v.clone(), c), num(3))
                    }
                };
                let n1 = 1 + self.r.below(5);
                let e1 = self.random(n1);
                let n2 = 1 + self.r.below(5);
                let e2 = self.random(n2);
                let t = match self.r.below(5) {
                    0 => op2(Op::Mul, bit, e1),
                    1 => op2(Op::Add, op2(Op::Mul, bit.clone(), e1), op2(Op::Mul, op2(Op::Xor, bit, num(1)), e2)),
                    2 => {
                        // Hikari: (1 & ~y)*(-y & -2) + (-y | 1)*(y & 1) = -y
                        let y = v.clone();
                        op2(
                            Op::Add,
                            op2(Op::Mul, op2(Op::And, num(1), op1(Op::Not, y.clone())), op2(Op::And, op1(Op::Neg, y.clone()), num(-2))),
                            op2(Op::Mul, op2(Op::Or, op1(Op::Neg, y.clone()), num(1)), op2(Op::And, y, num(1))),
                        )
                    }
                    3 => {
                        // (a | K)*(a & K) + (a & ~K)*(~a & K) = a*K
                        let a = if self.r.chance(0.5) { v.clone() } else { e1 };
                        let k = self.konst();
                        op2(
                            Op::Add,
                            op2(Op::Mul, op2(Op::Or, a.clone(), k.clone()), op2(Op::And, a.clone(), k.clone())),
                            op2(Op::Mul, op2(Op::And, a.clone(), op1(Op::Not, k.clone())), op2(Op::And, op1(Op::Not, a), k)),
                        )
                    }
                    _ => op2(Op::Mul, bit, op2(Op::Add, e1, e2)),
                };
                if self.r.chance(0.5) { self.obfuscate(t, 0.3, 1) } else { t }
            }
            "wide" => {
                let n = 1 + self.r.below(4);
                let terms: Vec<Term> = (0..n).map(|_| {
                    let s = 4 + self.r.below(14);
                    { let c = self.r.chance(0.3); self.bitwise(s, c) }
                }).collect();
                let mut t = if n == 1 && self.r.chance(0.5) { terms.into_iter().next().unwrap() } else { self.linear(terms) };
                if self.r.chance(0.3) {
                    let p = self.random(3);
                    t = op2(Op::Add, t, op2(Op::Mul, p, self.var()));
                }
                if self.r.chance(0.4) { self.obfuscate(t, 0.25, 1) } else { t }
            }
            "magic" => self.magic(),
            "poly" => {
                // Sums of products of small linear and bitwise terms (polynomial MBA).
                let n = 1 + self.r.below(3);
                let prods: Vec<Term> = (0..n)
                    .map(|_| {
                        let k = if self.r.chance(0.8) { 2 } else { 2 + self.r.below(2) };
                        let mut p: Option<Term> = None;
                        for _ in 0..k {
                            let f = match self.r.below(3) {
                                0 => {
                                    let s = 1 + self.r.below(4);
                                    let c = self.r.chance(0.3);
                                    self.bitwise(s, c)
                                }
                                1 => {
                                    let a = self.var();
                                    let b = self.leaf();
                                    op2(*self.r.pick(&[Op::Add, Op::Sub]), a, b)
                                }
                                _ => self.var(),
                            };
                            p = Some(match p {
                                None => f,
                                Some(q) => op2(Op::Mul, q, f),
                            });
                        }
                        p.unwrap()
                    })
                    .collect();
                let mut terms = prods;
                for _ in 0..self.r.below(3) {
                    let s = 1 + self.r.below(4);
                    terms.push(self.bitwise(s, false));
                }
                let t = self.linear(terms);
                if self.r.chance(0.5) { self.obfuscate(t, 0.25, 1) } else { t }
            }
            "semi" => {
                // Bitwise terms with constant masks in linear combinations (semi-linear MBA).
                let n = 1 + self.r.below(4);
                let terms: Vec<Term> = (0..n)
                    .map(|_| {
                        let s = 2 + self.r.below(6);
                        let mut b = self.bitwise(s, true);
                        if self.r.chance(0.5) {
                            let k = self.konst();
                            b = op2(*self.r.pick(&[Op::And, Op::Or, Op::Xor]), b, k);
                        }
                        b
                    })
                    .collect();
                let t = self.linear(terms);
                if self.r.chance(0.4) { self.obfuscate(t, 0.25, 1) } else { t }
            }
            "shared" => {
                // A few subterms used many times, so the term is a DAG with heavy sharing.
                let pool: Vec<Term> = (0..2 + self.r.below(3))
                    .map(|_| {
                        let s = 2 + self.r.below(8);
                        self.random(s)
                    })
                    .collect();
                let mut t = self.r.pick(&pool).clone();
                for _ in 0..3 + self.r.below(12) {
                    let x = self.r.pick(&pool).clone();
                    let op = *self.r.pick(&[Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor]);
                    t = if self.r.chance(0.5) { op2(op, t, x) } else { op2(op, x, t) };
                }
                t
            }
            _ => panic!("unknown kind {kind}"),
        }
    }

    /// Compiler division sequences, sometimes with a multiplier or shift off by one.
    fn magic(&mut self) -> Term {
        let w = self.w();
        let n = self.var();
        let cap = if self.r.chance(0.5) { 30 } else { 100_000 };
        let d = 2 + self.r.below(cap) as i64;
        let skew = |r: &mut Rng| if r.chance(0.3) { r.below(3) as i64 - 1 } else { 0 };
        let (ds, dm) = (skew(&mut self.r), skew(&mut self.r));
        let t = if self.ty.signed {
            let Some((m, s, add)) = eggy1::magic_s(d, w) else { return op2(Op::Div, n, num(d)) };
            let m = num((m as i64).wrapping_add(dm));
            let s = (s as i64 + ds).max(0);
            let mut q = op2(Op::Mulhi, m, n.clone());
            if add {
                q = op2(Op::Add, q, n.clone());
            }
            if s > 0 {
                q = op2(Op::Shr, q, num(s));
            }
            let sign = op2(Op::Shr, n.clone(), num(w as i64 - 1));
            if self.r.chance(0.5) { op2(Op::Add, q, op2(Op::And, sign, num(1))) } else { op2(Op::Sub, q, sign) }
        } else {
            let Some((m, s, add)) = eggy1::magic_u(d, w) else { return op2(Op::Div, n, num(d)) };
            let mm = num(((m & ((1u128 << w) - 1)) as i64).wrapping_add(dm));
            let s = (s as i64 + ds).max(0);
            let q = op2(Op::Mulhi, mm, n.clone());
            if add {
                let t = op2(Op::Add, op2(Op::Shr, op2(Op::Sub, n.clone(), q.clone()), num(1)), q);
                op2(Op::Shr, t, num((s - 1).max(0)))
            } else if s > 0 {
                op2(Op::Shr, q, num(s))
            } else {
                q
            }
        };
        match self.r.below(3) {
            0 => op2(Op::Sub, n, op2(Op::Mul, t, num(d))),
            _ => t,
        }
    }
}

impl Gen {
    /// `t` with one random subterm changed: a constant or variable replaced, an operation
    /// swapped, a subterm wrapped in an operation or replaced by a small random term.
    fn mutate(&mut self, t: Term) -> Term {
        let n = eval::size(&t);
        let i = self.r.below(n);
        let Some(sub) = subterm(&t, &mut i.clone()) else { return t };
        let new = match (&sub, self.r.below(5)) {
            (Term::Num(_), _) => self.konst(),
            (Term::Var(_), 0) => self.konst(),
            (Term::Var(_), 1) => self.random(3),
            (Term::Var(_), _) => self.var(),
            (Term::Op(op, a), 0 | 1) if a.len() == 2 => {
                let ops: &[Op] = if self.opaque {
                    &[Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor, Op::Shl, Op::Shr, Op::Div, Op::Mod, Op::Mulhi]
                } else {
                    &[Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor]
                };
                let o = *self.r.pick(ops);
                let o = if o == *op { Op::Xor } else { o };
                Term::Op(o, a.clone())
            }
            (_, 2) => {
                let l = self.leaf();
                let ops = [Op::Add, Op::Sub, Op::Mul, Op::And, Op::Or, Op::Xor];
                if self.opaque && self.r.chance(0.3) {
                    let s = self.amount(2);
                    op2(*self.r.pick(&[Op::Shl, Op::Shr]), sub.clone(), s)
                } else {
                    op2(*self.r.pick(&ops), sub.clone(), l)
                }
            }
            (_, 3) => op1(*self.r.pick(&[Op::Not, Op::Neg]), sub.clone()),
            _ => {
                let s = 1 + self.r.below(5);
                self.random(s)
            }
        };
        replace_at(&t, &mut i.clone(), &new)
    }
}

/// Inputs of benchmark dataset lines, each parsed as infix (unparsable and large ones skipped).
fn load_corpus(files: &str) -> Vec<Term> {
    let mut out = Vec::new();
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    for f in files.split(',').filter(|f| !f.is_empty()) {
        let text = std::fs::read_to_string(f).unwrap_or_else(|e| panic!("{f}: {e}"));
        for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
            let mut depth = 0i32;
            let input = line.split(|ch| {
                depth += (ch == '(') as i32 - (ch == ')') as i32;
                ch == ',' && depth == 0
            });
            let Some(input) = input.into_iter().next() else { continue };
            let input = input.trim().to_string();
            if input.len() > 4000 {
                continue;
            }
            let parsed = std::panic::catch_unwind(|| eval::parse(&infix_to_egglog(&input, true)));
            if let Ok(t) = parsed
                && eval::size(&t) <= 400
            {
                out.push(t);
            }
        }
    }
    std::panic::set_hook(hook);
    out
}

fn inverse(k: u64) -> u64 {
    let mut x = k;
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(k.wrapping_mul(x)));
    }
    x
}

fn gen_case(seed: u64, index: usize, types: &[&'static str], kinds: &[&'static str], corpus: &[Term]) -> (&'static str, &'static str, Term) {
    let mut r = Rng::new(seed ^ (index as u64).wrapping_mul(0xa076_1d64_78bd_642f));
    let kind = kinds[r.below(kinds.len())];
    if kind == "mutate" {
        let ty_name = types[r.below(types.len())];
        let t = r.pick(corpus).clone();
        let mut vars = eval::vars(&t);
        if vars.is_empty() {
            vars.push("x".into());
        }
        let opaque = r.chance(0.3);
        let mut g = Gen { ty: NumType::from_name(ty_name).unwrap(), vars, r, opaque };
        let n = 1 + g.r.below(3);
        let mut t = t;
        for _ in 0..n {
            t = g.mutate(t);
        }
        return (kind, ty_name, t);
    }
    let small = ["i8", "u8"];
    let ty_name = if kind == "small8" {
        *r.pick(&small)
    } else {
        types[r.below(types.len())]
    };
    let ty = NumType::from_name(ty_name).unwrap();
    let nvars = match kind {
        "small8" => 1 + r.below(2),
        "wide" => 4 + r.below(7),
        "magic" => 1,
        _ => {
            let cap = if r.chance(0.6) { 3 } else { 6 };
            1 + r.below(cap)
        }
    };
    let names = ["x", "y", "z", "w", "v", "u", "t", "s", "q", "p"];
    let vars = names[..nvars].iter().map(|s| s.to_string()).collect();
    let opaque = match kind {
        "linear" | "wide" | "poly" | "semi" => false,
        _ => r.chance(0.6),
    };
    let mut g = Gen { ty, vars, r, opaque };
    (kind, ty_name, g.case(kind))
}

fn norm(ty: NumType) -> impl Fn(i64) -> i64 {
    move |n| {
        let sh = 64 - ty.bits;
        if ty.signed { (n << sh) >> sh } else { ((n as u64) << sh >> sh) as i64 }
    }
}

/// Evaluation points: every point when there are at most 2^16, else corner values and random ones.
fn points(ty: NumType, k: usize) -> Vec<Vec<u64>> {
    if k == 0 {
        return vec![vec![]];
    }
    let total_bits = ty.bits as usize * k;
    if total_bits <= 16 {
        let m = ty.mask();
        return (0..1u64 << total_bits)
            .map(|p| (0..k).map(|i| (p >> (i as u32 * ty.bits)) & m).collect())
            .collect();
    }
    let w = ty.bits as u64;
    let min = 1u64 << (w - 1);
    let corner = [0, 1, 2, 3, u64::MAX, u64::MAX - 1, min, min - 1, min + 1, w - 1, w, w + 1, 0x5555_5555_5555_5555, 0xaaaa_aaaa_aaaa_aaaa, 0xff, 0x100];
    let mut out = Vec::new();
    let combos = corner.len().pow(k.min(4) as u32);
    if combos <= 4096 {
        for c in 0..combos {
            let mut c = c;
            out.push(
                (0..k)
                    .map(|_| {
                        let v = corner[c % corner.len()];
                        c /= corner.len();
                        v
                    })
                    .collect(),
            );
        }
    }
    let mut r = Rng::new(0x1234_5678);
    for i in 0..3000 {
        out.push(
            (0..k)
                .map(|_| match i % 4 {
                    0 => r.next(),
                    1 => r.next() >> r.below(64),
                    2 => (r.below(2 * w as usize + 4) as u64).wrapping_sub(2),
                    _ => corner[r.below(corner.len())] ^ (r.chance(0.5) as u64) << r.below(w as usize),
                })
                .collect(),
        );
    }
    out
}

enum Diff {
    Same,
    /// Point, input value, output value (None: output divides by zero).
    At(Vec<(String, u64)>, u64, Option<u64>),
}

fn compare(a: &Term, b: &Term, ty: NumType) -> Diff {
    let mut names = eval::vars(a);
    for v in eval::vars(b) {
        if !names.contains(&v) {
            names.push(v);
        }
    }
    for p in points(ty, names.len()) {
        let env = |v: &str| names.iter().position(|n| n == v).map_or(0, |i| p[i]);
        let Some(x) = eval::eval(a, ty, &env) else { continue };
        let y = eval::eval(b, ty, &env);
        if y != Some(x) {
            let at = names.iter().cloned().zip(p.iter().map(|v| v & ty.mask())).collect();
            return Diff::At(at, x, y);
        }
    }
    Diff::Same
}

fn describe(d: &Diff) -> String {
    match d {
        Diff::Same => String::new(),
        Diff::At(at, x, y) => {
            let p: Vec<String> = at.iter().map(|(n, v)| format!("{n}={v:#x}")).collect();
            format!("at {} input {x:#x} output {}", p.join(" "), y.map_or("div0".to_string(), |y| format!("{y:#x}")))
        }
    }
}

/// Child mode: stdin holds the type name and an egglog term; prints `status<TAB>detail`.
fn run_one() {
    let mut lines = std::io::stdin().lock().lines();
    let ty_name = lines.next().unwrap().unwrap();
    let egg = lines.next().unwrap().unwrap();
    let prepass_only = lines.next().and_then(Result::ok).is_some_and(|m| m == "prepass");
    let ty = NumType::from_name(&ty_name).expect("bad numeric type");
    let t = eval::parse(&egg);

    // The infix printer and parser must round-trip the input.
    let infix = egglog_to_infix(&egg, &norm(ty));
    let back = eval::parse(&infix_to_egglog(&infix, true));
    if let d @ Diff::At(..) = compare(&t, &back, ty) {
        println!("infix\t{} -> {infix}", describe(&d));
        return;
    }

    if prepass_only {
        let (alt, other) = prepass(&egg, &ty_name);
        let polished = run_default(&ty_name, &format!("(parse {}) | (polish polish_steps)", quoted(&alt))).swap_remove(0);
        let cands: Vec<(&str, &String)> = [("first", &alt), ("polished", &polished)].into_iter().chain(other.iter().map(|o| ("other", o))).collect();
        for (name, c) in &cands {
            let d = compare(&t, &eval::parse(c), ty);
            if !matches!(d, Diff::Same) {
                let status = if matches!(d, Diff::At(_, _, None)) { "undef" } else { "wrong" };
                println!("{status}\t{} -> {}; pre-pass {name}", describe(&d), egglog_to_infix(c, &norm(ty)));
                return;
            }
        }
        println!("ok\t{}\t{}\t{}", eval::size(&t), eval::size(&eval::parse(&alt)), egglog_to_infix(&alt, &norm(ty)));
        return;
    }

    let cli = Cli { num_type: ty_name.clone(), expr: infix.clone(), ..Default::default() };
    let out = match simplify(&egg, &cli) {
        Ok(o) => o,
        Err(e) => {
            println!("error\t{}", e.to_string().replace(['\n', '\t'], " "));
            return;
        }
    };
    let out_t = eval::parse(&infix_to_egglog(&out, true));
    match compare(&t, &out_t, ty) {
        Diff::Same => println!("ok\t{}\t{}\t{out}", eval::size(&t), eval::size(&out_t)),
        d => {
            let status = if matches!(d, Diff::At(_, _, None)) { "undef" } else { "wrong" };
            let (alt, other) = prepass(&egg, &ty_name);
            let stage = std::iter::once(&alt)
                .chain(&other)
                .find(|c| !matches!(compare(&t, &eval::parse(c), ty), Diff::Same))
                .map_or("rules".to_string(), |c| format!("pre-pass {}", egglog_to_infix(c, &norm(ty))));
            println!("{status}\t{} -> {out}; {stage}", describe(&d));
        }
    }
}

/// The egglog terms of the candidates the program `code` gives after `(import "default")` and
/// `num_type = ty`.
fn run_default(ty: &str, code: &str) -> Vec<String> {
    match eggy1::lang::run(&format!("(import \"default\")
num_type = {ty}
{code}"), &[]) {
        Ok(eggy1::lang::Outcome { value: Some(eggy1::lang::Value::Group(g)), .. }) => g.iter().map(|c| c.term().to_string()).collect(),
        Ok(_) => panic!("{code} gives no candidates"),
        Err(e) => panic!("{code}: {e}"),
    }
}

/// The pre-pass of the default passes on the egglog term `egg`: the main rebuild, then the
/// others unioned with it.
fn prepass(egg: &str, ty: &str) -> (String, Vec<String>) {
    let mut out = run_default(ty, &format!("(parse {}) | (prepass prepass_steps)", quoted(egg)));
    let main = out.remove(0);
    (main, out)
}

struct Outcome {
    status: String,
    secs: f64,
    detail: String,
}

/// Resident memory of the child once it runs this binary in child mode (before `exec`, the
/// fork still shows the parent's pages).
fn rss_mb(pid: u32) -> u64 {
    let execed = std::fs::read(format!("/proc/{pid}/cmdline")).is_ok_and(|c| c.windows(5).any(|w| w == b"--one"));
    if !execed {
        return 0;
    }
    std::fs::read_to_string(format!("/proc/{pid}/status"))
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmRSS:")).and_then(|l| l.split_whitespace().nth(1)?.parse::<u64>().ok()))
        .map_or(0, |kb| kb / 1024)
}

fn run_child(args: &Args, ty: &str, t: &Term) -> Outcome {
    let start = Instant::now();
    let exe = std::env::current_exe().unwrap();
    // A hard address-space limit as well, since a child can outgrow the polled limit between polls.
    let mut cmd = if cfg!(target_os = "linux") {
        let mut c = Command::new("sh");
        c.args(["-c", "ulimit -v $1 && exec \"$0\" --one"]).arg(&exe).arg((args.mem_mb * 4 * 1024).to_string());
        c
    } else {
        let mut c = Command::new(&exe);
        c.arg("--one");
        c
    };
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn child");
    let mut stdin = child.stdin.take().unwrap();
    let _ = writeln!(stdin, "{ty}\n{}\n{}", eval::show(t), if args.prepass { "prepass" } else { "full" });
    drop(stdin);
    let pipe = |mut r: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut s = String::new();
            let _ = r.read_to_string(&mut s);
            s
        })
    };
    let out = pipe(Box::new(child.stdout.take().unwrap()));
    let err = pipe(Box::new(child.stderr.take().unwrap()));
    let limit = Duration::from_secs_f64(args.timeout);
    let mut killed = None;
    let status = loop {
        if let Some(s) = child.try_wait().unwrap() {
            break Some(s);
        }
        let over = if start.elapsed() > limit {
            Some("timeout")
        } else if rss_mb(child.id()) > args.mem_mb {
            Some("memory")
        } else {
            None
        };
        if let Some(why) = over {
            let _ = child.kill();
            let _ = child.wait();
            killed = Some(why);
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let secs = start.elapsed().as_secs_f64();
    let (out, err) = (out.join().unwrap(), err.join().unwrap());
    match status {
        None => Outcome { status: killed.unwrap().into(), secs, detail: String::new() },
        Some(s) if !s.success() => {
            let (status, line) = if err.contains("memory allocation") {
                ("memory", err.lines().find(|l| l.contains("memory allocation")))
            } else if err.contains("overflow") && err.contains("stack") {
                ("stack", err.lines().find(|l| l.contains("overflow")))
            } else if err.contains("panicked") {
                ("panic", err.lines().skip_while(|l| !l.contains("panicked")).nth(1).or(err.lines().find(|l| l.contains("panicked"))))
            } else {
                ("crash", err.lines().last())
            };
            let first = err.lines().find(|l| l.contains("panicked")).unwrap_or("");
            Outcome { status: status.into(), secs, detail: format!("{s} {first} {}", line.unwrap_or("")).trim().to_string() }
        }
        Some(_) => {
            let (status, detail) = out.trim().split_once('\t').unwrap_or(("crash", "no output"));
            Outcome { status: status.into(), secs, detail: detail.into() }
        }
    }
}

fn is_failure(args: &Args, o: &Outcome, size: usize) -> bool {
    match o.status.as_str() {
        "ok" => false,
        "timeout" => size <= args.report_timeout_size,
        _ => true,
    }
}

/// Replacements for one subterm: one of its operands, a variable or 0, or a simpler constant.
fn replacements(t: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    match t {
        Term::Num(c) => {
            for v in [0, 1, -1, 2] {
                if *c != v && (c.unsigned_abs() > 2 || v == 0) {
                    out.push(num(v));
                }
            }
            if c.unsigned_abs() > 2 {
                out.extend([c / 2, c >> 32, *c as i32 as i64, *c as i8 as i64].map(num));
            }
        }
        Term::Var(v) if v != "x" => out.push(Term::Var("x".into())),
        Term::Var(_) => out.push(num(0)),
        Term::Op(_, a) => {
            out.extend(a.iter().cloned());
            out.push(num(0));
            out.push(Term::Var("x".into()));
        }
    }
    out
}

fn subterm(t: &Term, i: &mut usize) -> Option<Term> {
    if *i == 0 {
        return Some(t.clone());
    }
    *i -= 1;
    match t {
        Term::Op(_, a) => a.iter().find_map(|x| subterm(x, i)),
        _ => None,
    }
}

fn replace_at(t: &Term, i: &mut usize, r: &Term) -> Term {
    if *i == usize::MAX {
        return t.clone();
    }
    if *i == 0 {
        *i = usize::MAX;
        return r.clone();
    }
    *i -= 1;
    match t {
        Term::Op(op, a) => Term::Op(*op, a.iter().map(|x| replace_at(x, i, r)).collect()),
        _ => t.clone(),
    }
}

/// Greedy shrinking: tries replacements at each node in preorder and keeps the first
/// smaller term that fails with the same status.
fn shrink(args: &Args, ty: &str, t: &Term, status: &str) -> (Term, Outcome) {
    let mut best = t.clone();
    let mut best_o = None;
    let mut budget = args.shrink;
    'outer: while budget > 0 {
        for i in 0..eval::size(&best) {
            let Some(sub) = subterm(&best, &mut i.clone()) else { break };
            for r in replacements(&sub) {
                let c = replace_at(&best, &mut i.clone(), &r);
                if eval::size(&c) > eval::size(&best) || c == best {
                    continue;
                }
                if budget == 0 {
                    break 'outer;
                }
                budget -= 1;
                let o = run_child(args, ty, &c);
                if o.status == status {
                    best = c;
                    best_o = Some(o);
                    continue 'outer;
                }
            }
        }
        break;
    }
    let o = best_o.unwrap_or_else(|| run_child(args, ty, &best));
    (best, o)
}

struct Stats {
    cases: usize,
    sizes: Vec<usize>,
    statuses: BTreeMap<String, usize>,
}

fn run_all(args: &Args) {
    let types: Vec<&'static str> = if args.num_type == "all" {
        TYPES.to_vec()
    } else {
        args.num_type.split(',').map(|t| *TYPES.iter().find(|x| **x == t).expect("unknown type")).collect()
    };
    let kinds: Vec<&'static str> = if args.kind == "all" {
        KINDS.to_vec()
    } else {
        args.kind.split(',').map(|k| *KINDS.iter().chain(&["mutate"]).find(|x| **x == k).expect("unknown kind")).collect()
    };
    let corpus = Arc::new(load_corpus(&args.corpus));
    assert!(!kinds.contains(&"mutate") || !corpus.is_empty(), "kind mutate needs --corpus");
    let replay: Option<Vec<(String, String, Term)>> = args.replay.as_ref().map(|path| {
        std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("{path}: {e}"))
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
            .map(|l| {
                let cols: Vec<&str> = l.split('\t').collect();
                let (kind, ty, infix) = match cols.len() {
                    2 => ("replay", cols[0], cols[1]),
                    _ => (cols[0], cols[1], cols[3]),
                };
                (kind.to_string(), ty.to_string(), eval::parse(&infix_to_egglog(infix, true)))
            })
            .collect()
    });
    let total = replay.as_ref().map_or(args.cases, Vec::len);
    let replay = Arc::new(replay);
    let jobs = args.jobs.unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get()));
    let next = Arc::new(AtomicUsize::new(0));
    let stats: Arc<Mutex<BTreeMap<(String, String), Stats>>> = Arc::new(Mutex::new(BTreeMap::new()));
    let log = Arc::new(Mutex::new(std::fs::OpenOptions::new().create(true).append(true).open(&args.out).expect("open failure log")));
    let started = Instant::now();
    eprintln!("{total} cases, {jobs} jobs, seed {}", args.seed);
    let workers: Vec<_> = (0..jobs)
        .map(|_| {
            let (next, stats, log, args, types, kinds, replay, corpus) =
                (next.clone(), stats.clone(), log.clone(), args.clone(), types.clone(), kinds.clone(), replay.clone(), corpus.clone());
            std::thread::spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    if i >= total {
                        break;
                    }
                    let (kind, ty, t) = match replay.as_ref() {
                        Some(r) => r[i].clone(),
                        None => {
                            let (k, ty, t) = gen_case(args.seed, i, &types, &kinds, &corpus);
                            (k.to_string(), ty.to_string(), t)
                        }
                    };
                    let size = eval::size(&t);
                    let o = run_child(&args, &ty, &t);
                    let fail = is_failure(&args, &o, size);
                    {
                        let mut s = stats.lock().unwrap();
                        let e = s.entry((ty.clone(), kind.clone())).or_insert(Stats { cases: 0, sizes: Vec::new(), statuses: BTreeMap::new() });
                        e.cases += 1;
                        e.sizes.push(size);
                        *e.statuses.entry(o.status.clone()).or_default() += 1;
                    }
                    if fail {
                        let infix = egglog_to_infix(&eval::show(&t), &norm(NumType::from_name(&ty).unwrap()));
                        eprintln!("[{}] case {i} {kind} {ty} size {size}: {} {}", o.status, infix.chars().take(300).collect::<String>(), o.detail);
                        let (small, so) = if o.status == "timeout" || o.status == "memory" || args.shrink == 0 {
                            (t.clone(), Outcome { status: o.status.clone(), secs: o.secs, detail: o.detail.clone() })
                        } else {
                            shrink(&args, &ty, &t, &o.status)
                        };
                        let small_infix = egglog_to_infix(&eval::show(&small), &norm(NumType::from_name(&ty).unwrap()));
                        let line = format!(
                            "{kind}\t{ty}\t{}\t{small_infix}\t{} (case {i} seed {} size {size}, {:.1}s; original {infix})\n",
                            so.status,
                            so.detail.replace(['\t', '\n'], " "),
                            args.seed,
                            o.secs
                        );
                        eprintln!("  shrunk to size {}: {small_infix} {}", eval::size(&small), so.detail);
                        log.lock().unwrap().write_all(line.as_bytes()).unwrap();
                    }
                    let done = i + 1;
                    if done % 200 == 0 {
                        eprintln!("{done}/{total} ({:.0}s)", started.elapsed().as_secs_f64());
                    }
                }
            })
        })
        .collect();
    workers.into_iter().for_each(|w| w.join().unwrap());

    let stats = Arc::try_unwrap(stats).ok().unwrap().into_inner().unwrap();
    let mut by_type: BTreeMap<String, (usize, BTreeMap<String, usize>)> = BTreeMap::new();
    println!("| type | kind | cases | size min/median/max | statuses |");
    println!("|---|---|---|---|---|");
    for ((ty, kind), mut s) in stats {
        s.sizes.sort_unstable();
        let st: Vec<String> = s.statuses.iter().map(|(k, v)| format!("{k} {v}")).collect();
        println!("| {ty} | {kind} | {} | {}/{}/{} | {} |", s.cases, s.sizes[0], s.sizes[s.sizes.len() / 2], s.sizes[s.sizes.len() - 1], st.join(", "));
        let e = by_type.entry(ty).or_default();
        e.0 += s.cases;
        for (k, v) in s.statuses {
            *e.1.entry(k).or_default() += v;
        }
    }
    for (ty, (n, st)) in by_type {
        let st: Vec<String> = st.iter().map(|(k, v)| format!("{k} {v}")).collect();
        println!("| {ty} | all | {n} | | {} |", st.join(", "));
    }
    eprintln!("done in {:.0}s", started.elapsed().as_secs_f64());
}
