//! Exact replacement of subterms over at most `tfunc_max_vars` variables by the smallest
//! equivalent expression of size up to `tfunc_max_size`. Candidates are looked up by
//! their values at fixed points, then proved equal: `+ - & | ^ ~`, negation and
//! small constant multiples are T-functions (bit `i` of the result depends only on
//! bits `0..=i` of the inputs), so equality follows from running both terms bit by
//! bit over all input bits while tracking the reachable sets of carries.

use crate::eval::{Op, Term as T, size};
use crate::linear_mba::Ctx;
use crate::rust_vars::{limit, Limit};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

/// Most points (`tfunc_points`) and variables (`tfunc_max_vars`) of the lookup. Points past
/// `tfunc_points` are all 0, so their values repeat those at point 0 and change no key.
pub(crate) const POINTS_CAP: usize = 24;
pub(crate) const VARS_CAP: usize = 4;

type Fp = [u64; POINTS_CAP];
type Points = [[u64; VARS_CAP]; POINTS_CAP];

/// The variables of the lookup, read once per call.
struct Lims {
    max_vars: usize,
    max_size: usize,
    points: usize,
    max_try: usize,
    proof: Proof,
}

impl Lims {
    fn read() -> Lims {
        Lims {
            max_vars: limit(Limit::TfuncMaxVars),
            max_size: limit(Limit::TfuncMaxSize),
            points: limit(Limit::TfuncPoints),
            max_try: limit(Limit::TfuncMaxTry),
            proof: Proof::read(),
        }
    }
}

/// The limits of the equality proof: most carries, most reachable carry states per bit, and
/// the largest constant multiplier (or its negation) expanded into adders.
#[derive(Clone, Copy)]
pub(crate) struct Proof {
    max_carries: usize,
    max_states: usize,
    max_factor: u64,
}

impl Proof {
    pub(crate) fn read() -> Proof {
        Proof {
            max_carries: limit(Limit::TfuncMaxCarries),
            max_states: limit(Limit::TfuncMaxStates),
            max_factor: limit(Limit::TfuncMaxFactor) as u64,
        }
    }
}

fn points(w: &Ctx, lim: &Lims) -> Points {
    let mut h = 0x2545_f491_4f6c_dd1du64;
    let mut out = [[0; VARS_CAP]; POINTS_CAP];
    for (k, p) in out.iter_mut().enumerate().take(lim.points) {
        for (j, v) in p.iter_mut().enumerate().take(lim.max_vars) {
            h ^= h << 13;
            h ^= h >> 7;
            h ^= h << 17;
            // A few small and all-ones values, where carries chains differ most.
            *v = match (k, j) {
                (0, _) => 0,
                (1, _) => u64::MAX,
                (2, 0) | (3, 1) | (4, 2) => 1,
                (5, _) => 1 << j,
                _ => h,
            } & w.mask;
        }
    }
    out
}

fn op_vals(op: Op, a: &Fp, b: &Fp, m: u64) -> Fp {
    fn lanes(a: &Fp, b: &Fp, m: u64, f: impl Fn(u64, u64) -> u64) -> Fp {
        std::array::from_fn(|k| f(a[k], b[k]) & m)
    }
    match op {
        Op::Add => lanes(a, b, m, u64::wrapping_add),
        Op::Sub => lanes(a, b, m, u64::wrapping_sub),
        Op::Mul => lanes(a, b, m, u64::wrapping_mul),
        Op::And => lanes(a, b, m, |x, y| x & y),
        Op::Or => lanes(a, b, m, |x, y| x | y),
        _ => lanes(a, b, m, |x, y| x ^ y),
    }
}

/// A value vector hashed by a few of its pseudo-random points only, which tell most
/// vectors apart; equality still compares all of them.
#[derive(PartialEq, Eq)]
struct Key(Fp);

impl std::hash::Hash for Key {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.0[6..10].hash(h);
    }
}

/// Values of `t` at the points, with `vars[j]` read from coordinate `j`; `None` for
/// operations the proof does not handle.
fn values(t: &T, vars: &[String], pts: &Points, w: &Ctx) -> Option<Fp> {
    let m = w.mask;
    Some(match t {
        T::Num(c) => [*c as u64 & m; POINTS_CAP],
        T::Var(v) => {
            let j = vars.iter().position(|x| x == v)?;
            std::array::from_fn(|k| pts[k][j])
        }
        T::Op(op, a) => match op {
            Op::Not => values(&a[0], vars, pts, w)?.map(|x| !x & m),
            Op::Neg => values(&a[0], vars, pts, w)?.map(|x| x.wrapping_neg() & m),
            Op::Add | Op::Sub | Op::And | Op::Or | Op::Xor => op_vals(*op, &values(&a[0], vars, pts, w)?, &values(&a[1], vars, pts, w)?, m),
            Op::Mul if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => {
                op_vals(*op, &values(&a[0], vars, pts, w)?, &values(&a[1], vars, pts, w)?, m)
            }
            _ => return None,
        },
    })
}

/// An expression of the table, its operands given by their index in `Table::entries`.
#[derive(Clone, Copy)]
enum Entry {
    Var(usize),
    Num(i64),
    Un(Op, u32),
    Bin(Op, u32, u32),
}

struct Table {
    by_fp: crate::eval::FastMap<Key, u32>,
    entries: Vec<Entry>,
}

impl Table {
    fn term(&self, i: u32) -> T {
        match self.entries[i as usize] {
            Entry::Var(j) => T::Var(j.to_string()),
            Entry::Num(k) => T::Num(k),
            Entry::Un(op, a) => T::Op(op, vec![self.term(a)]),
            Entry::Bin(op, a, b) => T::Op(op, vec![self.term(a), self.term(b)]),
        }
    }
}

/// The table over `n` variables, one per width and values of the variables it is built from.
fn table(n: usize, w: &Ctx, lim: &Lims) -> &'static Table {
    type TableKey = (usize, u32, usize, usize, usize);
    static TABLES: OnceLock<Mutex<HashMap<TableKey, &'static Table>>> = OnceLock::new();
    let mut tables = TABLES.get_or_init(Default::default).lock().unwrap();
    tables.entry((n, w.w, lim.max_size, lim.points, lim.max_vars)).or_insert_with(|| Box::leak(Box::new(build_table(n, w, lim))))
}

/// Smallest expression for each distinct value vector, enumerated by size over
/// placeholder variables `"0"`, `"1"`, ... and the constants 1 and -1.
fn build_table(n: usize, w: &Ctx, lim: &Lims) -> Table {
    let pts = points(w, lim);
    let mut table = Table { by_fp: Default::default(), entries: Vec::new() };
    let mut fps: Vec<Fp> = Vec::new();
    let add = |table: &mut Table, fps: &mut Vec<Fp>, fp: Fp, e: Entry, level: &mut Vec<u32>| {
        if let std::collections::hash_map::Entry::Vacant(v) = table.by_fp.entry(Key(fp)) {
            let i = table.entries.len() as u32;
            v.insert(i);
            table.entries.push(e);
            fps.push(fp);
            level.push(i);
        }
    };
    let mut levels: Vec<Vec<u32>> = vec![Vec::new(), Vec::new()];
    for j in 0..n {
        add(&mut table, &mut fps, std::array::from_fn(|k| pts[k][j]), Entry::Var(j), &mut levels[1]);
    }
    for k in [1, w.signed(w.mask)] {
        add(&mut table, &mut fps, [k as u64 & w.mask; POINTS_CAP], Entry::Num(k), &mut levels[1]);
    }
    let m = w.mask;
    for s in 2..=lim.max_size {
        let mut level = Vec::new();
        for &x in &levels[s - 1] {
            let fx = fps[x as usize];
            add(&mut table, &mut fps, fx.map(|v| !v & m), Entry::Un(Op::Not, x), &mut level);
            add(&mut table, &mut fps, fx.map(|v| v.wrapping_neg() & m), Entry::Un(Op::Neg, x), &mut level);
        }
        for a in 1..s - 1 {
            let b = s - 1 - a;
            for (i, &x) in levels[a].iter().enumerate() {
                let fx = fps[x as usize];
                for (j, &y) in levels[b].iter().enumerate() {
                    let fy = fps[y as usize];
                    // A commutative operation on the swapped pair was already added.
                    let swapped = a > b || a == b && j < i;
                    for op in [Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor] {
                        if swapped && op != Op::Sub {
                            continue;
                        }
                        add(&mut table, &mut fps, op_vals(op, &fx, &fy, m), Entry::Bin(op, x, y), &mut level);
                    }
                }
            }
        }
        levels.push(level);
    }
    table
}

enum Gate {
    In(usize),
    Const(u64),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    /// Sum bit of `a + b + carry`, with the carry kept in state bit `c`.
    Add(usize, usize, usize),
}

struct Circuit {
    gates: Vec<Gate>,
    init: u128,
    carries: usize,
    lim: Proof,
}

impl Circuit {
    fn new(lim: Proof) -> Circuit {
        Circuit { gates: Vec::new(), init: 0, carries: 0, lim }
    }

    fn gate(&mut self, g: Gate) -> usize {
        self.gates.push(g);
        self.gates.len() - 1
    }

    fn adder(&mut self, a: usize, b: usize, carry_in: bool) -> Option<usize> {
        let c = self.carries;
        if c == self.lim.max_carries {
            return None;
        }
        self.carries += 1;
        self.init |= (carry_in as u128) << c;
        Some(self.gate(Gate::Add(a, b, c)))
    }

    fn neg(&mut self, a: usize) -> Option<usize> {
        let (na, zero) = (self.gate(Gate::Not(a)), self.gate(Gate::Const(0)));
        self.adder(na, zero, true)
    }

    fn times(&mut self, c: u64, e: usize, w: &Ctx) -> Option<usize> {
        let max = self.lim.max_factor;
        let (c, negate) = if c <= max { (c, false) } else { (c.wrapping_neg() & w.mask, true) };
        if c > max {
            return None;
        }
        let mut acc = self.gate(Gate::Const(0));
        for i in (0..64 - c.leading_zeros()).rev() {
            acc = self.adder(acc, acc, false)?;
            if c >> i & 1 == 1 {
                acc = self.adder(acc, e, false)?;
            }
        }
        if negate { self.neg(acc) } else { Some(acc) }
    }

    fn compile(&mut self, t: &T, vars: &[String], w: &Ctx) -> Option<usize> {
        Some(match t {
            T::Num(c) => self.gate(Gate::Const(*c as u64 & w.mask)),
            T::Var(v) => self.gate(Gate::In(vars.iter().position(|x| x == v)?)),
            T::Op(op, a) => match op {
                Op::Not => {
                    let x = self.compile(&a[0], vars, w)?;
                    self.gate(Gate::Not(x))
                }
                Op::Neg => {
                    let x = self.compile(&a[0], vars, w)?;
                    self.neg(x)?
                }
                Op::Mul => match (&a[0], &a[1]) {
                    (T::Num(c), e) | (e, T::Num(c)) => {
                        let x = self.compile(e, vars, w)?;
                        self.times(*c as u64 & w.mask, x, w)?
                    }
                    _ => return None,
                },
                Op::Add | Op::Sub | Op::And | Op::Or | Op::Xor => {
                    let x = self.compile(&a[0], vars, w)?;
                    let y = self.compile(&a[1], vars, w)?;
                    match op {
                        Op::Add => self.adder(x, y, false)?,
                        Op::Sub => {
                            let ny = self.gate(Gate::Not(y));
                            self.adder(x, ny, true)?
                        }
                        Op::And => self.gate(Gate::And(x, y)),
                        Op::Or => self.gate(Gate::Or(x, y)),
                        _ => self.gate(Gate::Xor(x, y)),
                    }
                }
                _ => return None,
            },
        })
    }
}

impl Circuit {
    /// Evaluates the gates at bit `i` from carry state `s` with input `j` given by
    /// `inp(j)`; returns the next state.
    fn step(&self, s: u128, i: u32, inp: impl Fn(usize) -> bool, v: &mut [bool]) -> u128 {
        let mut ns = s;
        for (k, g) in self.gates.iter().enumerate() {
            v[k] = match *g {
                Gate::In(j) => inp(j),
                Gate::Const(x) => x >> i & 1 == 1,
                Gate::Not(a) => !v[a],
                Gate::And(a, b) => v[a] & v[b],
                Gate::Or(a, b) => v[a] | v[b],
                Gate::Xor(a, b) => v[a] ^ v[b],
                Gate::Add(a, b, ci) => {
                    let cin = s >> ci & 1 == 1;
                    let (x, y) = (v[a], v[b]);
                    let cout = x & y | cin & (x ^ y);
                    ns = ns & !(1 << ci) | (cout as u128) << ci;
                    x ^ y ^ cin
                }
            };
        }
        ns
    }
}

/// Whether `f` and `g` agree on all inputs; `None` if a term has an unsupported
/// operation or the carry states grow too many.
fn equal(f: &T, g: &T, vars: &[String], lim: Proof, w: &Ctx) -> Option<bool> {
    equal_low(f, g, vars, vars.len(), 0, &|_| Vec::new(), lim, w)
}

/// Like `equal`, where inputs `vars[n..]` are not free but `extra` of the low `m`
/// bits of inputs `0..n`, with bits from `m` up the same for all of them.
#[allow(clippy::too_many_arguments)]
pub(crate) fn equal_low(f: &T, g: &T, vars: &[String], n: usize, m: u32, extra: &dyn Fn(&[u64]) -> Vec<u64>, lim: Proof, w: &Ctx) -> Option<bool> {
    let mut c = Circuit::new(lim);
    let (fo, go) = (c.compile(f, vars, w)?, c.compile(g, vars, w)?);
    let mut v = vec![false; c.gates.len()];
    let lm = (1u64 << m) - 1;
    let mut states: crate::eval::FastSet<u128> = Default::default();
    let mut high: Option<Vec<u64>> = None;
    for p in 0u64..1 << (n as u32 * m) {
        let low: Vec<u64> = (0..n).map(|j| p >> (j as u32 * m) & lm).collect();
        let ex = extra(&low);
        let hi: Vec<u64> = ex.iter().map(|x| x & !lm).collect();
        if *high.get_or_insert_with(|| hi.clone()) != hi {
            return None;
        }
        let mut s = c.init;
        for i in 0..m {
            s = c.step(s, i, |j| if j < n { low[j] >> i & 1 == 1 } else { ex[j - n] >> i & 1 == 1 }, &mut v);
            if v[fo] != v[go] {
                return Some(false);
            }
        }
        states.insert(s);
        if states.len() > lim.max_states {
            return None;
        }
    }
    let high = high.unwrap_or_default();
    for i in m..w.w {
        let mut next = crate::eval::FastSet::default();
        for &s in &states {
            for inp in 0..1usize << n {
                let ns = c.step(s, i, |j| if j < n { inp >> j & 1 == 1 } else { high[j - n] >> i & 1 == 1 }, &mut v);
                if v[fo] != v[go] {
                    return Some(false);
                }
                next.insert(ns);
            }
        }
        if next.len() > lim.max_states {
            return None;
        }
        states = next;
    }
    Some(true)
}

pub(crate) fn var_names(t: &T, out: &mut Vec<String>) {
    match t {
        T::Var(v) if !out.contains(v) => out.push(v.clone()),
        T::Op(_, a) => a.iter().for_each(|x| var_names(x, out)),
        _ => {}
    }
}

fn rename(t: &T, vars: &[String]) -> T {
    match t {
        T::Var(j) => T::Var(vars[j.parse::<usize>().unwrap()].clone()),
        T::Op(op, a) => T::Op(*op, a.iter().map(|x| rename(x, vars)).collect()),
        _ => t.clone(),
    }
}

/// The smallest proven-equal expression for `t`, if smaller than `t`.
pub(crate) fn replacement(t: &T, w: &Ctx) -> Option<T> {
    replacement_with(t, w, &Lims::read())
}

fn replacement_with(t: &T, w: &Ctx, lim: &Lims) -> Option<T> {
    if !(2..=lim.max_try).contains(&size(t)) {
        return None;
    }
    direct(t, w, lim).or_else(|| over_atoms(t, w, lim))
}

fn direct(t: &T, w: &Ctx, lim: &Lims) -> Option<T> {
    let mut vars = Vec::new();
    var_names(t, &mut vars);
    if vars.is_empty() || vars.len() > lim.max_vars {
        return None;
    }
    let fp = values(t, &vars, &points(w, lim), w)?;
    let tb = table(vars.len(), w, lim);
    let cand = rename(&tb.term(*tb.by_fp.get(&Key(fp))?), &vars);
    (size(&cand) < size(t) && equal(t, &cand, &vars, lim.proof, w)?).then_some(cand)
}

fn bitwise_only(t: &T) -> bool {
    match t {
        T::Var(_) | T::Num(_) => true,
        T::Op(op, a) => matches!(op, Op::And | Op::Or | Op::Xor | Op::Not) && a.iter().all(bitwise_only),
    }
}

/// Purely bitwise subterms as atoms, so `(x ^ z) & -((x ^ z) & -((x ^ z) & (y ^ z)))`
/// becomes `p & -(p & -(p & q))`. An atom that is a bitwise operation of other
/// atoms is split, or `p & q` would hide its relation to `p`.
fn over_atoms(t: &T, w: &Ctx, lim: &Lims) -> Option<T> {
    fn collect(t: &T, out: &mut Vec<T>) {
        match t {
            T::Op(op, a) if *op == Op::Not => collect(&a[0], out),
            T::Op(..) if bitwise_only(t) => {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            }
            T::Op(_, a) => a.iter().for_each(|x| collect(x, out)),
            T::Var(_) => {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            }
            T::Num(_) => {}
        }
    }
    let mut atoms = Vec::new();
    collect(t, &mut atoms);
    loop {
        let strip = |x: &T| match x {
            T::Op(op, a) if *op == Op::Not => a[0].clone(),
            _ => x.clone(),
        };
        let Some(i) = atoms.iter().position(|s| match s {
            T::Op(op, a) if *op != Op::Not => a.iter().any(|x| atoms.contains(&strip(x))),
            _ => false,
        }) else {
            break;
        };
        let T::Op(_, a) = atoms.remove(i) else { unreachable!() };
        for x in a.iter().map(strip) {
            if !matches!(x, T::Num(_)) && !atoms.contains(&x) {
                atoms.push(x);
            }
        }
    }
    if atoms.len() > lim.max_vars || atoms.iter().all(|a| matches!(a, T::Var(_))) {
        return None;
    }
    let names: Vec<T> = (0..atoms.len()).map(|i| T::Var(format!("\u{3}{i}"))).collect();
    fn abstracted(t: &T, atoms: &[T], names: &[T]) -> T {
        if let Some(i) = atoms.iter().position(|a| a == t) {
            return names[i].clone();
        }
        match t {
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| abstracted(x, atoms, names)).collect()),
            _ => t.clone(),
        }
    }
    fn fill(t: &T, atoms: &[T], names: &[T]) -> T {
        if let Some(i) = names.iter().position(|n| n == t) {
            return atoms[i].clone();
        }
        match t {
            T::Op(op, a) => T::Op(*op, a.iter().map(|x| fill(x, atoms, names)).collect()),
            _ => t.clone(),
        }
    }
    let r = fill(&direct(&abstracted(t, &atoms, &names), w, lim)?, &atoms, &names);
    (size(&r) < size(t)).then_some(r)
}

/// `t` with each outermost replaceable subterm replaced; a node whose operands
/// changed is tried again, since nested identities only show from the inside out.
pub(crate) fn simplify(t: &T, w: &Ctx) -> T {
    simplify_with(t, w, &Lims::read())
}

fn simplify_with(t: &T, w: &Ctx, lim: &Lims) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if let Some(r) = replacement_with(t, w, lim) {
        return r;
    }
    let inner = T::Op(*op, a.iter().map(|x| simplify_with(x, w, lim)).collect());
    if inner == *t {
        return inner;
    }
    replacement_with(&inner, w, lim).unwrap_or(inner)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn random_term(h: &mut u64, depth: u32) -> T {
        *h ^= *h << 13;
        *h ^= *h >> 7;
        *h ^= *h << 17;
        let r = *h;
        if depth == 0 || r % 7 == 0 {
            return match r >> 8 & 3 {
                0 => T::Num(r as i64 >> 40),
                1 => T::Var("x".into()),
                _ => T::Var("y".into()),
            };
        }
        let op = [Op::Add, Op::Sub, Op::And, Op::Or, Op::Xor, Op::Not, Op::Neg, Op::Mul][(r >> 16) as usize % 8];
        match op {
            Op::Not | Op::Neg => T::Op(op, vec![random_term(h, depth - 1)]),
            Op::Mul => T::Op(op, vec![T::Num((r >> 24) as i64 % 9 - 4), random_term(h, depth - 1)]),
            _ => T::Op(op, vec![random_term(h, depth - 1), random_term(h, depth - 1)]),
        }
    }

    #[test]
    fn proof_matches_exhaustive_check_at_8_bits() {
        let w = Ctx::new(8);
        let vars = vec!["x".to_string(), "y".to_string()];
        let ty = crate::eval::NumType { bits: 8, signed: false };
        let mut h = 0x1234_5678_9abc_def1u64;
        let proof = crate::rust_vars::in_default_run(Proof::read);
        let (mut proved, mut refuted) = (0, 0);
        for _ in 0..3000 {
            let (f, g) = (random_term(&mut h, 3), random_term(&mut h, 1));
            let Some(eq) = equal(&f, &g, &vars, proof, &w) else { continue };
            let truth = (0..256u64).all(|x| {
                (0..256u64).all(|y| {
                    let env = |v: &str| if v == "x" { x } else { y };
                    crate::eval::eval(&f, ty, &env) == crate::eval::eval(&g, ty, &env)
                })
            });
            assert_eq!(eq, truth, "{f:?}\n{g:?}");
            if eq { proved += 1 } else { refuted += 1 }
        }
        assert!(proved > 20 && refuted > 20, "proved {proved}, refuted {refuted}");
    }

    #[test]
    fn table_follows_its_variables() {
        let t = crate::eval::parse(&crate::expr_convert::infix_to_egglog("x & -(x & -(x & y))", true));
        let best = |spec: &str| {
            let p = crate::passes::Passes::parse(spec).unwrap();
            crate::lang::eval::in_run(&p, None, || crate::cand::Cand::new("(Var \"x\")", "input"), || replacement(&t, &Ctx::new(8)).map(|r| crate::eval::show(&r)))
        };
        let plain = best("");
        assert_eq!(plain.as_deref(), Some("(And (Var \"x\") (Var \"y\"))"));
        assert_eq!(best("tfunc_max_size=2"), None);
        assert_eq!(best(""), plain, "a smaller table leaves the default one");
        assert_eq!(best("tfunc_points=1"), None, "one point finds a smaller term the proof rejects");
        assert_eq!(best("tfunc_points=12 tfunc_max_vars=4"), plain);
        assert_eq!(best("tfunc_max_size=2"), None);
    }
}
