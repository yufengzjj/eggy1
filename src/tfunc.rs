//! Exact replacement of subterms over at most `MAX_VARS` variables by the smallest
//! equivalent expression of size up to `MAX_SIZE`. Candidates are looked up by
//! their values at fixed points, then proved equal: `+ - & | ^ ~`, negation and
//! small constant multiples are T-functions (bit `i` of the result depends only on
//! bits `0..=i` of the inputs), so equality follows from running both terms bit by
//! bit over all input bits while tracking the reachable sets of carries.

use crate::eval::{Term as T, size};
use crate::linear_mba::Width;
use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

const MAX_VARS: usize = 3;
const MAX_SIZE: usize = 5;
const POINTS: usize = 24;
/// Largest subterm tried; larger ones are rarely replaceable and costly to prove.
const MAX_TRY: usize = 256;
/// Most carries, and most reachable carry states per bit, before the proof gives up.
const MAX_CARRIES: usize = 64;
const MAX_STATES: usize = 512;
/// Largest constant multiplier (or its negation) the proof expands into adders.
const MAX_FACTOR: u64 = 255;

type Fp = [u64; POINTS];

fn points(w: &Width) -> [[u64; MAX_VARS]; POINTS] {
    let mut h = 0x2545_f491_4f6c_dd1du64;
    let mut out = [[0; MAX_VARS]; POINTS];
    for (k, p) in out.iter_mut().enumerate() {
        for (j, v) in p.iter_mut().enumerate() {
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

fn op_vals(op: &str, a: &Fp, b: &Fp, m: u64) -> Fp {
    let f: fn(u64, u64) -> u64 = match op {
        "Add" => u64::wrapping_add,
        "Sub" => u64::wrapping_sub,
        "Mul" => u64::wrapping_mul,
        "And" => |x, y| x & y,
        "Or" => |x, y| x | y,
        _ => |x, y| x ^ y,
    };
    std::array::from_fn(|k| f(a[k], b[k]) & m)
}

/// Values of `t` at the points, with `vars[j]` read from coordinate `j`; `None` for
/// operations the proof does not handle.
fn values(t: &T, vars: &[String], pts: &[[u64; MAX_VARS]; POINTS], w: &Width) -> Option<Fp> {
    let m = w.mask;
    Some(match t {
        T::Num(c) => [*c as u64 & m; POINTS],
        T::Var(v) => {
            let j = vars.iter().position(|x| x == v)?;
            std::array::from_fn(|k| pts[k][j])
        }
        T::Op(op, a) => match op.as_str() {
            "Not" => values(&a[0], vars, pts, w)?.map(|x| !x & m),
            "Neg" => values(&a[0], vars, pts, w)?.map(|x| x.wrapping_neg() & m),
            "Add" | "Sub" | "And" | "Or" | "Xor" => op_vals(op, &values(&a[0], vars, pts, w)?, &values(&a[1], vars, pts, w)?, m),
            "Mul" if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => {
                op_vals(op, &values(&a[0], vars, pts, w)?, &values(&a[1], vars, pts, w)?, m)
            }
            _ => return None,
        },
    })
}

struct Table {
    by_fp: HashMap<Fp, T>,
}

fn table(n: usize, w: &Width) -> &'static Table {
    static TABLES: OnceLock<Mutex<HashMap<(usize, u32), &'static Table>>> = OnceLock::new();
    let mut tables = TABLES.get_or_init(Default::default).lock().unwrap();
    tables.entry((n, w.w)).or_insert_with(|| Box::leak(Box::new(build_table(n, w))))
}

/// Smallest expression for each distinct value vector, enumerated by size over
/// placeholder variables `"0"`, `"1"`, ... and the constants 1 and -1.
fn build_table(n: usize, w: &Width) -> Table {
    let pts = points(w);
    let vars: Vec<String> = (0..n).map(|j| j.to_string()).collect();
    let mut by_fp: HashMap<Fp, T> = HashMap::new();
    let mut levels: Vec<Vec<(T, Fp)>> = vec![Vec::new()];
    let mut add = |t: T, levels: &mut Vec<Vec<(T, Fp)>>, s: usize| {
        let fp = values(&t, &vars, &pts, w).unwrap();
        if let std::collections::hash_map::Entry::Vacant(e) = by_fp.entry(fp) {
            e.insert(t.clone());
            levels[s].push((t, fp));
        }
    };
    levels.push(Vec::new());
    for j in 0..n {
        add(T::Var(j.to_string()), &mut levels, 1);
    }
    add(T::Num(1), &mut levels, 1);
    add(T::Num(w.signed(w.mask)), &mut levels, 1);
    for s in 2..=MAX_SIZE {
        levels.push(Vec::new());
        let mut new = Vec::new();
        for (t, _) in &levels[s - 1] {
            for op in ["Not", "Neg"] {
                new.push(T::Op(op.into(), vec![t.clone()]));
            }
        }
        for a in 1..s - 1 {
            for (x, _) in &levels[a] {
                for (y, _) in &levels[s - 1 - a] {
                    for op in ["Add", "Sub", "And", "Or", "Xor"] {
                        new.push(T::Op(op.into(), vec![x.clone(), y.clone()]));
                    }
                }
            }
        }
        for t in new {
            add(t, &mut levels, s);
        }
    }
    Table { by_fp }
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

#[derive(Default)]
struct Circuit {
    gates: Vec<Gate>,
    init: u128,
    carries: usize,
}

impl Circuit {
    fn gate(&mut self, g: Gate) -> usize {
        self.gates.push(g);
        self.gates.len() - 1
    }

    fn adder(&mut self, a: usize, b: usize, carry_in: bool) -> Option<usize> {
        let c = self.carries;
        if c == MAX_CARRIES {
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

    fn times(&mut self, c: u64, e: usize, w: &Width) -> Option<usize> {
        let (c, negate) = if c <= MAX_FACTOR { (c, false) } else { (c.wrapping_neg() & w.mask, true) };
        if c > MAX_FACTOR {
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

    fn compile(&mut self, t: &T, vars: &[String], w: &Width) -> Option<usize> {
        Some(match t {
            T::Num(c) => self.gate(Gate::Const(*c as u64 & w.mask)),
            T::Var(v) => self.gate(Gate::In(vars.iter().position(|x| x == v)?)),
            T::Op(op, a) => match op.as_str() {
                "Not" => {
                    let x = self.compile(&a[0], vars, w)?;
                    self.gate(Gate::Not(x))
                }
                "Neg" => {
                    let x = self.compile(&a[0], vars, w)?;
                    self.neg(x)?
                }
                "Mul" => match (&a[0], &a[1]) {
                    (T::Num(c), e) | (e, T::Num(c)) => {
                        let x = self.compile(e, vars, w)?;
                        self.times(*c as u64 & w.mask, x, w)?
                    }
                    _ => return None,
                },
                "Add" | "Sub" | "And" | "Or" | "Xor" => {
                    let x = self.compile(&a[0], vars, w)?;
                    let y = self.compile(&a[1], vars, w)?;
                    match op.as_str() {
                        "Add" => self.adder(x, y, false)?,
                        "Sub" => {
                            let ny = self.gate(Gate::Not(y));
                            self.adder(x, ny, true)?
                        }
                        "And" => self.gate(Gate::And(x, y)),
                        "Or" => self.gate(Gate::Or(x, y)),
                        _ => self.gate(Gate::Xor(x, y)),
                    }
                }
                _ => return None,
            },
        })
    }
}

/// Whether `f` and `g` agree on all inputs; `None` if a term has an unsupported
/// operation or the carry states grow too many.
fn equal(f: &T, g: &T, vars: &[String], w: &Width) -> Option<bool> {
    let mut c = Circuit::default();
    let (fo, go) = (c.compile(f, vars, w)?, c.compile(g, vars, w)?);
    let n = vars.len();
    let mut states: HashSet<u128> = HashSet::from([c.init]);
    let mut v = vec![false; c.gates.len()];
    for i in 0..w.w {
        let mut next = HashSet::new();
        for &s in &states {
            for inp in 0..1usize << n {
                let mut ns = s;
                for (k, g) in c.gates.iter().enumerate() {
                    v[k] = match *g {
                        Gate::In(j) => inp >> j & 1 == 1,
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
                if v[fo] != v[go] {
                    return Some(false);
                }
                next.insert(ns);
            }
        }
        if next.len() > MAX_STATES {
            return None;
        }
        states = next;
    }
    Some(true)
}

fn var_names(t: &T, out: &mut Vec<String>) {
    match t {
        T::Var(v) if !out.contains(v) => out.push(v.clone()),
        T::Op(_, a) => a.iter().for_each(|x| var_names(x, out)),
        _ => {}
    }
}

fn rename(t: &T, vars: &[String]) -> T {
    match t {
        T::Var(j) => T::Var(vars[j.parse::<usize>().unwrap()].clone()),
        T::Op(op, a) => T::Op(op.clone(), a.iter().map(|x| rename(x, vars)).collect()),
        _ => t.clone(),
    }
}

/// The smallest proven-equal expression for `t`, if smaller than `t`.
pub(crate) fn replacement(t: &T, w: &Width) -> Option<T> {
    if !(2..=MAX_TRY).contains(&size(t)) {
        return None;
    }
    let mut vars = Vec::new();
    var_names(t, &mut vars);
    if vars.is_empty() || vars.len() > MAX_VARS {
        return None;
    }
    let fp = values(t, &vars, &points(w), w)?;
    let cand = rename(table(vars.len(), w).by_fp.get(&fp)?, &vars);
    (size(&cand) < size(t) && equal(t, &cand, &vars, w)?).then_some(cand)
}

/// `t` with each outermost replaceable subterm replaced.
pub(crate) fn simplify(t: &T, w: &Width) -> T {
    let T::Op(op, a) = t else { return t.clone() };
    if let Some(r) = replacement(t, w) {
        return r;
    }
    T::Op(op.clone(), a.iter().map(|x| simplify(x, w)).collect())
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
        let op = ["Add", "Sub", "And", "Or", "Xor", "Not", "Neg", "Mul"][(r >> 16) as usize % 8];
        match op {
            "Not" | "Neg" => T::Op(op.into(), vec![random_term(h, depth - 1)]),
            "Mul" => T::Op(op.into(), vec![T::Num((r >> 24) as i64 % 9 - 4), random_term(h, depth - 1)]),
            _ => T::Op(op.into(), vec![random_term(h, depth - 1), random_term(h, depth - 1)]),
        }
    }

    #[test]
    fn proof_matches_exhaustive_check_at_8_bits() {
        let w = Width::new(8);
        let vars = vec!["x".to_string(), "y".to_string()];
        let ty = crate::eval::NumType { bits: 8, signed: false };
        let mut h = 0x1234_5678_9abc_def1u64;
        let (mut proved, mut refuted) = (0, 0);
        for _ in 0..3000 {
            let (f, g) = (random_term(&mut h, 3), random_term(&mut h, 1));
            let Some(eq) = equal(&f, &g, &vars, &w) else { continue };
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
}
