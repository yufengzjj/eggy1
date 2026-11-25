//! Counts and times per candidate source and pass, collected while `enable` was called
//! (`--stats`, or `bench` with `EGGY_STATS`); off, every call here returns at once.
//!
//! Keys: `pre/NAME/...` pre-pass candidates, `egglog/...` and `round/...` rounds,
//! `polish/NAME/run|won`, `final/ORIGIN`, and `pass/NAME` for the passes inside a rebuild
//! (time includes the passes they call), with `pass/NAME/smaller` when the result was
//! smaller than the pass's input and `pass/NAME/won` when it was the form kept among
//! alternatives.

use crate::eval::{Term, size};
use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::time::Instant;

static ON: AtomicBool = AtomicBool::new(false);
/// Key → (count, seconds).
static COUNTS: Mutex<BTreeMap<String, (u64, f64)>> = Mutex::new(BTreeMap::new());
/// Printed form of each pre-pass candidate of the current call → its source.
static LABELS: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

/// Starts collecting.
pub fn enable() {
    ON.store(true, Relaxed);
}

pub fn on() -> bool {
    ON.load(Relaxed)
}

/// Counts `key` once and adds `secs` to its time.
pub fn add(key: &str, secs: f64) {
    if !on() {
        return;
    }
    let mut c = COUNTS.lock().unwrap();
    let e = c.entry(key.to_string()).or_insert((0, 0.0));
    e.0 += 1;
    e.1 += secs;
}

/// Seconds since `start`.
pub fn since(start: Instant) -> f64 {
    start.elapsed().as_secs_f64()
}

/// A pass result whose size can be compared with the pass's input.
pub trait Out {
    fn smaller_than(&self, n: usize) -> bool;
}

impl Out for Term {
    fn smaller_than(&self, n: usize) -> bool {
        size(self) < n
    }
}

impl Out for Option<Term> {
    fn smaller_than(&self, n: usize) -> bool {
        self.as_ref().is_some_and(|t| size(t) < n)
    }
}

/// `f()`, counted and timed under `pass/NAME`, and under `pass/NAME/smaller` when its
/// result is smaller than `input`.
pub fn pass<R: Out>(name: &str, input: &Term, f: impl FnOnce() -> R) -> R {
    if !on() {
        return f();
    }
    let clock = Instant::now();
    let r = f();
    add(&format!("pass/{name}"), since(clock));
    if r.smaller_than(size(input)) {
        add(&format!("pass/{name}/smaller"), 0.0);
    }
    r
}

/// `f()`, counted and timed under `pass/NAME`.
pub fn time<R>(name: &str, f: impl FnOnce() -> R) -> R {
    if !on() {
        return f();
    }
    let clock = Instant::now();
    let r = f();
    add(&format!("pass/{name}"), since(clock));
    r
}

/// Counts `pass/NAME/won`: its form was kept among alternatives.
pub fn won(name: &str) {
    if on() {
        add(&format!("pass/{name}/won"), 0.0);
    }
}

/// Remembers that the pre-pass candidate `egg` came from `source`.
pub fn label(egg: &str, source: &str) {
    if on() {
        LABELS.lock().unwrap().entry(egg.to_string()).or_insert_with(|| source.to_string());
    }
}

/// The source `label` gave `egg`, if any.
pub fn source_of(egg: &str) -> Option<String> {
    if !on() {
        return None;
    }
    LABELS.lock().unwrap().get(egg).cloned()
}

/// The counts so far, cleared with the labels.
pub fn take() -> BTreeMap<String, (u64, f64)> {
    LABELS.lock().unwrap().clear();
    std::mem::take(&mut *COUNTS.lock().unwrap())
}

/// Features of an input term, as `name=value,...`, so pass counts can be grouped by them:
/// size, distinct variables, depth, products of two non-constant factors, bitwise
/// operations with a constant operand, arithmetic operations directly under a bitwise
/// one, shifts, and divisions, remainders and mulhi.
pub fn features(t: &Term) -> String {
    use crate::eval::Op;
    #[derive(Default)]
    struct F {
        depth: usize,
        mul: usize,
        bitconst: usize,
        arith_in_bit: usize,
        shift: usize,
        div: usize,
    }
    fn go(t: &Term, d: usize, f: &mut F) {
        f.depth = f.depth.max(d);
        let Term::Op(op, a) = t else { return };
        let bit = matches!(op, Op::And | Op::Or | Op::Xor);
        let arith = |x: &Term| matches!(x, Term::Op(Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Shl, _));
        match op {
            Op::Mul if a.iter().all(|x| !matches!(x, Term::Num(_))) => f.mul += 1,
            Op::Shl | Op::Shr => f.shift += 1,
            Op::Div | Op::Mod | Op::Mulhi => f.div += 1,
            _ if bit && a.iter().any(|x| matches!(x, Term::Num(_))) => f.bitconst += 1,
            _ => {}
        }
        if bit || matches!(op, Op::Not) {
            f.arith_in_bit += a.iter().filter(|x| arith(x)).count();
        }
        a.iter().for_each(|x| go(x, d + 1, f));
    }
    let mut f = F::default();
    go(t, 0, &mut f);
    format!(
        "size={},vars={},depth={},mul={},bitconst={},arith_in_bit={},shift={},div={}",
        size(t),
        crate::eval::vars(t).len(),
        f.depth,
        f.mul,
        f.bitconst,
        f.arith_in_bit,
        f.shift,
        f.div
    )
}

/// The counts as a table, grouped by key prefix.
pub fn report(counts: &BTreeMap<String, (u64, f64)>) -> String {
    let mut out = String::new();
    let mut last = "";
    for (key, (n, secs)) in counts {
        let group = key.split('/').next().unwrap_or("");
        if group != last {
            out.push_str(&format!("{group}:\n"));
            last = group;
        }
        out.push_str(&format!("  {key:48} {n:8} {secs:10.4}s\n"));
    }
    out
}
