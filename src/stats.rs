//! Counts and times per candidate source and pass, collected while `enable` was called
//! (`--stats`, or `bench` with `EGGY_STATS`); off, every call here returns at once.
//!
//! Keys: `pre/NAME/...` pre-pass candidates, `egglog/...` and `round/...` rounds,
//! `polish/NAME/run|won|gain`, `final/ORIGIN`, and `pass/NAME` for the passes inside a
//! rebuild: its time includes the passes it calls, `pass/NAME/self` has the time without
//! them, `pass/NAME/smaller` counts results smaller than the pass's input, `pass/NAME/won`
//! results kept among alternatives, and `pass/NAME/gain` sums the nodes a pass saved: for
//! a pass in a chain its input's size less its result's, for one of several alternatives
//! the next best alternative's size (or the input's) less the kept one's.

use crate::eval::{Term, size};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::time::Instant;

static ON: AtomicBool = AtomicBool::new(false);
/// Key → (count, seconds).
static COUNTS: Mutex<BTreeMap<String, (u64, f64)>> = Mutex::new(BTreeMap::new());
/// Printed form of each pre-pass candidate of the current call → its source.
static LABELS: Mutex<BTreeMap<String, String>> = Mutex::new(BTreeMap::new());

thread_local! {
    /// Time spent in nested passes, one entry per pass being run.
    static NESTED: RefCell<Vec<f64>> = const { RefCell::new(Vec::new()) };
}

/// Starts collecting.
pub fn enable() {
    ON.store(true, Relaxed);
}

pub fn on() -> bool {
    ON.load(Relaxed)
}

/// Adds `n` to the count of `key` and `secs` to its time.
pub fn add_n(key: &str, n: u64, secs: f64) {
    if !on() {
        return;
    }
    let mut c = COUNTS.lock().unwrap();
    let e = c.entry(key.to_string()).or_insert((0, 0.0));
    e.0 += n;
    e.1 += secs;
}

/// Counts `key` once and adds `secs` to its time.
pub fn add(key: &str, secs: f64) {
    add_n(key, 1, secs);
}

/// Seconds since `start`.
pub fn since(start: Instant) -> f64 {
    start.elapsed().as_secs_f64()
}

/// A pass result whose size can be compared with the pass's input.
pub trait Out {
    fn out_size(&self) -> Option<usize>;
}

impl Out for Term {
    fn out_size(&self) -> Option<usize> {
        Some(size(self))
    }
}

impl Out for Option<Term> {
    fn out_size(&self) -> Option<usize> {
        self.as_ref().map(size)
    }
}

/// `f()`, counted and timed under `pass/NAME` and `pass/NAME/self`.
pub fn time<R>(name: &str, f: impl FnOnce() -> R) -> R {
    if !on() {
        return f();
    }
    NESTED.with(|n| n.borrow_mut().push(0.0));
    let clock = Instant::now();
    let r = f();
    let secs = since(clock);
    let nested = NESTED.with(|n| {
        let mut n = n.borrow_mut();
        let own = n.pop().unwrap_or(0.0);
        if let Some(parent) = n.last_mut() {
            *parent += secs;
        }
        own
    });
    add(&format!("pass/{name}"), secs);
    add(&format!("pass/{name}/self"), (secs - nested).max(0.0));
    r
}

/// `time` for a pass in a chain: also counts `pass/NAME/smaller` and adds the nodes it
/// saved to `pass/NAME/gain`.
pub fn pass<R: Out>(name: &str, input: &Term, f: impl FnOnce() -> R) -> R {
    if !on() {
        return f();
    }
    let r = time(name, f);
    smaller(name, size(input), r.out_size());
    if let Some(out) = r.out_size().filter(|&o| o < size(input)) {
        add_n(&format!("pass/{name}/gain"), (size(input) - out) as u64, 0.0);
    }
    r
}

/// `time` for one of several alternatives: also counts `pass/NAME/smaller`; its gain is
/// counted by `won` if it is kept.
pub fn try_pass<R: Out>(name: &str, input: &Term, f: impl FnOnce() -> R) -> R {
    if !on() {
        return f();
    }
    let r = time(name, f);
    smaller(name, size(input), r.out_size());
    r
}

fn smaller(name: &str, input: usize, out: Option<usize>) {
    if out.is_some_and(|o| o < input) {
        add(&format!("pass/{name}/smaller"), 0.0);
    }
}

/// Counts `pass/NAME/won`, its form kept among alternatives, of size `kept` where the
/// next best had `next`.
pub fn won(name: &str, next: usize, kept: usize) {
    if on() {
        add(&format!("pass/{name}/won"), 0.0);
        add_n(&format!("pass/{name}/gain"), next.saturating_sub(kept) as u64, 0.0);
    }
}

/// `won` for `name` among alternatives of the given sizes, when its form is smaller than
/// the input of size `input`; the next best is the smallest other one or the input.
pub fn won_among(name: &str, sizes: &[(&str, usize)], input: usize) {
    if !on() {
        return;
    }
    let Some(&(_, kept)) = sizes.iter().find(|(n, _)| *n == name) else { return };
    if kept < input {
        let next = sizes.iter().filter(|(n, _)| *n != name).map(|(_, s)| *s).fold(input, usize::min);
        won(name, next, kept);
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
