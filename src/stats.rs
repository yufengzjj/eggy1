//! Counts and times per candidate source and pass, collected while `enable` was called
//! (`--stats`, or `bench` with `EGGY_STATS`); off, every call here returns at once.
//!
//! Keys: `pre/NAME/...` pre-pass candidates, `egglog/...` and `round/...` rounds,
//! `polish_NAME/run|won|gain`, `final/ORIGIN`, and `pass/NAME` for the passes inside a
//! rebuild: its time includes the passes it calls, `pass/NAME/self` has the time without
//! them, `pass/NAME/smaller` counts results smaller than the pass's input, `pass/NAME/won`
//! results kept among alternatives, and `pass/NAME/gain` sums the nodes a pass saved: for
//! a pass in a chain its input's size less its result's, for one of several alternatives
//! the next best alternative's size (or the input's) less the kept one's. `KEY/survived`
//! sums the gain of the forms the final result still contains (`settle`).

use crate::eval::{Term, size};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};
use std::time::Instant;

static ON: AtomicBool = AtomicBool::new(false);
/// Key → (count, seconds).
static COUNTS: Mutex<BTreeMap<String, (u64, f64)>> = Mutex::new(BTreeMap::new());
/// Forms that saved nodes: hash, key and gain, for `settle`.
static PRODUCED: Mutex<Vec<(u64, String, u64)>> = Mutex::new(Vec::new());
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
    fn term(&self) -> Option<&Term>;
    /// The result of the pass turned off: its input, or no form.
    fn skipped(input: &Term) -> Self;
}

impl Out for Term {
    fn term(&self) -> Option<&Term> {
        Some(self)
    }
    fn skipped(input: &Term) -> Term {
        input.clone()
    }
}

impl Out for Option<Term> {
    fn term(&self) -> Option<&Term> {
        self.as_ref()
    }
    fn skipped(_: &Term) -> Option<Term> {
        None
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

/// `time`, or the default result when the pass is turned off (`rust_vars::is_off`).
pub fn optional<R: Default>(name: &str, f: impl FnOnce() -> R) -> R {
    if crate::rust_vars::is_off(name) {
        return R::default();
    }
    time(name, f)
}

/// `time` for a pass in a chain, which returns its input when turned off: also counts
/// `pass/NAME/smaller` and adds the nodes it saved to `pass/NAME/gain`.
pub fn pass<R: Out>(name: &str, input: &Term, f: impl FnOnce() -> R) -> R {
    if crate::rust_vars::is_off(name) {
        return R::skipped(input);
    }
    if !on() {
        return f();
    }
    let r = time(name, f);
    if let Some(out) = r.term().filter(|o| size(o) < size(input)) {
        add(&format!("pass/{name}/smaller"), 0.0);
        produced(&format!("pass/{name}"), out, size(input) - size(out));
    }
    r
}

/// `time` for one of several alternatives, which gives no form when turned off: also
/// counts `pass/NAME/smaller`; its gain is counted by `won` if it is kept.
pub fn try_pass<R: Out>(name: &str, input: &Term, f: impl FnOnce() -> R) -> R {
    if crate::rust_vars::is_off(name) {
        return R::skipped(input);
    }
    if !on() {
        return f();
    }
    let r = time(name, f);
    if r.term().is_some_and(|o| size(o) < size(input)) {
        add(&format!("pass/{name}/smaller"), 0.0);
    }
    r
}

/// Counts `pass/NAME/won`, its form `kept` kept among alternatives where the next best
/// had size `next`.
pub fn won(name: &str, next: usize, kept: &Term) {
    if on() {
        add(&format!("pass/{name}/won"), 0.0);
        produced(&format!("pass/{name}"), kept, next.saturating_sub(size(kept)));
    }
}

/// `won` for `name` among alternatives of the given sizes, when its form `kept` is smaller
/// than the input of size `input`; the next best is the smallest other one or the input.
pub fn won_among(name: &str, sizes: &[(&str, usize)], input: usize, kept: &Term) {
    if !on() || size(kept) >= input {
        return;
    }
    let next = sizes.iter().filter(|(n, _)| *n != name).map(|(_, s)| *s).fold(input, usize::min);
    won(name, next, kept);
}

/// Bits of the numeric type of the current run, for comparing constants in `settle`.
static MASK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(u64::MAX);

/// Sets the width constants are compared in by `settle`.
pub fn set_width(w: u32) {
    MASK.store(if w >= 64 { u64::MAX } else { (1 << w) - 1 }, Relaxed);
}

/// A hash equal for terms that differ only in the order and grouping of the operands of
/// `+ * & | ^` and in how constants are extended past the type's width, since the rules
/// rearrange those freely.
fn term_hash(t: &Term) -> u64 {
    use crate::eval::Op;
    use std::hash::{Hash, Hasher};
    fn flat<'a>(t: &'a Term, op: Op, out: &mut Vec<&'a Term>) {
        match t {
            Term::Op(o, a) if *o == op => a.iter().for_each(|x| flat(x, op, out)),
            _ => out.push(t),
        }
    }
    let mut h = std::collections::hash_map::DefaultHasher::new();
    match t {
        Term::Num(v) => (0u8, *v as u64 & MASK.load(Relaxed)).hash(&mut h),
        Term::Var(v) => (1u8, v).hash(&mut h),
        Term::Op(op @ (Op::Add | Op::Mul | Op::And | Op::Or | Op::Xor), _) => {
            let mut parts = Vec::new();
            flat(t, *op, &mut parts);
            let mut hs: Vec<u64> = parts.into_iter().map(term_hash).collect();
            hs.sort_unstable();
            (2u8, op, hs).hash(&mut h);
        }
        Term::Op(op, a) => (3u8, op, a.iter().map(term_hash).collect::<Vec<_>>()).hash(&mut h),
    }
    h.finish()
}

/// Adds `gain` to `KEY/gain` and remembers the form, so `settle` can add it to
/// `KEY/survived` if the final result contains it.
pub fn produced(key: &str, form: &Term, gain: usize) {
    if !on() || gain == 0 {
        return;
    }
    add_n(&format!("{key}/gain"), gain as u64, 0.0);
    PRODUCED.lock().unwrap().push((term_hash(form), key.to_string(), gain as u64));
}

/// Adds the gain of each form `produced` remembered to `KEY/survived` when `result` has it
/// as a subterm, and forgets them. Forms the rules rewrote count as lost, so this is a
/// lower bound on what reached the result.
pub fn settle(result: &Term) {
    if !on() {
        return;
    }
    fn walk(t: &Term, out: &mut std::collections::HashSet<u64>) {
        out.insert(term_hash(t));
        if let Term::Op(_, a) = t {
            a.iter().for_each(|x| walk(x, out));
        }
    }
    let mut seen = std::collections::HashSet::new();
    walk(result, &mut seen);
    let produced = std::mem::take(&mut *PRODUCED.lock().unwrap());
    for (h, key, gain) in produced {
        if seen.contains(&h) {
            add_n(&format!("{key}/survived"), gain, 0.0);
        }
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
    PRODUCED.lock().unwrap().clear();
    std::mem::take(&mut *COUNTS.lock().unwrap())
}

/// Features of an input term: size, distinct variables, depth, products of two
/// non-constant factors, bitwise operations with a constant operand, arithmetic operations
/// directly under a bitwise one, shifts, and divisions, remainders and mulhi.
#[derive(Default)]
pub struct Shape {
    pub size: usize,
    pub vars: usize,
    pub depth: usize,
    pub mul: usize,
    pub bitconst: usize,
    pub arith_in_bit: usize,
    pub shift: usize,
    pub div: usize,
}

pub fn shape(t: &Term) -> Shape {
    use crate::eval::Op;
    /// Whether `t` has no variable.
    fn go(t: &Term, d: usize, f: &mut Shape) -> bool {
        f.depth = f.depth.max(d);
        let Term::Op(op, a) = t else { return !matches!(t, Term::Var(_)) };
        let konst: Vec<bool> = a.iter().map(|x| go(x, d + 1, f)).collect();
        let bit = matches!(op, Op::And | Op::Or | Op::Xor);
        let arith = |x: &Term| matches!(x, Term::Op(Op::Add | Op::Sub | Op::Mul | Op::Neg | Op::Shl, _));
        match op {
            Op::Mul if !konst.contains(&true) => f.mul += 1,
            Op::Shl | Op::Shr => f.shift += 1,
            Op::Div | Op::Mod | Op::Mulhi => f.div += 1,
            _ if bit && konst.contains(&true) => f.bitconst += 1,
            _ => {}
        }
        if bit || matches!(op, Op::Not) {
            f.arith_in_bit += a.iter().filter(|x| arith(x)).count();
        }
        !konst.contains(&false)
    }
    let mut f = Shape { size: size(t), vars: crate::eval::vars(t).len(), ..Shape::default() };
    go(t, 0, &mut f);
    f
}

/// `shape(t)` as `name=value,...`, so pass counts can be grouped by it.
pub fn features(t: &Term) -> String {
    let f = shape(t);
    format!(
        "size={},vars={},depth={},mul={},bitconst={},arith_in_bit={},shift={},div={}",
        f.size,
        f.vars,
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
