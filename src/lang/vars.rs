//! The global variables of the runs on a thread: their positions and kinds, their values,
//! dynamically scoped by shallow binding, the budgets and the deadline, and the reads the memos
//! record.

use super::host::{DEFAULT, LIMIT0, RUST_VARS, SETTING0, is_unread, rust_var};

/// How the Rust code uses a variable, which decides how a binding combines with the outer
/// ones.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarKind {
    /// An `INNER` pass: 0 off, any other value (also `none`) on.
    Pass,
    /// A `FLAGS` switch: 0 off, any other value (also `none`) on.
    Flag,
    /// An entry of `LIMITS`.
    Limit,
    /// An entry of `UNREAD`.
    Unread,
    /// `semi_leaves`, `relate_leaves` and the `RUN` settings.
    Setting,
    /// `rewrites`, `bit_split_budget`: a binding is at most what the outer one has left, and
    /// what is used inside is used up outside too.
    Budget,
    /// `time_limit`, a deadline in ns of `epoch_ns`: a binding is never later than the outer
    /// one.
    Deadline,
    /// A variable a source file defines that the Rust code does not read.
    Global,
}

/// A variable of the runs on this thread: one the Rust code reads (an `INNER` pass, a `FLAGS`
/// switch, a `LIMITS` entry, a `SETTINGS` entry, a `RUN` setting or the deadline, at a fixed
/// position below `RUST_VARS`), or one only the pipelines read.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Var {
    pub name: &'static str,
    pub kind: VarKind,
}

/// The read bit that stands for all the `LIMITS` (`limits_key`).
const LIMITS_BIT: usize = RUST_VARS;
/// The read bit that stands for all the variables past `RUST_VARS` (`globals_hash`).
const GLOBALS_BIT: usize = RUST_VARS + 1;
const READ_WORDS: usize = (RUST_VARS + 2).div_ceil(64);

/// A set of variables below `RUST_VARS`, `LIMITS_BIT` and `GLOBALS_BIT`, as the memos record
/// what a computation read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReadSet([u64; READ_WORDS]);

impl ReadSet {
    pub const EMPTY: ReadSet = ReadSet([0; READ_WORDS]);

    pub fn union(mut self, o: ReadSet) -> ReadSet {
        self.0.iter_mut().zip(o.0).for_each(|(a, b)| *a |= b);
        self
    }

    pub fn remove(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }

    pub(crate) fn ones(self) -> impl Iterator<Item = usize> {
        self.0.into_iter().enumerate().flat_map(|(k, mut bits)| {
            std::iter::from_fn(move || {
                let i = bits.trailing_zeros() as usize;
                bits &= bits.wrapping_sub(1);
                (i < 64).then_some(k * 64 + i)
            })
        })
    }
}

/// `none`, no limit: the value of every variable until it is assigned.
pub const NONE: u64 = u64::MAX;

/// The kind of the variable at position `i`.
pub fn kind(i: usize) -> VarKind {
    if i < RUST_VARS { rust_var(i).1 } else { VarKind::Global }
}

/// The names of the variables past `RUST_VARS`, in the order the source files first defined
/// them in this process; each keeps its position.
static GLOBALS: std::sync::RwLock<Vec<&'static str>> = std::sync::RwLock::new(Vec::new());

/// The number of variables with a position so far.
fn count() -> usize {
    RUST_VARS + GLOBALS.read().unwrap().len()
}

/// The variable at position `i`.
pub fn var(i: usize) -> Var {
    let name = if i < RUST_VARS { rust_var(i).0 } else { GLOBALS.read().unwrap()[i - RUST_VARS] };
    Var { name, kind: kind(i) }
}

thread_local! {
    /// The variables past `RUST_VARS` that the source files of the parse under way on this
    /// thread define (`Passes::globals`), while one is.
    pub(crate) static PARSED: std::cell::RefCell<Option<Vec<usize>>> = const { std::cell::RefCell::new(None) };
}

/// The position of the variable `name`: one the Rust code reads, or one that `default.pipe` or
/// the source files of the parse under way define.
pub fn var_index(name: &str) -> Option<usize> {
    if let Some(i) = (0..RUST_VARS).find(|i| rust_var(*i).0 == name) {
        return Some(i);
    }
    let i = GLOBALS.read().unwrap().iter().position(|n| *n == name)? + RUST_VARS;
    match PARSED.with(|p| p.borrow().as_ref().map(|g| g.contains(&i))) {
        Some(found) => found.then_some(i),
        None => DEFAULT.0.globals.contains(&i).then_some(i),
    }
}

/// `f` with the variables `globals` defined for `var_index`, as a parse that defines them sees
/// them; `f` may add more.
pub(crate) fn parsing<R>(globals: &mut Vec<usize>, f: impl FnOnce() -> R) -> R {
    let outer = PARSED.with(|p| p.replace(Some(std::mem::take(globals))));
    let r = f();
    *globals = PARSED.with(|p| p.replace(outer)).unwrap_or_default();
    r
}

/// The position of a variable past `RUST_VARS` named `name`, given one when it has none, and
/// recorded as defined by the parse under way.
pub(crate) fn global_slot(name: &str) -> usize {
    let i = {
        let mut g = GLOBALS.write().unwrap();
        match g.iter().position(|n| *n == name) {
            Some(i) => RUST_VARS + i,
            None => {
                g.push(intern(name));
                RUST_VARS + g.len() - 1
            }
        }
    };
    PARSED.with(|p| p.borrow_mut().get_or_insert_with(Vec::new).push(i));
    i
}

/// The names of all variables `var_index` finds, in order.
pub fn var_names() -> Vec<&'static str> {
    (0..count()).map(|i| var(i).name).filter(|n| var_index(n).is_some()).collect()
}

/// Whether the variable at `i` is a switch: an `INNER` pass or a `FLAGS` switch.
pub fn is_switch(i: usize) -> bool {
    matches!(kind(i), VarKind::Pass | VarKind::Flag)
}

thread_local! {
    /// The current value of each variable. Shallow binding: `bind` keeps the outer value in
    /// the innermost scope of `FRAMES`, which puts it back when it ends.
    static VARS: [std::cell::Cell<u64>; RUST_VARS] = const { [const { std::cell::Cell::new(NONE) }; RUST_VARS] };
    /// The values of the variables past `RUST_VARS`, by position less `RUST_VARS`; `none`
    /// past the end.
    static GLOBAL_VALS: std::cell::RefCell<Vec<u64>> = const { std::cell::RefCell::new(Vec::new()) };
    /// A hash of `GLOBAL_VALS`, made when first needed after a `set` of one of them.
    static GLOBALS_HASH: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
    /// A hash of the values of the `LIMITS`, kept up to date by `set`.
    static LIMITS_HASH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The scopes under way, innermost last: each variable bound there, its value outside and
    /// the value bound.
    static FRAMES: std::cell::RefCell<Vec<Vec<(usize, u64, u64)>>> = const { std::cell::RefCell::new(Vec::new()) };
    /// Bits of the variables read since the last `swap_read`.
    static READ: [std::cell::Cell<u64>; READ_WORDS] = const { [const { std::cell::Cell::new(0) }; READ_WORDS] };
}

/// The value of variable `i`, not recorded as read.
pub fn get(i: usize) -> u64 {
    if i < RUST_VARS { VARS.with(|v| v[i].get()) } else { GLOBAL_VALS.with(|g| g.borrow().get(i - RUST_VARS).copied().unwrap_or(NONE)) }
}

/// The value of variable `i`, recorded as read for the memos (`swap_read`).
pub fn read(i: usize) -> u64 {
    mark_read(if i < RUST_VARS { i } else { GLOBALS_BIT });
    get(i)
}

/// `read` for a pipeline: the `UNREAD` limits are not recorded.
pub fn read_var(i: usize) -> u64 {
    if is_unread(i) { get(i) } else { read(i) }
}

fn mark_read(i: usize) {
    READ.with(|r| {
        let c = &r[i / 64];
        c.set(c.get() | 1 << (i % 64));
    });
}

/// Sets variable `i` outside any binding: a scope that binds it later restores this value.
pub fn set(i: usize, v: u64) {
    if i >= RUST_VARS {
        GLOBAL_VALS.with(|g| {
            let mut g = g.borrow_mut();
            let k = i - RUST_VARS;
            if k >= g.len() {
                g.resize(k + 1, NONE);
            }
            g[k] = v;
        });
        GLOBALS_HASH.with(|c| c.set(None));
        return;
    }
    VARS.with(|a| {
        a[i].set(v);
        if (LIMIT0..SETTING0).contains(&i) {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            a[LIMIT0..SETTING0].iter().for_each(|c| c.get().hash(&mut h));
            LIMITS_HASH.with(|c| c.set(h.finish()));
        }
    });
}

/// Binds variable `i` to `v` in the innermost scope (`in_scope`) until it ends; a budget is
/// at most what the outer binding has left, a deadline no later than the outer one.
pub fn bind(i: usize, v: u64) {
    let cur = get(i);
    let kind = kind(i);
    let new = FRAMES.with(|f| {
        let mut f = f.borrow_mut();
        let Some(frame) = f.last_mut() else { return v };
        let slot = frame.iter().position(|e| e.0 == i);
        let outer = match slot {
            Some(s) if kind == VarKind::Budget => {
                let e = &mut frame[s];
                e.1 = e.1.saturating_sub(e.2.saturating_sub(cur));
                e.1
            }
            Some(s) => frame[s].1,
            None => cur,
        };
        let new = match kind {
            VarKind::Budget | VarKind::Deadline => v.min(outer),
            _ => v,
        };
        match slot {
            Some(s) => frame[s].2 = new,
            None => frame.push((i, cur, new)),
        }
        new
    });
    set(i, new);
}

/// Takes one from the budget `i`; false when it is used up.
pub fn take(i: usize) -> bool {
    let left = get(i);
    set(i, left.saturating_sub(1));
    left > 0
}

/// `f` as a scope: the variables bound inside it are back after, a budget less what was
/// used inside.
pub fn in_scope<R>(f: impl FnOnce() -> R) -> R {
    FRAMES.with(|fr| fr.borrow_mut().push(Vec::new()));
    let r = f();
    let frame = FRAMES.with(|fr| fr.borrow_mut().pop()).unwrap_or_default();
    for (i, old, bound) in frame {
        let back = match kind(i) {
            VarKind::Budget => old.saturating_sub(bound.saturating_sub(get(i))),
            _ => old,
        };
        set(i, back);
    }
    r
}

/// The variables read since the last call, which sets them to `v`.
pub fn swap_read(v: ReadSet) -> ReadSet {
    READ.with(|r| ReadSet(std::array::from_fn(|k| r[k].replace(v.0[k]))))
}

/// The values of the variables in `bits`, in order.
pub fn values(bits: ReadSet) -> Vec<u64> {
    VARS.with(|a| bits.ones().map(|i| value_at(a, i)).collect())
}

/// Whether the variables in `bits` have the values `vals` (`values`).
pub fn same_values(bits: ReadSet, vals: &[u64]) -> bool {
    VARS.with(|a| bits.ones().zip(vals).all(|(i, v)| value_at(a, i) == *v))
}

fn value_at(a: &[std::cell::Cell<u64>; RUST_VARS], i: usize) -> u64 {
    match i {
        LIMITS_BIT => LIMITS_HASH.with(|c| c.get()),
        GLOBALS_BIT => globals_hash(),
        _ => a[i].get(),
    }
}

/// A hash of the values of the variables past `RUST_VARS` on this thread.
fn globals_hash() -> u64 {
    GLOBALS_HASH.with(|c| {
        if let Some(v) = c.get() {
            return v;
        }
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        GLOBAL_VALS.with(|g| g.borrow().iter().enumerate().filter(|(_, v)| **v != NONE).for_each(|e| e.hash(&mut h)));
        let v = h.finish();
        c.set(Some(v));
        v
    })
}

/// The values of all variables but the budgets and the deadline, which a result depends on
/// only where they cut it short.
pub fn key() -> Vec<u64> {
    (0..count()).filter(|i| !matches!(kind(*i), VarKind::Budget | VarKind::Deadline)).map(get).collect()
}

/// A hash of the `LIMITS` on this thread, for the key of a memo that may depend on any of
/// them; recorded as a read of all of them.
pub fn limits_key() -> u64 {
    mark_read(LIMITS_BIT);
    LIMITS_HASH.with(|c| c.get())
}

/// Nanoseconds since the first call in the process, the unit of `DEADLINE`.
pub fn epoch_ns() -> u64 {
    static EPOCH: std::sync::LazyLock<std::time::Instant> = std::sync::LazyLock::new(std::time::Instant::now);
    EPOCH.elapsed().as_nanos() as u64
}

/// `s` for as long as the program runs: the name of a variable a source file defines.
pub(crate) fn intern(s: &str) -> &'static str {
    static NAMES: std::sync::Mutex<Vec<&'static str>> = std::sync::Mutex::new(Vec::new());
    let mut names = NAMES.lock().unwrap();
    if let Some(n) = names.iter().find(|n| **n == s) {
        return n;
    }
    let n: &'static str = Box::leak(s.to_string().into_boxed_str());
    names.push(n);
    n
}
