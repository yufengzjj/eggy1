//! The pass pipeline of `simplify`: the egglog schedule of a round, which pre-pass candidates
//! are built, how the rounds run and which polish passes run in what order. `Passes::default()` is the tuned pipeline;
//! `--passes` changes it with a spec such as `pre-=halve_input polish=push_not,factor extra=0`.

use crate::pipe_lang as lang;
use std::fmt;

/// Pre-pass candidates built beside the first rebuild, in the order they are computed.
pub const PRE: [&str; 9] = [
    "unified",
    "no_wide",
    "split_bits",
    "halve_first",
    "over_products",
    "over_const_bitwise",
    "over_shared_bitwise",
    "halve_input",
    "unclustered",
];

/// Passes inside a rebuild that `off` can turn off: one in a chain then returns its input,
/// one of several alternatives gives no form.
pub const INNER: [&str; 34] = [
    "lowbits",
    "unshift",
    "tfunc_whole",
    "relate",
    "tfunc",
    "unify_operands",
    "recombine",
    "cut_products",
    "shifted_xor",
    "simplify_rebuilt",
    "cluster_regions",
    "simba",
    "small_blocks",
    "wide_blocks",
    "poly_mba",
    "poly/masked",
    "rebuild_values",
    "common_multiple",
    "related_leaves",
    "one_wide_term",
    "semi_linear",
    "drop_unused",
    "clustered",
    "peel",
    "peel_clustered",
    "semi/grouped",
    "semi/peel_grouped",
    "semi/shapes",
    "semi/pairs",
    "semi/peel_shapes",
    "semi/semi_split",
    "semi/scaled",
    "semi/bit_split",
    "semi/short_consts",
];

/// Switches besides the `INNER` passes: `cut` (off unless turned on: a step skipped past a
/// `time_limit` makes the run cut, `crate::pipe::cut`), `rerun_input` (rerun the first round
/// with the input when its result still mixes arithmetic into bitwise operations),
/// `prove_minimal` (take a rebuild proved minimal as the extraction without saturating).
pub const FLAGS: [&str; 3] = ["cut", "rerun_input", "prove_minimal"];

/// The `INNER` pass or `FLAGS` switch named `name`, which `(on NAME)` and `(off NAME)` take.
pub fn switch(name: &str) -> Option<&'static str> {
    INNER.iter().chain(&FLAGS).find(|k| **k == name).copied()
}

macro_rules! limits {
    ($($(#[doc = $doc:literal])* $id:ident $name:literal = $default:expr;)*) => {
        /// Numeric limits of the passes inside a rebuild; `--passes` sets them as `NAME=value`.
        #[derive(Clone, Copy, Debug, PartialEq)]
        pub enum Limit {
            $($(#[doc = $doc])* $id,)*
        }
        /// Names and defaults of the `Limit`s, in order.
        pub const LIMITS: &[(&str, usize)] = &[$(($name, $default),)*];
    };
}

limits! {
    /// `relate` in the rebuild without `clustered` only on regions of at most this many
    /// leaves; wider ones take seconds there.
    UnclusteredRelateLeaves "unclustered_relate_leaves" = 10;
    /// Most `rewrite` calls the rebuild without `clustered` makes; past them it is dropped.
    UnclusteredRewrites "unclustered_rewrites" = 256;
    /// Most `rewrite` calls of the other rebuilds after which the one without `clustered`
    /// is still tried: inputs that need more are slow to rebuild without it.
    UnclusteredAfter "unclustered_after" = 1024;
    /// Most `rewrite` calls the rebuild of the input with unified operands makes; past them
    /// it is dropped.
    UnifiedRewrites "unified_rewrites" = 128;
    /// Most combinations `related_leaves` rebuilds.
    RelatedRebuilds "related_rebuilds" = 8;
    /// Most arithmetic leaves `relate_region` tries.
    Related "related" = 4;
    /// Most leaf splits `bit_split` rebuilds per region.
    BitSplits "bit_splits" = 4;
    /// Most `P op Q` pairs `bit_split` rebuilds per pre-pass candidate: `Pipe::Cand` sets
    /// the budget `bit_split_budget` to it.
    CandBitSplits "cand_bit_splits" = 8;
    /// Most variable bits `split_bits` tries on one term.
    Splits "splits" = 4;
    /// How deep `split_bits` nests.
    SplitDepth "split_depth" = 2;
    /// Most rebuilds one `split_bits` call runs.
    SplitRuns "split_runs" = 16;
    /// Largest first rebuild `split_bits` runs on.
    SplitSize "split_size" = 64;
    /// Most leaves `small_blocks` handles.
    BlockLeaves "block_leaves" = 12;
    /// Most combinations of block choices `small_blocks` tries exhaustively, and steps of
    /// the `wide_blocks` search.
    BlockCombos "block_combos" = 1 << 15;
    /// Most `clustered` calls nested inside each other.
    ClusterDepth "cluster_depth" = 2;
    /// Most products `poly_mba` builds with every choice before it keeps to the first.
    PolyBuilds "poly_builds" = 512;
    /// Expansions with more monomials than this keep to the first choice at each level
    /// from the start, as after `poly_builds` products.
    PolyBranchMonos "poly_branch_monos" = 128;
    /// Uncached `rewrite` calls one `polish` call may make.
    PolishRewrites "polish_rewrites" = 2000;
}

/// Variables besides the limits: `rewrites` (uncached `rewrite` calls left), `semi_leaves`
/// (most leaves of a semi-linear region rebuilt), `relate_leaves` (most leaves of a region
/// `relate` tries), `bit_split_budget` (`bit_split` pairs left).
pub const SETTINGS: [&str; 4] = ["rewrites", "semi_leaves", "relate_leaves", "bit_split_budget"];

/// Settings of a run, `none` until its entry assignments (`Passes::entry_steps`) set them:
/// `keep` (pre-pass rebuilds unioned into a round, read as at least 1), `extra` (rounds added
/// while the pre-pass still changes the extraction), `printed` (rounds of the run from the
/// printed result), `match_limit` and `ban_length` (the back-off scheduler of the next egglog
/// round), `restarts` (`-m`) and `iter_limit` (`-i`, schedule repetitions of an egglog round).
pub const RUN: [&str; 7] = ["keep", "extra", "printed", "match_limit", "ban_length", "restarts", "iter_limit"];

/// How a binding of a variable combines with the outer ones.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarKind {
    /// An `INNER` pass: 1 on, 0 off.
    Pass,
    /// A `FLAGS` switch: 1 on, 0 off.
    Flag,
    /// An entry of `LIMITS`.
    Limit,
    /// `semi_leaves`, `relate_leaves` and the `RUN` settings.
    Setting,
    /// `rewrites`, `bit_split_budget`: a binding is at most what the outer one has left, and
    /// what is used inside is used up outside too.
    Budget,
    /// `time_limit`, a deadline in ns of `epoch_ns`: a binding is never later than the outer
    /// one.
    Deadline,
}

/// A variable of the runs on this thread, by its position in `VARS`: an `INNER` pass, a
/// `FLAGS` switch, a `LIMITS` entry, a `SETTINGS` entry, a `RUN` setting or the deadline.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Var {
    pub name: &'static str,
    pub kind: VarKind,
}

const FLAG0: usize = INNER.len();
const LIMIT0: usize = FLAG0 + FLAGS.len();
const SETTING0: usize = LIMIT0 + LIMITS.len();
pub const REWRITES: usize = SETTING0;
pub const SEMI_LEAVES: usize = SETTING0 + 1;
pub const RELATE_LEAVES: usize = SETTING0 + 2;
pub const BIT_SPLIT_BUDGET: usize = SETTING0 + 3;
const RUN0: usize = SETTING0 + SETTINGS.len();
pub const CUT: usize = FLAG0;
pub const RERUN_INPUT: usize = FLAG0 + 1;
pub const PROVE_MINIMAL: usize = FLAG0 + 2;
pub const KEEP: usize = RUN0;
pub const MATCH_LIMIT: usize = RUN0 + 3;
pub const BAN_LENGTH: usize = RUN0 + 4;
pub const RESTARTS: usize = RUN0 + 5;
pub const ITER_LIMIT: usize = RUN0 + 6;
pub const DEADLINE: usize = RUN0 + RUN.len();
pub const NVARS: usize = DEADLINE + 1;
const _: () = assert!(NVARS <= 128, "the read variables are a u128");

/// No limit: the value of an unbound budget or deadline.
pub const NONE: u64 = u64::MAX;

/// The variable at position `i` of `VARS`.
pub const fn var(i: usize) -> Var {
    match i {
        _ if i < FLAG0 => Var { name: INNER[i], kind: VarKind::Pass },
        _ if i < LIMIT0 => Var { name: FLAGS[i - FLAG0], kind: VarKind::Flag },
        _ if i < SETTING0 => Var { name: LIMITS[i - LIMIT0].0, kind: VarKind::Limit },
        _ if i == SEMI_LEAVES || i == RELATE_LEAVES => Var { name: SETTINGS[i - SETTING0], kind: VarKind::Setting },
        _ if i < RUN0 => Var { name: SETTINGS[i - SETTING0], kind: VarKind::Budget },
        _ if i < DEADLINE => Var { name: RUN[i - RUN0], kind: VarKind::Setting },
        _ => Var { name: "time_limit", kind: VarKind::Deadline },
    }
}

/// The position in `VARS` of the variable `name`.
pub fn var_index(name: &str) -> Option<usize> {
    (0..NVARS).find(|i| var(*i).name == name)
}

/// Whether the variable at `i` is a switch: an `INNER` pass or a `FLAGS` switch.
pub fn is_switch(i: usize) -> bool {
    matches!(var(i).kind, VarKind::Pass | VarKind::Flag)
}

const DEFAULTS: [u64; NVARS] = {
    let mut a = [0u64; NVARS];
    let mut i = 0;
    while i < NVARS {
        a[i] = match var(i).kind {
            VarKind::Pass => 1,
            VarKind::Flag if i == CUT => 0,
            VarKind::Limit => LIMITS[i - LIMIT0].1 as u64,
            VarKind::Setting if i == SEMI_LEAVES => crate::linear_mba::MAX_LEAVES as u64,
            VarKind::Setting if i == RELATE_LEAVES => crate::linear_mba::MAX_WIDE_LEAVES as u64,
            _ => NONE,
        };
        i += 1;
    }
    a
};

const fn initial_vars() -> [std::cell::Cell<u64>; NVARS] {
    let mut a = [const { std::cell::Cell::new(0) }; NVARS];
    let mut i = 0;
    while i < NVARS {
        a[i] = std::cell::Cell::new(DEFAULTS[i]);
        i += 1;
    }
    a
}

thread_local! {
    /// The current value of each variable. Shallow binding: `bind` keeps the outer value in
    /// the innermost scope of `FRAMES`, which puts it back when it ends.
    static VARS: [std::cell::Cell<u64>; NVARS] = const { initial_vars() };
    /// The scopes under way, innermost last: each variable bound there, its value outside and
    /// the value bound.
    static FRAMES: std::cell::RefCell<Vec<Vec<(usize, u64, u64)>>> = const { std::cell::RefCell::new(Vec::new()) };
    /// Bits of the variables read since the last `swap_read`.
    static READ: std::cell::Cell<u128> = const { std::cell::Cell::new(0) };
    /// The passes of the run on this thread (`set_current`), the default ones until set.
    static CURRENT: std::cell::RefCell<Option<std::rc::Rc<Passes>>> = const { std::cell::RefCell::new(None) };
}

/// The passes `set_current` last set on this thread.
pub fn current() -> std::rc::Rc<Passes> {
    CURRENT.with(|c| c.borrow_mut().get_or_insert_with(|| std::rc::Rc::new(Passes::default())).clone())
}

/// Makes `p` the passes of the runs on this thread that follow (`current`).
pub fn set_current(p: &Passes) {
    CURRENT.with(|c| {
        let mut c = c.borrow_mut();
        if c.as_deref() != Some(p) {
            *c = Some(std::rc::Rc::new(p.clone()));
        }
    });
}

/// The value of variable `i`, not recorded as read.
pub fn get(i: usize) -> u64 {
    VARS.with(|v| v[i].get())
}

/// The value of variable `i`, recorded as read for the memos (`swap_read`).
pub fn read(i: usize) -> u64 {
    READ.with(|r| r.set(r.get() | 1 << i));
    get(i)
}

/// Sets variable `i` outside any binding: a scope that binds it later restores this value.
pub fn set(i: usize, v: u64) {
    VARS.with(|a| a[i].set(v));
}

/// Binds variable `i` to `v` in the innermost scope (`in_scope`) until it ends; a budget is
/// at most what the outer binding has left, a deadline no later than the outer one.
pub fn bind(i: usize, v: u64) {
    let cur = get(i);
    let kind = var(i).kind;
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
        let back = match var(i).kind {
            VarKind::Budget => old.saturating_sub(bound.saturating_sub(get(i))),
            _ => old,
        };
        set(i, back);
    }
    r
}

/// The variables read since the last call, which sets them to `v`.
pub fn swap_read(v: u128) -> u128 {
    READ.with(|r| r.replace(v))
}

/// The values of the variables in `bits`, in order.
pub fn values(bits: u128) -> Vec<u64> {
    VARS.with(|a| ones(bits).map(|i| a[i].get()).collect())
}

/// Whether the variables in `bits` have the values `vals` (`values`).
pub fn same_values(bits: u128, vals: &[u64]) -> bool {
    VARS.with(|a| ones(bits).zip(vals).all(|(i, v)| a[i].get() == *v))
}

fn ones(mut bits: u128) -> impl Iterator<Item = usize> {
    std::iter::from_fn(move || {
        let i = bits.trailing_zeros() as usize;
        bits &= bits.wrapping_sub(1);
        (i < 128).then_some(i)
    })
}

/// The values of all variables but the budgets and the deadline, which a result depends on
/// only where they cut it short.
pub fn key() -> Vec<u64> {
    VARS.with(|a| (0..NVARS).filter(|i| !matches!(var(*i).kind, VarKind::Budget | VarKind::Deadline)).map(|i| a[i].get()).collect())
}

/// A hash of the limits on this thread.
pub fn limits_key() -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    VARS.with(|a| a[LIMIT0..SETTING0].iter().for_each(|c| c.get().hash(&mut h)));
    h.finish()
}

/// Nanoseconds since the first call in the process, the unit of `DEADLINE`.
pub fn epoch_ns() -> u64 {
    static EPOCH: std::sync::LazyLock<std::time::Instant> = std::sync::LazyLock::new(std::time::Instant::now);
    EPOCH.elapsed().as_nanos() as u64
}

/// The value of `l` on this thread.
pub fn limit(l: Limit) -> usize {
    read(LIMIT0 + l as usize) as usize
}

/// `f` with the `INNER` passes `names` turned off, as `((off NAMES) | f)` would run it.
pub fn with_off<R>(names: &[&str], f: impl FnOnce() -> R) -> R {
    in_scope(|| {
        names.iter().for_each(|n| turn_off(n));
        f()
    })
}

/// A pass pipeline: every pass maps a list of equivalent candidate terms (the first is the
/// main one) to another, so any pass can follow any other. Written in `crate::pipe_lang`
/// (`lowbits | rewrite | (fix 3 egglog)`).
#[derive(Clone, Debug, PartialEq)]
pub enum Pipe {
    /// A pass, its name resolved (`crate::pipe::resolve`).
    Pass(Pass),
    /// Each in turn on the candidates of the one before (`a | b`).
    Seq(Vec<Pipe>),
    /// All on the same candidates; their candidates in order, repeats dropped (`union`).
    Union(Vec<Pipe>),
    /// All on the same candidates; the `k` smallest of their candidates, the earlier of
    /// equal ones first (`best`).
    Best(Value, Vec<Pipe>),
    /// The candidates of the first that gives candidates other than its input's, else the
    /// input (`first`).
    First(Vec<Pipe>),
    /// Repeated at most `n` times while the main candidate changes (`fix`).
    Fix(Value, Box<Pipe>),
    /// `a` where the condition holds for the candidates, else `b` (`if`).
    If(Cond, Box<Pipe>, Box<Pipe>),
    /// `a`, and where the condition holds for its candidates, `b` on the same input taken
    /// instead when its main candidate is no larger (`retry`).
    Retry(Cond, Box<Pipe>, Box<Pipe>),
    /// The candidates of `p`, unless a pass inside gave a strictly smaller candidate than
    /// their main one: then the first smallest (`smallest`).
    Smallest(Box<Pipe>),
    /// `p` timed as `NAME/run`; a main candidate it changed is counted in `NAME/won/ORIGIN`
    /// and gets origin `NAME` (`tag`).
    Tag(String, Box<Pipe>),
    /// The candidates the condition holds for, each taken alone (`filter`).
    Filter(Cond),
    /// The pre-pass candidate `NAME`: `p` as a scope with `bit_split_budget = cand_bit_splits`
    /// first, timed as `pre/NAME/made`, its candidates with origin `NAME`; none when `NAME`
    /// is an entry of `PRE` turned off (`cand`).
    Cand(String, Box<Pipe>),
    /// `p` with its passes over one term sharing one run's memos (`scope`).
    Scope(Box<Pipe>),
    /// `p`, taken only when its main candidate is smaller than the input's; timed as
    /// `NAME/run`, counted in `NAME/won` and `NAME/gain` when taken, which gives the main
    /// candidate origin `NAME` (`smaller`).
    Smaller(String, Box<Pipe>),
    /// `p` repeated while the `smaller` inside take a result, until they have taken `n` (`wins`).
    Wins(Value, Box<Pipe>),
    /// Each candidate that is a linear region rebuilt by the first candidate of `p`, with the
    /// atom leaves of that form rewritten by `Passes::rewrite`; otherwise, or when `p` gives
    /// none, its operands rewritten (`regions`).
    Regions(Box<Pipe>),
    /// `p`, then `Passes::rewrite` again on its main candidate, kept when smaller, where it
    /// changed a term with an arithmetic leaf of a bitwise operation (`again`).
    Again(Box<Pipe>),
}

/// A pass of a `Pipe`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pass {
    /// A pass over the candidate list, by position in `crate::pipe::SET_PASSES`.
    Set(usize),
    /// An egglog round, by the name it is timed as (`egglog`, `egglog/LABEL`).
    Egglog(String),
    Save(String),
    Load(String),
    Label(String),
    /// Turns an `INNER` pass or `FLAGS` switch off until the end of the enclosing sequence,
    /// also in the runs it calls.
    Off(Vec<&'static str>),
    /// `Off` the other way.
    On(Vec<&'static str>),
    /// `NAME = VALUE`: binds the variable at this position of `VARS` in the enclosing scope
    /// to the value, evaluated on the candidates; `None` is `none` (no limit). A switch is on
    /// for any value but 0; `time_limit` takes milliseconds from now.
    Assign(usize, Option<Value>),
    /// A pass over one term; `alt` is the used bit of an alternative
    /// (`crate::linear_mba::ALTERNATIVES`).
    Term { name: String, at: TermAt, alt: Option<u8> },
}

/// Where a pass over one term is: `crate::linear_mba::TERM_PASSES` or `POLISH`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TermAt {
    Term(usize),
    Polish(usize),
}

impl Pass {
    /// The pass `id`.
    pub fn id() -> Pass {
        crate::pipe::resolve("id").unwrap()
    }

    /// The name it is written and counted as.
    pub fn name(&self) -> String {
        match self {
            Pass::Set(i) => crate::pipe::SET_PASSES[*i].to_string(),
            Pass::Egglog(n) | Pass::Term { name: n, .. } => n.clone(),
            Pass::Save(r) => format!("save/{r}"),
            Pass::Load(r) => format!("load/{r}"),
            Pass::Label(r) => format!("label/{r}"),
            Pass::Off(ns) => format!("off/{}", ns.join(" ")),
            Pass::On(ns) => format!("on/{}", ns.join(" ")),
            Pass::Assign(i, _) => var(*i).name.into(),
        }
    }
}

/// A number in a pipeline: a count of `fix`, `best` or `wins`, or a side of a comparison.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Num(u64),
    /// The main candidate's entry of `crate::pipe::FEATURES` (`size` is its node count).
    Feature(usize),
    /// The size of the main candidate of register `R` (`(size R)`).
    Size(String),
    /// A variable of `VARS`; `time_limit` reads as the milliseconds left, `keep` as at least 1.
    Var(usize),
    /// `+ - * /` of two values.
    Bin(char, Box<Value>, Box<Value>),
}

/// A comparison operator.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Cmp {
    pub const ALL: [(Cmp, &'static str); 6] = [(Cmp::Lt, "<"), (Cmp::Le, "<="), (Cmp::Gt, ">"), (Cmp::Ge, ">="), (Cmp::Eq, "=="), (Cmp::Ne, "!=")];

    pub fn symbol(self) -> &'static str {
        Cmp::ALL.iter().find(|(c, _)| *c == self).unwrap().1
    }

    pub fn holds(self, a: u64, b: u64) -> bool {
        match self {
            Cmp::Lt => a < b,
            Cmp::Le => a <= b,
            Cmp::Gt => a > b,
            Cmp::Ge => a >= b,
            Cmp::Eq => a == b,
            Cmp::Ne => a != b,
        }
    }
}

/// A condition on candidates. A name, `Same` and a comparison are false without a main
/// candidate, and a comparison also when a register it reads is empty.
#[derive(Clone, Debug, PartialEq)]
pub enum Cond {
    /// An entry of `crate::pipe::CONDS`.
    Is(usize),
    /// A variable of `VARS`, true when not 0 (`none` too).
    Var(usize),
    /// The main candidate is the term of register `R`'s (`(same R)`).
    Same(String),
    Not(Box<Cond>),
    And(Vec<Cond>),
    Or(Vec<Cond>),
    Cmp(Cmp, Value, Value),
    /// Some candidate alone satisfies it (`(any C)`).
    Any(Box<Cond>),
    /// There are candidates and each alone satisfies it (`(all C)`).
    All(Box<Cond>),
}

impl fmt::Display for Pipe {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", lang::show(self))
    }
}

/// The rebuilds of subterms that passes inside a rebuild make (`Passes::subs`), by name, and
/// their default pipelines: `rewrite` (the memoized `Passes::rewrite`) or `rebuild` (the
/// rebuild of `simplify_linear` without `relate`, `linear_mba::rebuild_once`).
pub const SUBS: [(&str, &str); 13] = [
    // Each group of a clustered region, and each term of a group that did not shrink.
    ("cluster", "rewrite"),
    // A region with arithmetic leaves related, the shrunk region whole, complemented leaves.
    ("relate", "rewrite"),
    // The sides of a `bit_split`.
    ("bit_split", "rewrite"),
    // The halved operands of `halve`.
    ("halve", "rewrite"),
    // A region with its unused leaves set to 0.
    ("drop_unused", "rewrite"),
    // The factors of recombined products and the region they changed.
    ("recombine", "rewrite"),
    // The joined groups of `join_constants` and `join_linear`.
    ("polish", "rewrite"),
    // A product factor with its constants cut below the other's trailing zeros.
    ("low_factor", "rewrite"),
    // The leaves `poly_mba` expands over and its factors with a constant bitwise operation.
    ("poly", "rewrite"),
    // The cases of `over_products`.
    ("over_products", "rebuild"),
    // The cases of `split_bits`.
    ("split_bits", "rebuild"),
    // The terms of `over_const_bitwise` and `over_shared_bitwise`.
    ("over_bitwise", "rebuild"),
    // The cases of `shift_cases`.
    ("shift_cases", "rebuild"),
];

/// The position of `name` in `SUBS`.
pub const fn sub_index(name: &str) -> usize {
    let mut i = 0;
    while i < SUBS.len() {
        let (a, b) = (SUBS[i].0.as_bytes(), name.as_bytes());
        if a.len() == b.len() {
            let mut j = 0;
            while j < a.len() && a[j] == b[j] {
                j += 1;
            }
            if j == a.len() {
                return i;
            }
        }
        i += 1;
    }
    panic!("not a SUBS name")
}

/// The polish `polish=a,b,...` writes: the polish passes `names` in turn, each kept when
/// smaller, repeated while one is, until 8 are, as the default in `default.pipe`.
pub fn polish(names: &[&str]) -> String {
    let step = |n: &&str| {
        let run = format!("polish/{n} | drop_identities");
        let run = if *n == "join_linear" { format!("(semi_leaves = 2 | {run})") } else { run };
        format!("(smaller polish/{n} {run})")
    };
    let steps: Vec<String> = names.iter().map(step).collect();
    let steps = if steps.len() == 1 { format!("(seq {})", steps[0]) } else { steps.join("\n  | ") };
    format!("(scope rewrites = polish_rewrites\n  | (wins 8\n  {steps}))")
}

fn switch_index(name: &str) -> Option<usize> {
    INNER.iter().chain(&FLAGS).position(|k| *k == name)
}

/// Turns off the `INNER` pass or `FLAGS` switch `name` until the end of the scope under way
/// (`in_scope`: the enclosing sequence or pipeline run), also in the runs it starts (the
/// pass `(off NAME)`).
pub fn turn_off(name: &str) {
    if let Some(i) = switch_index(name) {
        bind(i, 0);
    }
}

/// `turn_off` the other way (the pass `(on NAME)`): the later of the two in a scope counts.
pub fn turn_on(name: &str) {
    if let Some(i) = switch_index(name) {
        bind(i, 1);
    }
}

/// Whether the `FLAGS` switch `name` is on on this thread.
pub fn is_on(name: &str) -> bool {
    FLAGS.iter().position(|k| *k == name).is_some_and(|i| read(FLAG0 + i) != 0)
}

/// Whether the pass `name` is turned off on this thread.
pub fn is_off(name: &str) -> bool {
    INNER.iter().position(|k| *k == name).is_some_and(is_off_at)
}

/// The position of `name` in `INNER`, for `is_off_at`.
pub const fn inner_index(name: &str) -> usize {
    let mut i = 0;
    while i < INNER.len() {
        let (a, b) = (INNER[i].as_bytes(), name.as_bytes());
        if a.len() == b.len() {
            let mut j = 0;
            while j < a.len() && a[j] == b[j] {
                j += 1;
            }
            if j == a.len() {
                return i;
            }
        }
        i += 1;
    }
    panic!("not an INNER pass")
}

/// `is_off` of the `INNER` pass at position `i`.
pub fn is_off_at(i: usize) -> bool {
    read(i) == 0
}

/// The rulesets of `make_egg`.
pub const RULESETS: [&str; 6] = ["default-ruleset", "canonicalization", "constant-folding", "analysis", "identity-zero-element", "simplify"];

/// How one step of a round's egglog schedule runs its ruleset.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Step {
    /// Once, with the back-off scheduler (`run:` in a spec).
    Run,
    /// Once, matching everything (`once:`).
    Once,
    /// Until nothing changes (`sat:`).
    Saturate,
}

const STEPS: [(Step, &str); 3] = [(Step::Run, "run"), (Step::Once, "once"), (Step::Saturate, "sat")];

#[derive(Clone, Debug, PartialEq)]
pub struct Passes {
    /// The steps each of a round's `iter_limit` repetitions runs, in order.
    pub schedule: Vec<(Step, &'static str)>,
    /// Enabled entries of `PRE`.
    pub pre: Vec<&'static str>,
    /// The assignments (`Pass::Assign`, `Pass::On`, `Pass::Off`) a run starts with, in order:
    /// the first `defaults` from `default.pipe`, the rest from `--passes` (`entry_steps`).
    pub entry: Vec<Pass>,
    pub defaults: usize,
    /// The passes `simplify` runs on its input.
    pub pipeline: Pipe,
    /// The pre-pass on one term: its first candidate is the main rebuild, the others are
    /// unioned with it.
    pub prepass: Pipe,
    /// The final polish, on each candidate alone; a candidate is replaced by its first result
    /// when smaller.
    pub polish: Pipe,
    /// The rebuild of one term, memoized by `linear_mba::rewrite` and used by the
    /// passes inside it for subterms.
    pub rewrite: Pipe,
    /// The rebuild of one linear region, the `simba` pass.
    pub simba: Pipe,
    /// The rebuilds of subterms, in the order of `SUBS`.
    pub subs: Vec<Pipe>,
}

/// The default passes, and the names `default.pipe` defines for `--passes` to use.
static DEFAULT: std::sync::LazyLock<(Passes, lang::Defs)> = std::sync::LazyLock::new(|| {
    let mut p = Passes::base();
    let mut defs = lang::Defs::new();
    p.apply(include_str!("default.pipe"), &mut defs, &mut Lets::default()).and_then(|()| p.finish()).unwrap_or_else(|e| panic!("src/default.pipe: {e}"));
    p.defaults = p.entry.len();
    (p, defs)
});

impl Default for Passes {
    fn default() -> Passes {
        DEFAULT.0.clone()
    }
}

impl Passes {
    /// The settings `default.pipe` starts from; its pipelines are `id`.
    fn base() -> Passes {
        use Step::*;
        let id = Pipe::Pass(Pass::id());
        Passes {
            schedule: vec![
                (Run, "default-ruleset"),
                (Run, "canonicalization"),
                (Saturate, "constant-folding"),
                (Saturate, "analysis"),
                (Saturate, "identity-zero-element"),
                (Run, "simplify"),
            ],
            pre: PRE.to_vec(),
            entry: Vec::new(),
            defaults: 0,
            pipeline: id.clone(),
            prepass: id.clone(),
            polish: id.clone(),
            rewrite: id.clone(),
            simba: id,
            subs: SUBS.iter().map(|(_, d)| Pipe::Pass(crate::pipe::resolve(d).unwrap())).collect(),
        }
    }

    /// Whether the pre-pass candidate `name` (an entry of `PRE`) is built.
    pub fn pre_on(&self, name: &str) -> bool {
        debug_assert!(PRE.contains(&name), "unknown pre-pass candidate {name}");
        self.pre.contains(&name)
    }

    /// The assignments a run starts with: those of `default.pipe`, then `restarts = m` and
    /// `iter_limit = i` of the command line (`cli`), then those of `--passes`.
    pub fn entry_steps(&self, cli: Option<(usize, usize)>) -> Vec<Pass> {
        let (base, spec) = self.entry.split_at(self.defaults);
        let num = |i: usize, n: usize| Pass::Assign(i, Some(Value::Num(n as u64)));
        let cli = cli.map(|(m, i)| [num(RESTARTS, m), num(ITER_LIMIT, i)]);
        base.iter().cloned().chain(cli.into_iter().flatten()).chain(spec.iter().cloned()).collect()
    }

    /// `{:#}` after a comment line with the run it describes: `entry_steps` for `-m m -i i`,
    /// then `pipeline` (`--show-passes`).
    pub fn show_run(&self, m: usize, i: usize) -> String {
        let steps: Vec<String> = self.entry_steps(Some((m, i))).into_iter().map(|p| lang::show(&Pipe::Pass(p))).collect();
        format!("# A run: {} | pipeline
{self:#}", steps.join(" | "))
    }

    /// The `run-schedule` command of an egglog round: `iter_limit` repetitions, the back-off
    /// scheduler with `match_limit` and `ban_length`.
    pub fn egglog_schedule(&self) -> String {
        let iter = get(ITER_LIMIT);
        let steps: String = self
            .schedule
            .iter()
            .map(|(step, rs)| match step {
                Step::Run => format!("\n            (run-with babibo {rs})"),
                Step::Once => format!("\n            (run {rs})"),
                Step::Saturate => format!("\n            (saturate (run {rs}))"),
            })
            .collect();
        format!(
            "(run-schedule\n    (let-scheduler babibo (back-off :match-limit {} :ban-length {}))\n    (repeat {iter}\n        (seq{steps}\n        )\n    )\n)",
            get(MATCH_LIMIT),
            get(BAN_LENGTH)
        )
    }

    /// The default pipeline changed by `spec`: items `key=value`, and for the lists `pre`,
    /// `off` and `schedule` also `key+=names` and `key-=names` (names separated by `,`;
    /// schedule steps written `run:`, `once:` or `sat:` and a ruleset). `pipeline`,
    /// `prepass`, `polish`, `rewrite`, `simba` and `sub/NAME` (`SUBS`) take a pipeline
    /// (`crate::pipe_lang`), and `polish` also a list of polish pass names, run as
    /// `polish(names)`. Any other key is a variable: the item is an entry assignment
    /// (`entry`), as are the `off` items.
    /// `(let NAME p)` defines a name for the items after it (those of `default.pipe` come
    /// first), and `file=PATH` reads the items of a file there. Items are separated by `;`,
    /// or by white space before a `key=` or `(let` outside parentheses that does not follow
    /// a `|` (so `prepass=a | split_runs=4 | b` is one item); `#` starts a comment to the end
    /// of the line.
    pub fn parse(spec: &str) -> Result<Passes, String> {
        Passes::parse_noting(spec).map(|(p, _)| p)
    }

    /// `parse`, and warnings about parts of `spec` that do nothing: a `let` it defines and
    /// never uses, and what `Passes::warnings` finds.
    pub fn parse_noting(spec: &str) -> Result<(Passes, Vec<String>), String> {
        let (mut p, mut defs) = DEFAULT.clone();
        let mut lets = Lets::default();
        p.apply(spec, &mut defs, &mut lets)?;
        p.finish()?;
        let mut notes: Vec<String> = lets.defined.iter().filter(|n| !lets.used.contains(n)).map(|n| format!("(let {n} ...) is never used: a name is expanded only where a later item writes it")).collect();
        notes.extend(p.warnings());
        notes.dedup();
        Ok((p, notes))
    }

    /// The items of `spec` applied in turn.
    fn apply(&mut self, spec: &str, defs: &mut lang::Defs, lets: &mut Lets) -> Result<(), String> {
        let p = self;
        let read = |val: &str, defs: &lang::Defs, used: &mut Vec<String>| {
            lang::parse_with(val, defs, used).map_err(|e| match lang::is_old_syntax(val) {
                true => format!("{e} (the old seq(a,b) syntax is no longer read: write a | b, (best 1 a b), (if c a))"),
                false => e,
            })
        };
        let spec: String = spec.lines().map(|l| l.split_once('#').map_or(l, |(a, _)| a)).collect::<Vec<_>>().join("\n");
        let mut items: Vec<String> = Vec::new();
        let (mut depth, mut cur, mut fresh, mut after_bar) = (0i32, String::new(), true, false);
        let mut chunks = Vec::new();
        for c in spec.chars() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            if depth == 0 && (c.is_whitespace() || c == ';') {
                chunks.push((std::mem::take(&mut cur), c == ';'));
            } else {
                cur.push(c);
            }
        }
        chunks.push((cur, false));
        for (chunk, ends) in chunks {
            if !chunk.is_empty() {
                let key: String = chunk.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '/').collect();
                let def = chunk.starts_with("(let");
                let starts = def || !key.is_empty() && ["=", "+=", "-="].iter().any(|op| chunk[key.len()..].starts_with(op));
                let bar = chunk.ends_with('|');
                match items.last_mut() {
                    Some(last) if !fresh && (!starts || after_bar) => *last = format!("{last} {chunk}"),
                    _ => items.push(chunk),
                }
                fresh = def;
                after_bar = bar;
            }
            fresh |= ends;
            after_bar &= !ends;
        }
        for item in items.iter().map(String::as_str) {
            if item.starts_with("(let") {
                let (name, pipe) = lang::parse_let(item, defs, &mut lets.used)?;
                lets.defined.push(name.clone());
                defs.insert(name, pipe);
                continue;
            }
            if let Some(path) = item.strip_prefix("file=") {
                let text = std::fs::read_to_string(path).map_err(|e| format!("file={path}: {e}"))?;
                p.apply(&text, defs, lets).map_err(|e| format!("{path}: {e}"))?;
                continue;
            }
            if let Some(val) = item.strip_prefix("prepass=") {
                p.prepass = read(val, defs, &mut lets.used)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("pipeline=") {
                p.pipeline = read(val, defs, &mut lets.used)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("rewrite=") {
                p.rewrite = read(val, defs, &mut lets.used)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("simba=") {
                p.simba = read(val, defs, &mut lets.used)?;
                continue;
            }
            if let Some((name, val)) = item.strip_prefix("sub/").and_then(|s| s.split_once('=')) {
                let names: Vec<&str> = SUBS.iter().map(|(n, _)| *n).collect();
                let i = names.iter().position(|n| *n == name).ok_or_else(|| format!("unknown sub/{name}; known: {}", names.join(" ")))?;
                p.subs[i] = read(val, defs, &mut lets.used)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("polish=") {
                let names: Vec<&str> = val.split(',').filter(|s| !s.is_empty()).collect();
                let all_polish = names.iter().all(|n| crate::linear_mba::POLISH.iter().any(|(m, _)| m == n));
                p.polish = if all_polish { lang::parse(&polish(&names))? } else { read(val, defs, &mut lets.used)? };
                continue;
            }
            let (key, op, val) = ["+=", "-=", "="]
                .iter()
                .find_map(|op| item.split_once(op).map(|(k, v)| (k, *op, v)))
                .ok_or_else(|| format!("expected key=value: {item}"))?;
            let names = |known: &[&'static str]| -> Result<Vec<&'static str>, String> {
                val.split(',').filter(|s| !s.is_empty()).map(|n| known.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown {key} name {n}; known: {}", known.join(",")))).collect()
            };
            if key == "pre" {
                let ns = names(&PRE)?;
                match op {
                    "=" => p.pre = ns,
                    "+=" => p.pre.extend(ns),
                    _ => p.pre.retain(|n| !ns.contains(n)),
                }
                continue;
            }
            // `off=a,b` turns every `INNER` pass on and then `a`, `b` off.
            if key == "off" {
                let ns = names(&INNER)?;
                if op == "=" {
                    p.entry.push(Pass::On(INNER.to_vec()));
                }
                if !ns.is_empty() {
                    p.entry.push(if op == "-=" { Pass::On(ns) } else { Pass::Off(ns) });
                }
                continue;
            }
            if key == "schedule" {
                let steps = val
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        let (kind, rs) = s.split_once(':').ok_or_else(|| format!("expected run:, once: or sat: and a ruleset: {s}"))?;
                        let step = STEPS.iter().find(|(_, k)| *k == kind).ok_or_else(|| format!("unknown step kind {kind}; known: run once sat"))?.0;
                        let rs = RULESETS.iter().find(|r| **r == rs).ok_or_else(|| format!("unknown ruleset {rs}; known: {}", RULESETS.join(",")))?;
                        Ok((step, *rs))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                match op {
                    "=" => p.schedule = steps,
                    "+=" => p.schedule.extend(steps),
                    _ => p.schedule.retain(|s| !steps.contains(s)),
                }
                continue;
            }
            if op != "=" {
                return Err(format!("{key} is not a list: {item}"));
            }
            p.entry.push(lang::parse_assign(key, val).map_err(|e| format!("{item}: {e}"))?);
        }
        Ok(())
    }

    /// The lists in their canonical order, then `check`.
    fn finish(&mut self) -> Result<(), String> {
        self.pre.sort_by_key(|n| PRE.iter().position(|k| k == n));
        self.pre.dedup();
        self.check()
    }

    /// Rejects pipelines that cannot run: an egglog round or `reprint` outside `pipeline`
    /// (only a `simplify` run has them), and `prepass` or `polish` that reach themselves.
    fn check(&self) -> Result<(), String> {
        // The pipelines each reaches: `prepass`, `polish`, or the rebuilds of one term
        // (`inner`), which any pass over one term may run.
        let mut reach = std::collections::HashMap::new();
        for (name, uses) in self.uses() {
            if let Some(r) = uses.unsaved {
                return Err(format!("{name} reads register {r} before any (save {r})"));
            }
            if name != "pipeline" {
                if let Some(what) = uses.needs_run.first() {
                    return Err(format!("{what} needs a simplify run and cannot be in {name}"));
                }
            }
            let node = if ["pipeline", "prepass", "polish"].contains(&name) { name } else { "inner" };
            let e: &mut Vec<&str> = reach.entry(node).or_default();
            e.extend(uses.calls);
        }
        for start in ["prepass", "polish"] {
            let (mut seen, mut todo) = (Vec::new(), reach.get(start).cloned().unwrap_or_default());
            while let Some(n) = todo.pop() {
                if n == start {
                    return Err(format!("{start} reaches itself"));
                }
                if !seen.contains(&n) {
                    seen.push(n);
                    todo.extend(reach.get(n).cloned().unwrap_or_default());
                }
            }
        }
        Ok(())
    }

    /// Parts of the pipelines that do nothing: a `(save R)` never read in its pipeline or
    /// saved over before any read on every path, an assignment (also `(on NAME)`, `(off
    /// NAME)`) that ends its sequence, and one assigned again in its sequence before any
    /// read of it or any other step.
    pub fn warnings(&self) -> Vec<String> {
        let mut out = Vec::new();
        for (name, uses) in self.uses() {
            let mut unread: Vec<&String> = uses.saved.iter().filter(|r| !uses.reads.contains(r)).collect();
            unread.dedup();
            out.extend(unread.into_iter().map(|r| format!("{name}: register {r} is saved and never read")));
            let mut dead = uses.dead.clone();
            dead.dedup();
            out.extend(dead.iter().map(|r| format!("{name}: register {r} is saved again before the earlier save is read")));
            out.extend(uses.idle_assign.iter().map(|t| format!("{name}: {t} ends its sequence and changes nothing")));
            out.extend(uses.reassigned.iter().map(|v| format!("{name}: {v} is assigned again before anything reads it")));
        }
        out
    }

    /// Each pipeline by name, with what it uses.
    fn uses(&self) -> Vec<(&'static str, Uses)> {
        let main = [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)];
        main.into_iter()
            .chain(SUBS.iter().map(|(n, _)| *n).zip(&self.subs))
            .map(|(name, p)| {
                let mut uses = Uses::default();
                uses.walk(p);
                if let Pipe::Pass(a @ (Pass::Assign(..) | Pass::On(_) | Pass::Off(_))) = p {
                    uses.idle_assign.push(lang::show(&Pipe::Pass(a.clone())));
                }
                (name, uses)
            })
            .collect()
    }
}

/// The `let` names a spec defines and those its items expand, for `Passes::parse_noting`.
#[derive(Default)]
struct Lets {
    defined: Vec<String>,
    used: Vec<String>,
}

/// What a pipeline uses, for `Passes::check` and `Passes::warnings`.
#[derive(Default)]
struct Uses {
    /// The passes in it that need a `simplify` run.
    needs_run: Vec<String>,
    /// The pipelines it runs: `prepass`, `polish`, `inner`.
    calls: Vec<&'static str>,
    /// The registers a `(save R)` may have set by now, in run order; each pipeline has its own.
    saved: Vec<String>,
    /// The first register read where no `(save R)` can have run before.
    unsaved: Option<String>,
    /// Every register read, also by `pre_done` (`t0`, which it may find empty).
    reads: Vec<String>,
    /// The assignments that end their sequence, so change nothing.
    idle_assign: Vec<String>,
    /// The variables assigned twice in a sequence with no read or other step between.
    reassigned: Vec<String>,
    /// The registers saved and not read since on every path that reaches this point, from
    /// saves at the same level of `if`s and other parts that may not run.
    pending: Vec<String>,
    /// The registers saved again where they are `pending`: the earlier save is never read.
    dead: Vec<String>,
}

impl Uses {
    fn walk(&mut self, p: &Pipe) {
        match p {
            Pipe::Pass(Pass::Egglog(n)) => self.needs_run.push(n.clone()),
            Pipe::Pass(Pass::Set(i)) => match crate::pipe::SET_PASSES[*i] {
                "reprint" => self.needs_run.push("reprint".into()),
                "prepass" => self.calls.push("prepass"),
                "polish" => self.calls.push("polish"),
                "pre_done" => self.seen("t0"),
                _ => {}
            },
            Pipe::Pass(Pass::Term { .. }) => self.calls.push("inner"),
            Pipe::Pass(Pass::Save(r)) => {
                self.saved.push(r.clone());
                if self.pending.contains(r) {
                    self.dead.push(r.clone());
                } else {
                    self.pending.push(r.clone());
                }
            }
            Pipe::Pass(Pass::Load(r) | Pass::Label(r)) => self.read(r),
            Pipe::Pass(Pass::Assign(_, v)) => {
                if let Some(v) = v {
                    self.value(v);
                }
            }
            Pipe::Pass(_) => {}
            Pipe::Seq(ps) => {
                let mut pending: Vec<usize> = Vec::new();
                for p in ps {
                    match p {
                        Pipe::Pass(Pass::Assign(i, v)) => {
                            if v.as_ref().is_some_and(|v| reads_var(v, *i)) {
                                pending.retain(|j| j != i);
                            }
                            self.assigned(&mut pending, *i);
                        }
                        Pipe::Pass(Pass::On(ns) | Pass::Off(ns)) => ns.iter().filter_map(|n| var_index(n)).for_each(|i| self.assigned(&mut pending, i)),
                        _ => pending.clear(),
                    }
                }
                ps.iter().for_each(|p| self.walk(p));
                if let Some(Pipe::Pass(a @ (Pass::Assign(..) | Pass::On(_) | Pass::Off(_)))) = ps.last() {
                    self.idle_assign.push(lang::show(&Pipe::Pass(a.clone())));
                }
            }
            Pipe::Union(ps) => ps.iter().for_each(|p| self.walk(p)),
            Pipe::First(ps) => {
                self.walk(&ps[0]);
                ps[1..].iter().for_each(|p| self.maybe(p));
            }
            Pipe::Best(v, ps) => {
                ps.iter().for_each(|p| self.walk(p));
                self.value(v);
            }
            Pipe::Fix(v, p) | Pipe::Wins(v, p) => {
                self.value(v);
                self.repeated(p);
            }
            Pipe::If(c, a, b) => {
                self.cond(c);
                let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
                self.walk(a);
                let after_a = std::mem::take(&mut self.pending);
                self.walk(b);
                let both: Vec<String> = self.pending.drain(..).filter(|r| after_a.contains(r)).collect();
                self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
                for r in both {
                    if !self.pending.contains(&r) {
                        self.pending.push(r);
                    }
                }
            }
            Pipe::Retry(c, a, b) => {
                self.walk(a);
                self.cond(c);
                self.maybe(b);
            }
            Pipe::Cand(_, p) => self.maybe(p),
            Pipe::Filter(c) => self.cond(c),
            Pipe::Smallest(p) | Pipe::Scope(p) | Pipe::Tag(_, p) | Pipe::Smaller(_, p) => self.walk(p),
            // Both rebuild with `Passes::rewrite`.
            Pipe::Regions(p) => {
                self.calls.push("inner");
                self.repeated(p);
            }
            Pipe::Again(p) => {
                self.calls.push("inner");
                self.walk(p);
            }
        }
    }

    fn assigned(&mut self, pending: &mut Vec<usize>, i: usize) {
        if pending.contains(&i) {
            self.reassigned.push(var(i).name.to_string());
        } else {
            pending.push(i);
        }
    }

    /// `p` run more than once: a read can see a save of an earlier run.
    fn repeated(&mut self, p: &Pipe) {
        let mut body = Uses::default();
        body.walk(p);
        self.saved.extend(body.saved);
        self.maybe(p);
    }

    /// `p` run or not. A save in `p` does not make an earlier one dead (`(save t) | (if c
    /// (save t))` keeps a default), and only what is pending either way stays pending.
    fn maybe(&mut self, p: &Pipe) {
        let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
        self.walk(p);
        self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
    }

    fn seen(&mut self, r: &str) {
        self.reads.push(r.to_string());
        self.pending.retain(|s| s != r);
    }

    fn read(&mut self, r: &str) {
        self.seen(r);
        if self.unsaved.is_none() && !self.saved.iter().any(|s| s == r) {
            self.unsaved = Some(r.to_string());
        }
    }

    fn cond(&mut self, c: &Cond) {
        match c {
            Cond::Is(i) if ["opaque", "rebuilds"].contains(&crate::pipe::CONDS[*i]) => self.calls.push("prepass"),
            Cond::Is(_) | Cond::Var(_) => {}
            Cond::Same(r) => self.read(r),
            Cond::Not(c) | Cond::Any(c) | Cond::All(c) => self.cond(c),
            Cond::And(cs) | Cond::Or(cs) => cs.iter().for_each(|c| self.cond(c)),
            Cond::Cmp(_, a, b) => {
                self.value(a);
                self.value(b);
            }
        }
    }

    fn value(&mut self, v: &Value) {
        match v {
            Value::Size(r) => self.read(r),
            Value::Bin(_, a, b) => {
                self.value(a);
                self.value(b);
            }
            _ => {}
        }
    }
}

/// Whether `v` reads the variable at `i`.
fn reads_var(v: &Value, i: usize) -> bool {
    match v {
        Value::Var(j) => *j == i,
        Value::Bin(_, a, b) => reads_var(a, i) || reads_var(b, i),
        _ => false,
    }
}

/// The spec `Passes::parse` reads back to these passes; `{:#}` puts each pipeline on its own
/// lines.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(f, "schedule={} pre={}", steps.join(","), self.pre.join(","))?;
        let spec = &self.entry[self.defaults..];
        let mut i = 0;
        while i < spec.len() {
            let names = |ns: &[&str]| ns.join(",");
            match &spec[i] {
                Pass::On(ns) if *ns == INNER => match spec.get(i + 1) {
                    Some(Pass::Off(off)) if off.iter().all(|n| INNER.contains(n)) => {
                        write!(f, " off={}", names(off))?;
                        i += 1;
                    }
                    _ => write!(f, " off=")?,
                },
                Pass::Off(ns) => write!(f, " off+={}", names(ns))?,
                Pass::On(ns) => write!(f, " off-={}", names(ns))?,
                Pass::Assign(v, val) => write!(f, " {}={}", var(*v).name, lang::show_assigned(val))?,
                p => unreachable!("entry step {p:?}"),
            }
            i += 1;
        }
        let show = if f.alternate() { lang::pretty } else { lang::show };
        let sep = if f.alternate() { "\n" } else { " " };
        for (name, p) in [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)] {
            write!(f, "{sep}{name}={}", show(p))?;
        }
        for ((name, default), p) in SUBS.iter().zip(&self.subs) {
            if *p != Pipe::Pass(crate::pipe::resolve(default).unwrap()) {
                write!(f, "{sep}sub/{name}={}", show(p))?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> crate::pipe::Cand {
        crate::pipe::Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input")
    }

    /// The value of variable `name` after the entry assignments of `p`.
    fn after_entry(p: &Passes, name: &str) -> u64 {
        crate::pipe::in_run(p, None, x, || get(var_index(name).unwrap()))
    }

    #[test]
    fn off_ends_with_its_scope() {
        let p = Passes::parse("off+=relate").unwrap();
        crate::pipe::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("semi/peel_shapes"), "the entry assignments run first");
            in_scope(|| {
                turn_on("relate");
                crate::pipe::in_run(&p, None, x, || assert!(!is_off("relate"), "a run inside a run keeps the bindings of its caller"));
                turn_off("tfunc");
            });
            assert!(!is_off("tfunc") && is_off("relate"), "a pass turned off in a scope is on again after it");
        });
        assert!(!is_off("relate") && !is_off("semi/peel_shapes"), "the entry bindings end with the run");
    }

    #[test]
    fn entry_assignments() {
        let p = Passes::parse("extra=5 split_runs=vars*3 extra=extra+1 off=relate,tfunc off+=simba off-=tfunc").unwrap();
        assert_eq!(after_entry(&p, "extra"), 6, "items run in order, a later one reading an earlier");
        assert_eq!(after_entry(&p, "split_runs"), 6, "a value is evaluated on the input");
        assert_eq!(after_entry(&p, "keep"), 2, "default.pipe comes first");
        crate::pipe::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("simba") && !is_off("tfunc"));
            assert!(!is_off("semi/peel_shapes"), "off= turns every other pass on");
        });
        assert!(!is_off("relate") && get(var_index("extra").unwrap()) == NONE, "nothing leaks out of a run");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(p.to_string().contains(" extra=5 split_runs=vars * 3 extra=extra + 1 off=relate,tfunc off+=simba off-=tfunc "), "{p}");
        let p = Passes::parse("off-=semi/peel_shapes keep=0 prove_minimal=0 restarts=7 match_limit=9").unwrap();
        assert!(crate::pipe::in_run(&p, None, x, || !is_off("semi/peel_shapes")));
        assert_eq!([after_entry(&p, "keep"), after_entry(&p, "prove_minimal"), after_entry(&p, "restarts")], [0, 0, 7]);
        assert!(crate::pipe::in_run(&p, None, x, || p.egglog_schedule().contains(":match-limit 9 :ban-length 3")));
        let p = Passes::parse("off=").unwrap();
        assert_eq!(p.entry[p.defaults..], [Pass::On(INNER.to_vec())]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let cli = crate::Cli { max_restarts: 5, iter_limit: 3, passes: Passes::parse("iter_limit=iter_limit*2").unwrap(), ..Default::default() };
        let (m, i) = crate::pipe::in_run(&cli.passes, Some(&cli), x, || (get(RESTARTS), get(ITER_LIMIT)));
        assert_eq!((m, i), (5, 6), "-m and -i come before the --passes items");
        let shown = cli.passes.show_run(5, 3);
        assert!(shown.starts_with("# A run: keep = 2 | ") && shown.contains("| restarts = 5 | iter_limit = 3 | iter_limit = iter_limit * 2 | pipeline\n"), "{shown}");
        assert_eq!(Passes::parse(&shown).unwrap(), cli.passes);
        for bad in ["minimal=0", "relate=none", "nope=1", "split_runs=4 | rewrite", "keep+=1", "size=3"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn time_limit_zero_is_a_deadline() {
        let at = |spec: &str| crate::pipe::in_run(&Passes::parse(spec).unwrap(), None, x, || (get(DEADLINE), epoch_ns()));
        assert_eq!(at("time_limit=none").0, NONE);
        let (deadline, now) = at("time_limit=0");
        assert!(deadline <= now, "0 is a deadline now");
        let (deadline, now) = at("time_limit=2000");
        assert!(deadline > now + 1_000_000_000 && deadline <= now + 2_000_000_000);
        assert_eq!(at("time_limit=1000 time_limit=none").0, NONE, "a later item wins");
    }

    #[test]
    fn spec_round_trip() {
        assert_eq!(Passes::parse("").unwrap(), Passes::default());
        let p = Passes::parse("pre-=halve_input,unified;polish=factor,push_not,factor extra=0 keep=3 prove_minimal=0").unwrap();
        assert!(!p.pre_on("unified") && p.pre_on("no_wide"));
        assert_eq!(p.polish, lang::parse(&polish(&["factor", "push_not", "factor"])).unwrap());
        assert_eq!(lang::parse(&Passes::default().polish.to_string()).unwrap(), Passes::default().polish);
        let p = Passes::parse("rewrite=(regions (best 1 simba poly_mba))").unwrap();
        assert_eq!(p.rewrite.to_string(), "(regions (best 1 simba poly_mba))");
        assert_eq!(lang::parse(&Passes::default().simba.to_string()).unwrap(), Passes::default().simba);
        let p = Passes::parse("sub/cluster=(regions simba) sub/split_bits=rewrite").unwrap();
        assert_eq!(p.subs[sub_index("cluster")].to_string(), "(regions simba)");
        assert!(p.to_string().contains(" sub/cluster=(regions simba) sub/split_bits=rewrite"));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("sub/nope=rewrite").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("polish+=factor").is_err() && Passes::parse("polish=nope").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("pre+=nope").is_err() && Passes::parse("keep+=1").is_err());
        let p = Passes::parse("off=semi/bit_split,relate").unwrap();
        assert_eq!(p.entry[p.defaults..], [Pass::On(INNER.to_vec()), Pass::Off(vec!["semi/bit_split", "relate"])]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(crate::pipe::in_run(&p, None, x, || is_off("relate") && !is_off("simba")));
        assert!(!is_off("relate"));
        in_scope(|| {
            turn_off("poly_mba");
            assert!(is_off("poly_mba") && !is_off("lowbits"));
        });
        assert!(!is_off("poly_mba"));
        let p = Passes::parse("prepass=(if (mul < 1 && size >= 10 || vars >= 3) (off lowbits)) | lowbits").unwrap();
        assert_eq!(p.prepass.to_string(), "(if (mul < 1 && size >= 10 || vars >= 3) (off lowbits)) | lowbits");
        assert!(Passes::parse("prepass=(if (nope >= 1) id)").is_err() && Passes::parse("prepass=(off nope)").is_err() && Passes::parse("prepass=(if (mul >= x) id)").is_err());
        let e = Passes::parse("prepass=seq(lowbits,rewrite)").unwrap_err();
        assert!(e.contains("no longer read"), "{e}");
        let p = Passes::parse("schedule-=sat:analysis schedule+=once:simplify,sat:analysis match_limit=128").unwrap();
        assert_eq!(p.schedule.last(), Some(&(Step::Saturate, "analysis")));
        assert_eq!(p.schedule.len(), 7);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("schedule=run:nope").is_err() && Passes::parse("schedule=go:simplify").is_err());
        let p = Passes::parse("split_runs=4 poly_builds=64").unwrap();
        assert!(p.to_string().contains(" split_runs=4 poly_builds=64 "));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("split_runs+=1").is_err() && Passes::parse("split_runs=x").is_err());
        assert_eq!(limit(Limit::SplitRuns), 16);
        let got = crate::pipe::in_run(&p, None, x, || (limit(Limit::SplitRuns), limit(Limit::PolyBuilds), limit(Limit::SplitDepth)));
        assert_eq!(got, (4, 64, 2));
        assert_eq!(limit(Limit::SplitRuns), 16);
        let p = Passes::parse("keep=1 pipeline=lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish/factor extra=0").unwrap();
        assert_eq!(p.pipeline.to_string(), "lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish/factor");
        assert_eq!((after_entry(&p, "keep"), after_entry(&p, "extra")), (1, 0));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let p = Passes::parse("pipeline=(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish) id))").unwrap();
        assert_eq!(p.pipeline.to_string(), "(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(lang::parse(&Passes::default().pipeline.to_string()).unwrap(), Passes::default().pipeline);
        assert_eq!(lang::parse(&Passes::default().prepass.to_string()).unwrap(), Passes::default().prepass);
        let d = Passes::default();
        assert_eq!(Passes::parse(&d.to_string()).unwrap(), d);
        assert_eq!(Passes::parse(&format!("{d:#}")).unwrap(), d);
        let p = Passes::parse("extra=0 prepass=lowbits | (if mixed rewrite) # a comment\n| polish keep=3;pipeline=(fix 2 prepass | egglog)").unwrap();
        assert_eq!((after_entry(&p, "extra"), after_entry(&p, "keep")), (0, 3));
        assert_eq!(p.prepass, lang::parse("(seq lowbits (if mixed rewrite id) polish)").unwrap());
        assert_eq!(p.pipeline, lang::parse("(fix 2 (seq prepass egglog))").unwrap());
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let p = Passes::parse("prepass=(scope (save t) | (with rewrites=unified_rewrites semi_leaves=2 rewrite) | (filter (size < (size t) || size <= (size t) * 3 / 4 && !tiny)) | (cand halve_input (load t)))").unwrap();
        assert_eq!(p.prepass.to_string(), "(scope (save t) | (rewrites = unified_rewrites | semi_leaves = 2 | rewrite) | (filter (size < (size t) || size <= (size t) * 3 / 4 && !tiny)) | (cand halve_input (load t)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["prepass=(filter lt)", "prepass=(filter (size <=))", "prepass=(with rewrites=x id)", "prepass=(with nope=1 id)", "prepass=(save)", "prepass=(scope id id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        assert_eq!(Passes::default().check(), Ok(()));
        assert_eq!(Passes::default().polish, lang::parse(&polish(&crate::linear_mba::POLISH.map(|(n, _)| n))).unwrap());
        let p = Passes::parse("(let twice (fix 2 rewrite)) rewrite=twice | (best 1 twice simba) pipeline=(fix 1 first_round) | polish").unwrap();
        assert_eq!(p.rewrite, lang::parse("(fix 2 rewrite) | (best 1 (fix 2 rewrite) simba)").unwrap());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["(let rewrite id)", "(let x id) (let y nope)", "(let x id) extra", "pipeline=undefined_name", "file=no/such/file.pipe"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        let dir = std::env::temp_dir().join(format!("eggy1-passes-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("a.pipe");
        std::fs::write(&f, "# a file
(let r2 rewrite | rewrite)
extra=1
prepass=lowbits | r2
").unwrap();
        let p = Passes::parse(&format!("file={} keep=3", f.display())).unwrap();
        assert_eq!((after_entry(&p, "extra"), after_entry(&p, "keep")), (1, 3));
        assert_eq!(p.prepass, lang::parse("lowbits | rewrite | rewrite").unwrap());
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(Passes::parse("rewrite=(fix (restarts - 1) rewrite)").is_ok(), "restarts is a variable");
        for bad in ["prepass=egglog", "simba=reprint", "sub/cluster=(egglog first)", "prepass=lowbits | prepass", "polish=polish", "rewrite=(again polish)", "prepass=(if rebuilds id)"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("simplify run") || e.contains("reaches itself"), "{bad}: {e}");
        }
        assert!(Passes::parse("pipeline=(fix restarts prepass | egglog | polish)").is_ok());
        for bad in ["prepass=(load x)", "prepass=(save t) | (load u)", "prepass=(load t) | (save t)", "polish=(filter (size < (size t)))", "rewrite=(if (same t) id)", "prepass=(if mixed (save t)) | (label u)", "pipeline=(retry (size < (size t)) id (save t))"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("before any (save"), "{bad}: {e}");
        }
        for good in ["prepass=(if mixed (save t)) | (load t)", "prepass=(fix 3 (union (load t) id) | (save t))", "pipeline=(retry (size < (size t)) (save t) (load t))", "prepass=(best (size t) (save t) id)"] {
            assert!(Passes::parse(good).is_ok(), "{good}");
        }
        assert_eq!(Passes::default().warnings(), Vec::<String>::new());
        let mut lets = Lets::default();
        Passes::base().apply(include_str!("default.pipe"), &mut lang::Defs::new(), &mut lets).unwrap();
        assert!(lets.defined.iter().all(|n| lets.used.contains(n)), "{:?} {:?}", lets.defined, lets.used);
        let (_, w) = Passes::parse_noting("(let foo rewrite) (let bar lowbits) prepass=bar | (save t) | (save q) | (load t) | ((off relate) | (save x) | id) | (rewrite | (off relate))").unwrap();
        assert_eq!(w.len(), 4, "{w:?}");
        assert!(w[0].contains("let foo") && w[1].contains("register q") && w[2].contains("register x") && w[3].contains("(off relate) ends"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=(save t) | rewrite | (save t) | (load t)").unwrap();
        assert!(w.len() == 1 && w[0].contains("saved again"), "{w:?}");
        for ok in ["prepass=(save t) | (if mixed (save t)) | (load t)", "prepass=(save t) | (cand unified (save t)) | (load t)", "prepass=(fix 3 (save t) | rewrite) | (load t)", "prepass=(save t) | (filter (size < (size t))) | (save t) | (load t)", "prepass=(save t) | (first rewrite (save t)) | (load t)", "prepass=(if mixed (save t) (save t)) | (load t)"] {
            assert_eq!(Passes::parse_noting(ok).unwrap().1, Vec::<String>::new(), "{ok}");
        }
        let p = Passes::parse("prepass=rewrite | (time-limit 500) | relate | (time-limit (size-1 * 2)) | tfunc | (time-limit 0) | lowbits").unwrap();
        assert_eq!(p.prepass.to_string(), "rewrite | time_limit = 500 | relate | time_limit = size - 1 * 2 | tfunc | time_limit = none | lowbits");
        assert_eq!(p, Passes::parse(&p.prepass.to_string().replace("rewrite |", "prepass=rewrite |")).unwrap());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("prepass=(time-limit)").is_err() && Passes::parse("prepass=time-limit").is_err() && Passes::parse("prepass=(time-limit mixed)").is_err());
        assert!(Passes::parse("prepass=(if (size-x > 1) id)").unwrap_err().contains("size-x"));
        let (_, w) = Passes::parse_noting("prepass=rewrite | (time-limit 100)").unwrap();
        assert!(w.len() == 1 && w[0].contains("time_limit = 100 ends its sequence"), "{w:?}");
        assert_eq!(Passes::parse_noting("prepass=rewrite | (if mixed (time-limit 100)) | relate").unwrap().1, Vec::<String>::new());
        let flat = Passes::parse("(let g relate | tfunc) (let h (relate | tfunc)) prepass=lowbits | g | finish rewrite=lowbits | h | finish").unwrap();
        assert_eq!(flat.prepass.to_string(), "lowbits | relate | tfunc | finish");
        assert_eq!(flat.rewrite.to_string(), "lowbits | (relate | tfunc) | finish");
        let p = Passes::parse("prepass=(off relate tfunc) | (on relate cut) | rewrite time_limit=500").unwrap();
        assert_eq!(p.prepass.to_string(), "(off relate tfunc) | (on relate cut) | rewrite");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("prepass=(on nope)").is_err() && Passes::parse("prepass=(on)").is_err() && Passes::parse("prepass=on/relate").is_err());
        assert!(Passes::parse("prepass=(with off=relate rewrite)").unwrap_err().contains("(off relate)"), "with takes no off=");
        let (_, w) = Passes::parse_noting("prepass=rewrite | (scope (with rewrites=8 (off relate))) | (off cut) | lowbits").unwrap();
        assert!(w.len() == 1 && w[0].contains("(off relate) ends its sequence"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=(with semi_leaves=2 rewrite) polish=(scope (with semi_leaves=2 rewrite)) rewrite=(with semi_leaves=2 simba)").unwrap();
        assert!(w.is_empty(), "a with outside any scope binds too: {w:?}");
        let e = Passes::parse("prepass=save/t").unwrap_err();
        assert!(e.contains("(save t)"), "{e}");
        for bad in ["pipeline=nope", "pipeline=(seq rewrite", "pipeline=(best x rewrite)", "pipeline=(fix 2 a b)", "pipeline=(with nope=1 rewrite)", "pipeline=(loop rewrite)", "pipeline=(fix many id)", "pipeline=(if nope id)", "pipeline=(if mixed id id id)", "pipeline=(retry mixed id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        with_off(&["relate"], || {
            assert!(crate::pipe::in_run(&Passes::default(), None, x, || is_off("relate")));
        });
        assert!(!is_off("relate"));
    }

    #[test]
    fn assignment_items_and_warnings() {
        let p = Passes::parse("prepass=lowbits | split_runs=4 | rewrite").unwrap();
        assert_eq!(p.prepass.to_string(), "lowbits | split_runs = 4 | rewrite");
        assert_eq!(p.entry, Passes::default().entry, "an assignment after | stays in the pipeline");
        let p = Passes::parse("prepass=lowbits split_runs=4").unwrap();
        assert_eq!((p.prepass.to_string().as_str(), after_entry(&p, "split_runs")), ("lowbits", 4));
        let p = Passes::parse("prepass=lowbits | split_runs = vars * 2 | rewrite extra=0").unwrap();
        assert_eq!((p.prepass.to_string().as_str(), after_entry(&p, "extra")), ("lowbits | split_runs = vars * 2 | rewrite", 0));
        let p = Passes::parse("time_limit=2000 cand_bit_splits=3").unwrap();
        assert_eq!(after_entry(&p, "cand_bit_splits"), 3);
        assert!(p.to_string().contains(" time_limit=2000 cand_bit_splits=3 "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(after_entry(&Passes::parse("bit_split_budget=8").unwrap(), "bit_split_budget"), 8, "any variable is an item");
        let warn = |s: &str| Passes::parse_noting(s).unwrap().1;
        assert!(warn("prepass=rewrite | split_runs = 4").iter().any(|w| w.contains("split_runs = 4 ends its sequence")));
        assert!(warn("prepass=(off relate)").iter().any(|w| w.contains("(off relate) ends")), "a pipeline is a sequence too");
        let w = warn("prepass=split_runs = 4 | split_runs = 8 | rewrite");
        assert!(w.len() == 1 && w[0].contains("split_runs is assigned again"), "{w:?}");
        let w = warn("prepass=(off relate) | relate = 1 | rewrite");
        assert!(w.len() == 1 && w[0].contains("relate is assigned again"), "{w:?}");
        for ok in ["prepass=split_runs = 4 | rewrite | split_runs = 8 | rewrite", "prepass=split_runs = 4 | split_runs = split_runs * 2 | rewrite", "prepass=split_runs = 4 | (split_runs = 8 | rewrite) | rewrite", "prepass=cut = 1 | rewrite"] {
            assert_eq!(warn(ok), Vec::<String>::new(), "{ok}");
        }
    }
}
