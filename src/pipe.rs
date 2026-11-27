//! Runs a `sched::Pipe`. Every pass maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another: a pass over one term (`linear_mba::TERM_PASSES`, the
//! polish passes as `polish/NAME`) runs on each candidate and replaces it by its result; the
//! other passes take the list whole.

use crate::eval::{Op, Term, parse, show, size};
use crate::linear_mba::{CLUSTERED, Ctx, WIDE};
use crate::sched::{Expr, Limit, NONE, Pass, Passes, Pipe, TermAt, limit};
use crate::{Cli, Error, linear_mba, minimal, stats, width_of};
use std::cell::{Cell, OnceCell, RefCell};
use std::rc::Rc;
use std::collections::HashMap;

/// Passes that take the candidate list whole, besides `(save R)`, `(load R)` and `(label R)`.
pub const SET_PASSES: [&str; 9] = [
    // The candidates unchanged.
    "id",
    // No candidates.
    "none",
    // The main candidate's pre-pass rebuilds: the main one, then those to union with it.
    "prepass",
    // One egglog round on all candidates unioned: its extraction (`(egglog LABEL)` times it
    // as `egglog/LABEL`).
    "egglog",
    // The first candidate proved minimal (`minimal`).
    "take_minimal",
    // `Passes::polish` on each candidate alone, its first result kept when smaller.
    "polish",
    // The main candidate printed and read back.
    "reprint",
    // No candidates once `rewrite` has used up its calls in the scope under way.
    "within",
    // The end of the pre-pass: counts the kept candidates, names their origins `pre/NAME`
    // and gives the main one as the input was written when it equals it (register `t0`).
    "pre_done",
];

/// The functions of expressions that give 1 or 0 for the candidates they see (`Expr::Is`).
pub const CONDS: [&str; 17] = [
    // The main candidate has a shift, division or mulhi and its rebuild is not tiny.
    "opaque",
    // A candidate is proved minimal: no smaller term equals it (with `prove_minimal` on).
    "minimal",
    // The main candidate has arithmetic or a constant directly under a bitwise operation.
    "mixed",
    // The pre-pass changes the main candidate.
    "rebuilds",
    // The last `fix` stopped at its count, the main candidate still changing.
    "moved",
    // The main candidate is the input of `simplify`.
    "input",
    // The main candidate has at most `tiny_size` nodes.
    "tiny",
    // The main candidate has at most `split_size` nodes.
    "fits_split",
    // `wide_blocks` gave a kept form in the passes that made a candidate.
    "used_wide",
    // `clustered` gave a kept form in the passes that made a candidate.
    "used_clustered",
    // The passes that made the main candidate made at most `unclustered_after` uncached
    // `rewrite` calls.
    "few_rewrites",
    // The main candidate as a whole has a smaller T-function form (`tfunc::replacement`).
    "replaceable",
    // The main candidate comes from a rebuild with abstracted subterms
    // (`linear_mba::ABSTRACTED`).
    "abstracted",
    // The main candidate is a linear region without leaves.
    "no_leaves",
    // The main candidate is a linear region of more than `max_leaves` leaves.
    "wide",
    // The main candidate has a bitwise operation with a constant operand.
    "const_bitwise",
    // The run rebuilds a linear cofactor of `poly_mba` (`simba_memo`).
    "cofactor",
];

/// The input features of `stats::shape` that conditions compare (`mul >= 4`).
pub const FEATURES: [&str; 8] = ["size", "vars", "depth", "mul", "bitconst", "arith_in_bit", "shift", "div"];

fn feature(s: &stats::Shape, i: usize) -> usize {
    match FEATURES[i] {
        "size" => s.size,
        "vars" => s.vars,
        "depth" => s.depth,
        "mul" => s.mul,
        "bitconst" => s.bitconst,
        "arith_in_bit" => s.arith_in_bit,
        "shift" => s.shift,
        "div" => s.div,
        name => unreachable!("feature {name}"),
    }
}

/// The pass of the internal name `name`: `Pass::name`, `save/R` for `(save R)`.
pub fn resolve(name: &str) -> Option<Pass> {
    for (p, f) in [("save/", Pass::Save as fn(String) -> Pass), ("load/", Pass::Load), ("label/", Pass::Label)] {
        if let Some(r) = name.strip_prefix(p).filter(|r| !r.is_empty()) {
            return Some(f(r.to_string()));
        }
    }
    if name == "egglog" || name.strip_prefix("egglog/").is_some_and(|r| !r.is_empty()) {
        return Some(Pass::Egglog(name.to_string()));
    }
    if let Some(n) = name.strip_prefix("off/") {
        return crate::sched::switch(n).map(|n| Pass::Off(vec![n]));
    }
    if let Some(n) = name.strip_prefix("on/") {
        return crate::sched::switch(n).map(|n| Pass::On(vec![n]));
    }
    if let Some(i) = SET_PASSES.iter().position(|n| *n == name) {
        return Some(Pass::Set(i));
    }
    let alt = linear_mba::ALTERNATIVES.iter().find(|(a, _)| *a == name).map(|(_, bit)| *bit);
    if let Some(i) = linear_mba::TERM_PASSES.iter().position(|(n, _)| *n == name) {
        return Some(Pass::Term { name: name.to_string(), at: TermAt::Term(i), alt });
    }
    let i = linear_mba::POLISH.iter().position(|(n, _)| name.strip_prefix("polish/") == Some(n))?;
    Some(Pass::Term { name: name.to_string(), at: TermAt::Polish(i), alt })
}


/// A candidate term and the pass it came from, for `stats` (`final/ORIGIN`). The egglog
/// text, the tree and the size are each made once, when first needed: large inputs spend
/// more time printing and parsing than in the passes.
#[derive(Clone, Debug)]
pub struct Cand {
    forms: Rc<Forms>,
    pub origin: String,
    /// Which of `clustered` and `wide_blocks` gave a kept form in the passes that made it.
    used: u8,
    /// The uncached `rewrite` calls of the passes that made it.
    rewrites: usize,
}

#[derive(Debug, Default)]
struct Forms {
    text: OnceCell<String>,
    tree: OnceCell<Term>,
    size: OnceCell<usize>,
}

impl Cand {
    pub fn new(text: &str, origin: &str) -> Cand {
        Cand { forms: Rc::new(Forms { text: OnceCell::from(text.to_string()), ..Default::default() }), origin: origin.to_string(), used: 0, rewrites: 0 }
    }

    /// `tree` made from `from` by a pass with these `used` bits and `rewrites` calls.
    fn of(tree: Term, from: &Cand, used: u8, rewrites: usize) -> Cand {
        let forms = Rc::new(Forms { tree: OnceCell::from(tree), ..Default::default() });
        Cand { forms, origin: from.origin.clone(), used: from.used | used, rewrites: from.rewrites + rewrites }
    }

    /// The egglog text.
    pub fn term(&self) -> &str {
        self.forms.text.get_or_init(|| show(self.tree()))
    }

    fn tree(&self) -> &Term {
        self.forms.tree.get_or_init(|| parse(self.forms.text.get().unwrap()))
    }

    fn size(&self) -> usize {
        *self.forms.size.get_or_init(|| size(self.tree()))
    }

    fn into_tree(self) -> Term {
        match Rc::try_unwrap(self.forms) {
            Ok(f) => f.tree.into_inner().unwrap_or_else(|| parse(f.text.get().unwrap())),
            Err(f) => f.tree.get_or_init(|| parse(f.text.get().unwrap())).clone(),
        }
    }

    fn same(&self, o: &Cand) -> bool {
        if Rc::ptr_eq(&self.forms, &o.forms) {
            return true;
        }
        if let (Some(a), Some(b)) = (self.forms.text.get(), o.forms.text.get())
            && a == b
        {
            return true;
        }
        self.size() == o.size() && self.tree() == o.tree()
    }
}

impl PartialEq for Cand {
    fn eq(&self, o: &Cand) -> bool {
        self.origin == o.origin && self.same(o)
    }
}

/// What the passes of one run share.
pub struct Env<'a> {
    /// Set for a `simplify` run; egglog rounds, minimality proofs and `reprint` need it.
    cli: Option<&'a Cli>,
    passes: &'a Passes,
    w: u32,
    signed: Option<bool>,
    trace: bool,
    /// The egglog program of the numeric type.
    egg: Rc<str>,
    /// The run's input, registers and arguments; those of the call where a pipeline argument
    /// is written while it runs.
    lex: RefCell<Rc<Lex>>,
    moved: Cell<bool>,
    /// Results the `smaller` inside the innermost `wins` took.
    wins: Cell<usize>,
    /// Set inside a `regions`: the `won` its `best` would count, left for `regions` to count
    /// with the form it builds.
    deferred: RefCell<Option<Option<Won>>>,
    /// The run rebuilds a linear cofactor of `poly_mba`.
    cofactor: bool,
    /// The smallest candidate each enclosing `smallest` saw, innermost last.
    seen: RefCell<Vec<Option<(usize, Cand)>>>,
    /// The runs of the enclosing `scope`s, innermost last.
    ctxs: RefCell<Vec<Ctx>>,
}

/// What a pipeline argument takes along from the run where it is written (a closure): the
/// run's input and registers and the arguments of the call that run is.
struct Lex {
    input: String,
    /// Shared with the caller in the call of an `@inline` function.
    regs: Rc<RefCell<HashMap<String, Vec<Cand>>>>,
    frame: Option<Frame>,
}

impl Lex {
    fn new(input: &str, frame: Option<Frame>) -> Rc<Lex> {
        Rc::new(Lex { input: input.to_string(), regs: Default::default(), frame })
    }
}

/// The arguments of a call of a function with parameters.
struct Frame {
    call: std::sync::Arc<crate::sched::Call>,
    /// The run where the call is written, which its pipeline arguments run with.
    caller: Rc<Lex>,
    /// By parameter position, the values of the numeric arguments; empty without any.
    values: Vec<u64>,
}

impl<'a> Env<'a> {
    pub fn new(cli: &'a Cli, egg: String, input: &str) -> Env<'a> {
        let signed = crate::eval::NumType::from_name(&cli.num_type).map(|t| t.signed);
        Env::with(Some(cli), &cli.passes, width_of(&cli.num_type), signed, cli.trace, egg, input)
    }

    /// A pre-pass run on `input` at width `w`, `signed` as in `linear_mba::Ctx`.
    pub fn prepass(p: &'a Passes, w: u32, signed: Option<bool>, trace: bool, input: &str) -> Env<'a> {
        Env::with(None, p, w, signed, trace, String::new(), input)
    }

    fn with(cli: Option<&'a Cli>, passes: &'a Passes, w: u32, signed: Option<bool>, trace: bool, egg: String, input: &str) -> Env<'a> {
        let lex = RefCell::new(Lex::new(input, None));
        Env { cli, passes, w, signed, trace, egg: egg.into(), lex, moved: Cell::new(false), wins: Cell::new(0), deferred: Default::default(), cofactor: false, seen: Default::default(), ctxs: Default::default() }
    }

    fn cli(&self, pass: &str) -> &'a Cli {
        self.cli.unwrap_or_else(|| panic!("{pass} needs a simplify run"))
    }

    fn prepass_of(&self, s: &str) -> (String, Vec<String>) {
        linear_mba::simplify_linear_with(s, self.w, self.signed, self.trace, self.passes)
    }

    /// `f` on the run of the innermost `scope`, or on a fresh one.
    fn ctx<R>(&self, f: impl FnOnce(&Ctx) -> R) -> R {
        match self.ctxs.borrow().last() {
            Some(c) => f(c),
            None => f(&Ctx::typed(self.w, self.signed)),
        }
    }

    fn reg_main(&self, r: &str) -> Option<Cand> {
        self.lex.borrow().regs.borrow().get(r).and_then(|s| s.first().cloned())
    }

    /// `e` for the candidates `set`: a number or `NONE`.
    fn value(&self, e: &Expr, set: &[Cand]) -> u64 {
        let main = || set.first();
        match e {
            Expr::Num(n) => *n,
            Expr::Feature(0) => main().map_or(0, |m| m.size() as u64),
            Expr::Feature(i) => main().map_or(0, |m| feature(&stats::shape(m.tree()), *i) as u64),
            Expr::Is(i) => cond(*i, set, self) as u64,
            Expr::Size(r) => self.reg_main(r).map_or(0, |c| c.size() as u64),
            Expr::Same(r) => main().zip(self.reg_main(r)).is_some_and(|(m, c)| c.same(m)) as u64,
            Expr::Var(i) if *i == crate::sched::DEADLINE => match crate::sched::read(*i) {
                NONE => NONE,
                at => at.saturating_sub(crate::sched::epoch_ns()) / 1_000_000,
            },
            Expr::Var(i) if *i == crate::sched::KEEP => crate::sched::read(*i).max(1),
            Expr::Var(i) => crate::sched::read(*i),
            Expr::Param(i, _) => self.lex.borrow().frame.as_ref().expect("a parameter outside the body of its function").values[*i],
            Expr::Not(c) => !self.holds(c, set) as u64,
            Expr::And(cs) => cs.iter().all(|c| self.holds(c, set)) as u64,
            Expr::Or(cs) => cs.iter().any(|c| self.holds(c, set)) as u64,
            Expr::Cmp(op, a, b) => op.holds(self.value(a, set), self.value(b, set)) as u64,
            Expr::Bin(op, a, b) => crate::sched::arith(*op, self.value(a, set), self.value(b, set)),
            Expr::Any(c) => set.iter().any(|x| self.holds(c, std::slice::from_ref(x))) as u64,
            Expr::All(c) => (!set.is_empty() && set.iter().all(|x| self.holds(c, std::slice::from_ref(x)))) as u64,
        }
    }

    /// Whether `e` is not 0 for the candidates `set`.
    fn holds(&self, e: &Expr, set: &[Cand]) -> bool {
        self.value(e, set) != 0
    }

    /// `e` as a count: `none` is no limit.
    fn times(&self, e: &Expr, set: &[Cand]) -> usize {
        self.value(e, set).try_into().unwrap_or(usize::MAX)
    }
}

fn dedup(set: Vec<Cand>) -> Vec<Cand> {
    let mut out: Vec<Cand> = Vec::with_capacity(set.len());
    for c in set {
        if !out.iter().any(|o| o.same(&c)) {
            out.push(c);
        }
    }
    out
}

fn size_of(s: &str) -> usize {
    size(&parse(s))
}

/// Whether `t` has a shift, division or mulhi.
fn opaque(t: &Term) -> bool {
    match t {
        Term::Op(Op::Shl | Op::Shr | Op::Div | Op::Mod | Op::Mulhi, _) => true,
        Term::Op(_, a) => a.iter().any(opaque),
        _ => false,
    }
}

/// The first candidate of `set` proved minimal. Without a shift, division or mulhi in the
/// candidates, only smaller terms without them need ruling out: no rule makes one.
fn proved_minimal<'s>(set: &'s [Cand], env: &Env) -> Option<&'s Cand> {
    let cli = env.cli?;
    if crate::sched::get(crate::sched::PROVE_MINIMAL) == 0 {
        return None;
    }
    let t_only = !set.iter().any(|c| opaque(c.tree()));
    let ty = crate::eval::NumType::from_name(&cli.num_type);
    set.iter().find(|c| {
        let t = c.tree();
        minimal::is_tidy(t) && (ty.is_some_and(|ty| minimal::is_minimal(t, ty)) || t_only && minimal::is_t_minimal(t))
    })
}

fn cond(i: usize, set: &[Cand], env: &Env) -> bool {
    let Some(main) = set.first() else { return false };
    match CONDS[i] {
        "opaque" => opaque(main.tree()) && size_of(&env.prepass_of(main.term()).0) > limit(Limit::TinySize),
        "minimal" => proved_minimal(set, env).is_some(),
        "mixed" => crate::mixed(main.tree()),
        "rebuilds" => env.prepass_of(main.term()).0 != main.term(),
        "moved" => env.moved.get(),
        "input" => main.term() == env.lex.borrow().input,
        "tiny" => main.size() <= limit(Limit::TinySize),
        "fits_split" => main.size() <= limit(Limit::SplitSize),
        "used_wide" => set.iter().any(|c| c.used & WIDE != 0),
        "used_clustered" => set.iter().any(|c| c.used & CLUSTERED != 0),
        "few_rewrites" => main.rewrites <= limit(Limit::UnclusteredAfter),
        "replaceable" => env.ctx(|c| crate::tfunc::replacement(main.tree(), c).is_some()),
        "abstracted" => linear_mba::ABSTRACTED.contains(&main.origin.as_str()),
        "no_leaves" => env.ctx(|w| linear_mba::leaf_count(main.tree(), w) == 0),
        "wide" => env.ctx(|w| linear_mba::leaf_count(main.tree(), w) > limit(Limit::MaxLeaves)),
        "const_bitwise" => env.ctx(|w| linear_mba::const_bitwise(main.tree(), w)),
        "cofactor" => env.cofactor,
        name => unreachable!("condition {name}"),
    }
}

thread_local! {
    /// Some pass was skipped past a limit while the switch `cut` was on.
    static CUT: Cell<bool> = const { Cell::new(false) };
    /// Seconds the last egglog round took.
    static LAST_ROUND: Cell<f64> = const { Cell::new(0.0) };
}

/// Starts a `simplify` run on this thread: no limit, no cut, no egglog round timed yet.
pub fn start() {
    crate::sched::set(crate::sched::DEADLINE, crate::sched::NONE);
    CUT.with(|c| c.set(false));
    LAST_ROUND.with(|r| r.set(0.0));
}

/// Whether a step was skipped past a limit with `cut` on since `start`.
pub fn cut() -> bool {
    CUT.with(|c| c.get())
}

/// Whether work taking `secs` more would end past the `time_limit` in force; counts the
/// skipped step (`time_limit/skipped`), and records a cut of the run when the switch `cut` is
/// on. Results computed then are not memoized (`Ctx::mark_cut`).
fn past_deadline(secs: f64, env: &Env) -> bool {
    let at = crate::sched::get(crate::sched::DEADLINE);
    if at == crate::sched::NONE || crate::sched::epoch_ns().saturating_add((secs * 1e9) as u64) < at {
        return false;
    }
    stats::add("time_limit/skipped", 0.0);
    if crate::sched::is_on("cut") {
        CUT.with(|c| c.set(true));
    }
    env.ctx(|c| c.mark_cut());
    true
}

/// `f` as a scope (a sequence, `scope` or a pipeline run): an assignment inside it ends
/// with it.
fn scoped<R>(f: impl FnOnce() -> R) -> R {
    crate::sched::in_scope(f)
}

thread_local! {
    static IN_RUN: Cell<bool> = const { Cell::new(false) };
    /// The first error of the run under way that a nested run could not return.
    static FAILED: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// Records `e` as the run's error: every later step and `run` give it.
pub(crate) fn fail(e: &Error) {
    FAILED.with(|f| {
        f.borrow_mut().get_or_insert_with(|| e.to_string());
    });
}

/// The error recorded by `fail` in the run under way.
pub(crate) fn failed() -> Option<Error> {
    FAILED.with(|f| f.borrow().clone()).map(Error::BackendError)
}

/// `f` as part of a run of `p`: when no run is under way on this thread, as the outermost
/// scope of one, after its entry assignments (`Passes::entry_steps`, with `restarts` and
/// `iter_limit` of `cli`) evaluated on the candidate `input` gives; they all end with it.
pub fn in_run<R>(p: &Passes, cli: Option<&Cli>, input: impl FnOnce() -> Cand, f: impl FnOnce() -> R) -> R {
    if IN_RUN.with(Cell::get) {
        return f();
    }
    crate::sched::set_current(p);
    FAILED.with(|f| f.borrow_mut().take());
    struct Out;
    impl Drop for Out {
        fn drop(&mut self) {
            IN_RUN.with(|r| r.set(false));
        }
    }
    scoped(|| {
        IN_RUN.with(|r| r.set(true));
        let _out = Out;
        let env = Env::with(cli, p, cli.map_or(64, |c| width_of(&c.num_type)), None, false, String::new(), "");
        let set = vec![input()];
        for step in p.entry_steps(cli.map(|c| (c.max_restarts, c.iter_limit))) {
            if let Err(e) = pass(&step, set.clone(), &env) {
                fail(&e);
            }
        }
        f()
    })
}

/// The candidates `p` gives for `set`.
pub fn run(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    let first = set.first().cloned();
    let input = || first.unwrap_or_else(|| Cand::new(&env.lex.borrow().input, "input"));
    in_run(env.passes, env.cli, input, || scoped(|| go(p, set, env)).and_then(|out| failed().map_or(Ok(out), Err)))
}

/// `time_limit = ms` in the scope under way.
fn assign_time_limit(ms: u64) {
    let at = match ms {
        crate::sched::NONE => crate::sched::NONE,
        _ => crate::sched::epoch_ns().saturating_add(ms.saturating_mul(1_000_000)),
    };
    crate::sched::bind(crate::sched::DEADLINE, at);
}

/// Steps that only move candidates around: they run past a limit too, so that a sequence
/// still has its registers and can go on after a `time_limit = none`.
fn bookkeeping(p: &Pipe) -> bool {
    match p {
        Pipe::Seq(_) | Pipe::Filter(_) | Pipe::Param(..) => true,
        Pipe::Call(c) => c.def.inline,
        Pipe::Pass(Pass::Save(_) | Pass::Load(_) | Pass::Label(_) | Pass::Off(_) | Pass::On(_) | Pass::Assign(..)) => true,
        Pipe::Pass(Pass::Set(i)) => matches!(SET_PASSES[*i], "id" | "none" | "within" | "pre_done"),
        _ => false,
    }
}

fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    // Every candidate equals the input, so stopping anywhere keeps the result right.
    if let Some(e) = failed() {
        return Err(e);
    }
    if !bookkeeping(p) && past_deadline(0.0, env) {
        return Ok(set);
    }
    match p {
        Pipe::Pass(p) => pass(p, set, env),
        Pipe::Seq(ps) => scoped(|| ps.iter().try_fold(set, |s, p| go(p, s, env))),
        Pipe::Union(ps) => {
            let mut out = Vec::new();
            for p in ps {
                out.extend(go(p, set.clone(), env)?);
            }
            Ok(dedup(out))
        }
        Pipe::Best(k, ps) => {
            let mut out = Vec::new();
            for p in ps {
                out.extend(go(p, set.clone(), env)?);
            }
            if stats::on() {
                count_won(&out, &set, env);
            }
            let mut out = dedup(out);
            out.sort_by_cached_key(|c| c.size());
            out.truncate(env.times(k, &set).max(1));
            Ok(out)
        }
        Pipe::First(ps) => {
            for p in ps {
                let out = go(p, set.clone(), env)?;
                if !out.is_empty() && out != set {
                    return Ok(out);
                }
            }
            Ok(set)
        }
        Pipe::Fix(n, p) => {
            let mut set = set;
            for _ in 0..env.times(n, &set) {
                let out = go(p, set.clone(), env)?;
                let same = match (out.first(), set.first()) {
                    (Some(a), Some(b)) => a.same(b),
                    (a, b) => a.is_none() && b.is_none(),
                };
                env.moved.set(!same);
                set = out;
                if same {
                    break;
                }
            }
            Ok(set)
        }
        Pipe::If(c, a, b) => go(if env.holds(c, &set) { a } else { b }, set, env),
        Pipe::Retry(c, a, b) => {
            let out = go(a, set.clone(), env)?;
            if !env.holds(c, &out) {
                return Ok(out);
            }
            let again = go(b, set, env)?;
            let take = match (again.first(), out.first()) {
                (Some(b), Some(a)) => b.size() <= a.size(),
                (b, _) => b.is_some(),
            };
            Ok(if take { again } else { out })
        }
        Pipe::Smallest(p) => {
            env.seen.borrow_mut().push(None);
            let out = go(p, set, env);
            let seen = env.seen.borrow_mut().pop().flatten();
            let out = out?;
            match seen {
                Some((n, c)) if out.first().is_some_and(|m| n < m.size()) => Ok(dedup(std::iter::once(c).chain(out).collect())),
                _ => Ok(out),
            }
        }
        Pipe::Tag(name, p) => {
            let clock = std::time::Instant::now();
            let before = set.first().cloned();
            let mut out = go(p, set, env)?;
            stats::add(&format!("{name}/run"), stats::since(clock));
            if let Some(m) = out.first_mut().filter(|m| !before.as_ref().is_some_and(|b| b.same(m))) {
                stats::add(&format!("{name}/won/{}", m.origin), 0.0);
                m.origin = name.clone();
            }
            Ok(out)
        }
        Pipe::Filter(c) => Ok(set.into_iter().filter(|x| env.holds(c, std::slice::from_ref(x))).collect()),
        Pipe::Cand(name, p) => {
            if crate::sched::PRE.contains(&name.as_str()) && !env.passes.pre_on(name) {
                return Ok(Vec::new());
            }
            let clock = std::time::Instant::now();
            let out = scoped(|| {
                crate::sched::bind(crate::sched::BIT_SPLIT_BUDGET, limit(Limit::CandBitSplits) as u64);
                go(p, set, env)
            })?;
            stats::add(&format!("pre/{name}/made"), stats::since(clock));
            Ok(out.into_iter().map(|c| Cand { origin: name.clone(), ..c }).collect())
        }
        Pipe::Scope(p) => {
            env.ctxs.borrow_mut().push(Ctx::typed(env.w, env.signed));
            let out = scoped(|| go(p, set, env));
            env.ctxs.borrow_mut().pop();
            out
        }
        Pipe::Smaller(name, p) => {
            let clock = std::time::Instant::now();
            let mut out = go(p, set.clone(), env)?;
            stats::add(&format!("{name}/run"), stats::since(clock));
            let (Some(m), Some(before)) = (out.first_mut(), set.first()) else { return Ok(set) };
            if m.size() >= before.size() {
                return Ok(set);
            }
            if env.trace {
                eprintln!("{name}: {} -> {}", before.size(), m.size());
            }
            stats::add(&format!("{name}/won"), 0.0);
            stats::produced(name, m.tree(), before.size() - m.size());
            m.origin = name.clone();
            env.wins.set(env.wins.get() + 1);
            Ok(out)
        }
        Pipe::Regions(p) => {
            let w = env.ctx(|c| c.narrow(c.w));
            let mut out = Vec::with_capacity(set.len());
            for c in set {
                let outer = w.swap_used(0);
                let (mut err, mut won) = (None, None);
                let r = linear_mba::on_region(c.tree(), &w, || {
                    let before = env.deferred.replace(Some(None));
                    let rebuilt = go(p, vec![c.clone()], env);
                    won = env.deferred.replace(before).flatten();
                    match rebuilt {
                        Ok(o) => o.into_iter().next().map(|b| {
                            w.swap_used(w.swap_used(0) | b.used);
                            b.tree().clone()
                        }),
                        Err(e) => {
                            err = Some(e);
                            None
                        }
                    }
                });
                if let Some(e) = err {
                    return Err(e);
                }
                if let Some((name, sizes, input)) = won {
                    let sizes: Vec<(&str, usize)> = sizes.iter().map(|(n, s)| (n.as_str(), *s)).collect();
                    stats::won_among(&name, &sizes, input, &r);
                }
                let used = w.swap_used(0);
                w.swap_used(outer | used);
                out.push(Cand::of(r, &c, used, 0));
            }
            Ok(out)
        }
        Pipe::Again(p) => {
            let mut out = go(p, set.clone(), env)?;
            if let (Some(m), Some(t)) = (out.first_mut(), set.first()) {
                if let Some(r) = env.ctx(|w| linear_mba::again(t.tree(), m.tree(), w)) {
                    *m = Cand::of(r, m, 0, 0);
                }
            }
            Ok(out)
        }
        Pipe::Call(c) if c.def.inline => {
            let caller = env.lex.borrow().clone();
            let values = arg_values(c, &set, env);
            let lex = Lex { input: caller.input.clone(), regs: caller.regs.clone(), frame: Some(Frame { call: c.clone(), caller: caller.clone(), values }) };
            let outer = env.lex.replace(Rc::new(lex));
            let out = match &*c.body {
                Pipe::Seq(ps) if c.def.flat => ps.iter().try_fold(set, |s, p| go(p, s, env)),
                body => go(body, set, env),
            };
            env.lex.replace(outer);
            out
        }
        Pipe::Call(c) => {
            let input = set.first().map_or_else(String::new, |c| c.term().to_string());
            let mut run = Env::with(env.cli, env.passes, env.w, env.signed, env.trace, String::new(), &input);
            run.egg = env.egg.clone();
            run.cofactor = env.cofactor;
            if !c.args.is_empty() {
                let frame = Frame { call: c.clone(), caller: env.lex.borrow().clone(), values: arg_values(c, &set, env) };
                run.lex = RefCell::new(Lex::new(&input, Some(frame)));
            }
            if let Some(c) = env.ctxs.borrow().last() {
                run.ctxs.borrow_mut().push(c.narrow(c.w));
            }
            let out = scoped(|| go(&c.body, set, &run))?;
            Ok(seen(out, env))
        }
        Pipe::Param(i, _) => {
            let (call, caller) = {
                let lex = env.lex.borrow();
                let f = lex.frame.as_ref().expect("a parameter outside the body of its function");
                (f.call.clone(), f.caller.clone())
            };
            let crate::sched::CallArg::Pipe(arg) = &call.args[*i] else { unreachable!("a pipeline parameter") };
            let callee = env.lex.replace(caller);
            let out = go(arg, set, env);
            env.lex.replace(callee);
            out
        }
        Pipe::Wins(n, p) => {
            let n = env.times(n, &set);
            if n == 0 {
                return Ok(set);
            }
            let outer = env.wins.replace(0);
            let mut set = set;
            loop {
                let before = env.wins.get();
                set = go(p, set, env)?;
                if env.wins.get() == before || env.wins.get() >= n {
                    break;
                }
            }
            env.wins.set(outer + env.wins.get());
            Ok(set)
        }
    }
}

/// The values of the numeric arguments of `c` on the caller's candidates `set`, by parameter
/// position; empty without any.
fn arg_values(c: &crate::sched::Call, set: &[Cand], env: &Env) -> Vec<u64> {
    use crate::sched::CallArg;
    if !c.args.iter().any(|a| matches!(a, CallArg::Num(_))) {
        return Vec::new();
    }
    c.args.iter().map(|a| if let CallArg::Num(e) = a { env.value(e, set) } else { 0 }).collect()
}

/// A `won` to count: the winning pass, each pass's size, the input's size.
type Won = (String, Vec<(String, usize)>, usize);

/// Counts `won` for the alternative pass (`linear_mba::ALTERNATIVES`, the origin of its
/// candidates) whose candidate `best` keeps; inside a `regions`, leaves it for that to count.
fn count_won(out: &[Cand], set: &[Cand], env: &Env) {
    let name = |c: &Cand| match linear_mba::ALTERNATIVES.iter().any(|(a, _)| *a == c.origin) {
        true => c.origin.clone(),
        false => String::new(),
    };
    let (Some(input), Some(kept)) = (set.first(), out.iter().min_by_key(|c| c.size())) else { return };
    let winner = name(kept);
    if winner.is_empty() {
        return;
    }
    let sizes: Vec<(String, usize)> = out.iter().map(|c| (name(c), c.size())).collect();
    let mut slot = env.deferred.borrow_mut();
    match slot.as_mut() {
        Some(s @ None) => *s = Some((winner, sizes, input.size())),
        _ => {
            let sizes: Vec<(&str, usize)> = sizes.iter().map(|(n, s)| (n.as_str(), *s)).collect();
            stats::won_among(&winner, &sizes, input.size(), kept.tree());
        }
    }
}

/// `p` on the term `t`, on the run `w` (no new scope), for `linear_mba::rewrite`: its main
/// candidate, or `t` when it gives none.
pub(crate) fn run_term(p: &Pipe, t: &Term, w: &Ctx) -> Term {
    run_on(p, t, w, false).map_or_else(|| t.clone(), Cand::into_tree)
}

/// `run_term` for `linear_mba::simba`, `None` when `p` gives no candidate; the `State::used`
/// bits of the candidate kept count for the run (`cofactor`: `Env::cofactor`).
pub(crate) fn run_alt(p: &Pipe, t: &Term, w: &Ctx, cofactor: bool) -> Option<Term> {
    let c = run_on(p, t, w, cofactor)?;
    w.swap_used(w.swap_used(0) | c.used);
    Some(c.into_tree())
}

fn run_on(p: &Pipe, t: &Term, w: &Ctx, cofactor: bool) -> Option<Cand> {
    let passes = crate::sched::current();
    let mut env = Env::with(None, &passes, w.w, w.signed, false, String::new(), "");
    env.cofactor = cofactor;
    env.ctxs.borrow_mut().push(w.narrow(w.w));
    let input = || Cand::of(t.clone(), &Cand::new("", "input"), 0, 0);
    let out = in_run(&passes, None, input, || scoped(|| go(p, vec![input()], &env)));
    out.inspect_err(fail).ok()?.into_iter().next()
}

/// `Passes::polish` of `p` on the egglog term `egg` at width `w` (`signed` as in
/// `linear_mba::Ctx`), and the origin of its result when that is smaller.
pub fn polish(egg: &str, w: u32, signed: Option<bool>, p: &Passes) -> (String, Option<String>) {
    let env = Env::prepass(p, w, signed, false, egg);
    let input = || Cand::new(egg, "input");
    in_run(p, None, input, || polish_one(&input(), &env)).map_or((egg.to_string(), None), |c| (c.term().to_string(), Some(c.origin)))
}

/// `Passes::polish` on `c` alone, as a run of its own (its registers, `smallest`, `wins`),
/// when it makes it smaller.
fn polish_one(c: &Cand, env: &Env) -> Option<Cand> {
    let run = Env::with(env.cli, env.passes, env.w, env.signed, env.trace, String::new(), c.term());
    let out = scoped(|| go(&env.passes.polish, vec![c.clone()], &run));
    out.inspect_err(fail).ok()?.into_iter().next().filter(|r| r.size() < c.size())
}

fn pre(e: &str) -> String {
    format!("pre/{}", stats::source_of(e).unwrap_or_else(|| "unlabeled".into()))
}

fn pass(p: &Pass, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    let name = match p {
        Pass::Save(r) => {
            env.lex.borrow().regs.borrow_mut().insert(r.to_string(), set.clone());
            return Ok(set);
        }
        Pass::Load(r) => return Ok(env.lex.borrow().regs.borrow().get(r).cloned().unwrap_or_default()),
        Pass::Off(ns) => {
            ns.iter().for_each(|n| crate::sched::turn_off(n));
            return Ok(set);
        }
        Pass::On(ns) => {
            ns.iter().for_each(|n| crate::sched::turn_on(n));
            return Ok(set);
        }
        Pass::Assign(i, v) => {
            let v = env.value(v, &set);
            match *i {
                crate::sched::DEADLINE => assign_time_limit(v),
                i if crate::sched::is_switch(i) => crate::sched::bind(i, (v != 0) as u64),
                i => match crate::sched::check_cap(i, v) {
                    Ok(v) => crate::sched::bind(i, v),
                    Err(e) => {
                        env.ctx(|c| c.mark_cut());
                        return Err(Error::BackendError(e));
                    }
                },
            }
            return Ok(set);
        }
        Pass::Term { name, at, alt } => return Ok(seen(dedup(term_pass(name, linear_mba::term_pass_at(*at), *alt, &set, env)), env)),
        Pass::Set(i) => SET_PASSES[*i],
        Pass::Egglog(name) => name.as_str(),
        Pass::Label(_) => "label/",
    };
    let Some(main) = set.first().cloned() else { return Ok(set) };
    let new = |term: String, origin: String| Cand::new(&term, &origin);
    let out = match name {
        "id" => return Ok(set),
        "none" => return Ok(Vec::new()),
        "within" => return Ok(if crate::sched::get(crate::sched::REWRITES) > 0 { set } else { Vec::new() }),
        "label/" => {
            let Pass::Label(r) = p else { unreachable!() };
            let first = env.reg_main(r);
            for c in set.iter().filter(|_| stats::on()) {
                if let Some(f) = first.as_ref().filter(|f| f.origin != c.origin) {
                    stats::add(&format!("pre/{}/differs", c.origin), 0.0);
                    stats::add_n(&format!("pre/{}/gain", c.origin), f.size().saturating_sub(c.size()) as u64, 0.0);
                }
                stats::label(&show(c.tree()), &c.origin);
            }
            if env.trace {
                let all: Vec<String> = set.iter().map(|c| format!("{} {}", c.origin, c.size())).collect();
                eprintln!("prepass: candidates: {}", all.join(", "));
            }
            return Ok(set);
        }
        "pre_done" => {
            if env.trace {
                let kept: Vec<String> = set.iter().map(|c| format!("{} {}", c.origin, c.size())).collect();
                eprintln!("prepass: input {} chosen {}", size_of(&env.lex.borrow().input), kept.join(", then "));
            }
            let t0 = env.reg_main("t0").unwrap_or_else(|| Cand::new(&env.lex.borrow().input, "input"));
            return Ok(set
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    stats::add(&format!("pre/{}/{}", c.origin, if i == 0 { "main" } else { "kept" }), 0.0);
                    let term = if i == 0 && c.same(&t0) { t0.term().to_string() } else { show(c.tree()) };
                    new(term, format!("pre/{}", c.origin))
                })
                .collect());
        }
        "prepass" => {
            let (alt, other) = env.prepass_of(main.term());
            std::iter::once(alt).chain(other).map(|e| new(e.clone(), pre(&e))).collect()
        }
        "take_minimal" => match proved_minimal(&set, env) {
            Some(c) => {
                stats::add("round/minimal", 0.0);
                vec![c.clone()]
            }
            None => set.clone(),
        },
        "polish" => set.iter().map(|c| polish_one(c, env).unwrap_or_else(|| c.clone())).collect(),
        "reprint" => {
            let cli = env.cli(name);
            let out = crate::egglog_to_infix(main.term(), &|n| crate::norm_const(n, &cli.num_type));
            vec![new(crate::infix_to_egglog(&out, true), main.origin.clone())]
        }
        _ if name == "egglog" || name.starts_with("egglog/") => {
            let cli = env.cli(name);
            if past_deadline(LAST_ROUND.with(|r| r.get()), env) {
                return Ok(set);
            }
            let roots: Vec<&str> = set.iter().map(Cand::term).collect();
            let clock = std::time::Instant::now();
            let e = crate::egglog_round(&env.egg, &roots, cli)?;
            LAST_ROUND.with(|r| r.set(clock.elapsed().as_secs_f64()));
            stats::add(name, stats::since(clock));
            if env.trace {
                eprintln!("{name}: root {} extracted {}", main.size(), size_of(&e));
            }
            let origin = match stats::source_of(&e) {
                Some(src) => format!("pre/{src}"),
                None => name.to_string(),
            };
            vec![new(e, origin)]
        }
        _ => panic!("unknown pass {name}"),
    };
    // A term a pass over the list gives back keeps the origin it came with.
    let out: Vec<Cand> = dedup(out)
        .into_iter()
        .map(|c| match set.iter().find(|s| s.same(&c)) {
            Some(s) => s.clone(),
            None => c,
        })
        .collect();
    Ok(seen(out, env))
}

/// The pass over one term `f` on each candidate of `set`, which keeps its own origin.
fn term_pass(name: &str, f: linear_mba::TermPass, alt: Option<u8>, set: &[Cand], env: &Env) -> Vec<Cand> {
    env.ctx(|ctx| {
        set.iter()
            .filter_map(|c| {
                let t = c.tree();
                let (outer, left) = (ctx.swap_used(0), crate::sched::get(crate::sched::REWRITES) as usize);
                let r: Option<Term> = match alt {
                    Some(_) => stats::try_pass(name, t, || f.run(t, ctx)),
                    None => stats::pass(name, t, || f.run(t, ctx)),
                };
                let used = ctx.swap_used(0);
                ctx.swap_used(outer | used);
                let made = left.saturating_sub(crate::sched::get(crate::sched::REWRITES) as usize);
                match (r, alt) {
                    (Some(r), Some(bit)) => Some(Cand { origin: name.to_string(), ..Cand::of(r, c, used | bit, made) }),
                    (None, Some(_)) => None,
                    (Some(r), None) if r != *t => Some(Cand::of(r, c, used, made)),
                    _ => Some(Cand { used: c.used | used, rewrites: c.rewrites + made, ..c.clone() }),
                }
            })
            .collect()
    })
}

/// `out`, after the smallest candidate each enclosing `smallest` saw is updated with it.
fn seen(out: Vec<Cand>, env: &Env) -> Vec<Cand> {
    for scope in env.seen.borrow_mut().iter_mut() {
        for c in &out {
            let n = c.size();
            if scope.as_ref().is_none_or(|(m, _)| n < *m) {
                *scope = Some((n, c.clone()));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pipe_lang as lang;

    #[test]
    fn time_limit_ends_with_its_sequence() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let limit = |ms| Pass::Assign(crate::sched::DEADLINE, Expr::Num(if ms > 0 { ms } else { NONE }));
        let wait = || std::thread::sleep(std::time::Duration::from_millis(5));
        crate::sched::in_default_run(|| {
            pass(&limit(1), vec![], &env).unwrap();
            wait();
            assert!(past_deadline(0.0, &env));
            scoped(|| {
                pass(&limit(0), vec![], &env).unwrap();
                assert!(past_deadline(0.0, &env), "a clear inside keeps the outer limit");
                pass(&limit(100_000), vec![], &env).unwrap();
                assert!(past_deadline(0.0, &env), "an inner limit is never later than the outer one");
            });
            assert!(past_deadline(0.0, &env));
            pass(&limit(0), vec![], &env).unwrap();
            assert!(!past_deadline(0.0, &env));
            pass(&limit(1), vec![], &env).unwrap();
        });
        wait();
        assert!(!past_deadline(0.0, &env), "a limit ends with its sequence");
        assert!(!cut());
    }

    #[test]
    fn off_ends_with_its_sequence() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&lang::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        crate::sched::in_default_run(|| {
            step("((off relate) | id)");
            assert!(!crate::sched::is_off("relate"), "a group ends its off");
            step("(rewrites = 8 | (off relate))");
            assert!(!crate::sched::is_off("relate"), "a sequence ends its off");
            step("(scope (off relate))");
            assert!(!crate::sched::is_off("relate"), "scope ends its off");
            step("(if 1 (off relate))");
            assert!(crate::sched::is_off("relate"), "a branch that is no sequence does not");
        });
        assert!(!crate::sched::is_off("relate"));
    }

    #[test]
    fn on_and_off_switches() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&lang::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        use crate::sched::{is_off, is_on};
        crate::sched::in_default_run(|| {
            step("(off relate tfunc)");
            assert!(is_off("relate") && is_off("tfunc"), "several names in one off");
            step("(on relate)");
            assert!(!is_off("relate") && is_off("tfunc"), "the later switch counts");
            let x = || Cand::new("(Var \"x\")", "input");
            assert!(in_run(&passes, None, x, || !is_off("relate") && is_off("tfunc")), "a run started here keeps them");
            crate::sched::with_off(&["relate"], || {
                assert!(is_off("relate"));
                step("(on relate)");
                assert!(!is_off("relate"));
            });
            assert!(!is_off("relate"));
            assert!(!is_on("cut"));
            step("(on cut)");
            assert!(is_on("cut"));
        });
        assert!(crate::sched::get(crate::sched::CUT) == crate::sched::NONE && !is_off("tfunc"));
    }

    #[test]
    fn assignments_bind_in_their_scope() {
        use crate::sched::{BIT_SPLIT_BUDGET, NONE, REWRITES, get, is_off, is_on};
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Sub (Var \"x\") (Var \"y\"))");
        let step = |p: &str| go(&lang::parse(p).unwrap(), vec![Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input")], &env).unwrap();
        crate::sched::in_default_run(|| {
            step("split_runs = vars * 3");
            assert_eq!(limit(Limit::SplitRuns), 6, "the right side is evaluated on the candidates");
            step("(split_runs = 1 | id)");
            assert_eq!(limit(Limit::SplitRuns), 6, "a group ends its assignment");
            step("relate = 0 | cut = 2");
            assert!(!is_off("relate") && !is_on("cut"), "a sequence ends its assignments");
            step("relate = 0");
            step("cut = 2");
            assert!(is_off("relate") && is_on("cut"), "a switch is on for any value but 0");
            step("rewrites = 5");
            step("rewrites = 9");
            assert_eq!(get(REWRITES), 9);
            step("rewrites = none");
            assert_eq!(get(REWRITES), NONE);
            step("(cand x (bit_split_budget = bit_split_budget + 1))");
            assert_eq!(get(BIT_SPLIT_BUDGET), NONE, "cand is a scope");
        });
        assert_eq!(get(crate::sched::var_index("split_runs").unwrap()), NONE);
        assert!(!is_off("relate") && get(crate::sched::CUT) == NONE);
    }

    #[test]
    fn run_settings_are_variables() {
        use crate::sched::{KEEP, NONE, RESTARTS, get, var_index};
        let passes = Passes::default();
        let x = "(Sub (Var \"x\") (Var \"y\"))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let input = || Cand::new(x, "input");
        let step = |p: &str| go(&lang::parse(p).unwrap(), vec![input()], &env).unwrap();
        let extra = var_index("extra").unwrap();
        in_run(&passes, None, input, || {
            assert_eq!((get(KEEP), get(extra), get(RESTARTS)), (2, 2, NONE), "a run without -m leaves restarts none");
            step("keep = 0 | extra = keep + 3 | (if (extra == 3 && keep == 1) (save ok)) | (load ok)");
            assert_eq!(get(extra), 2, "assignments end with their sequence");
            assert_eq!(step("keep = 0 | (best keep id (union id rewrite))").len(), 1, "keep reads as at least 1");
            step("extra = 0");
            assert_eq!(get(extra), 0);
            assert!(step("(if extra none)").len() == 1 && step("(if !extra none)").is_empty(), "a number variable holds where it is not 0");
            step("rerun_input = 0");
            assert!(step("(if rerun_input none)").len() == 1);
            assert!(step("(if (time_limit && prove_minimal) none)").is_empty(), "none holds");
        });
        assert_eq!(get(extra), NONE, "the entry bindings end with the run");
        let mut cli = Cli { max_restarts: 4, iter_limit: 7, ..Default::default() };
        let counts = |cli: &Cli| in_run(&cli.passes, Some(cli), input, || (get(RESTARTS), get(crate::sched::ITER_LIMIT), get(extra)));
        assert_eq!(counts(&cli), (4, 7, 2));
        cli.passes = Passes::parse("extra=9 restarts=restarts+1").unwrap();
        assert_eq!(counts(&cli), (5, 7, 9), "--passes items come after -m and -i");
        cli.passes = Passes::default();
        assert_eq!(counts(&cli), (4, 7, 2), "nothing leaks between runs");
    }

    #[test]
    fn restarts_less_one_counts_the_later_rounds() {
        let passes = Passes::default();
        let x = "(Var \"x\")";
        let env = Env::prepass(&passes, 32, None, false, x);
        let input = || Cand::new(x, "input");
        let Pipe::Fix(count, _) = lang::parse("(fix (restarts - 1) id)").unwrap() else { unreachable!() };
        let rounds = |m: usize| {
            let cli = Cli { max_restarts: m, ..Default::default() };
            in_run(&cli.passes, Some(&cli), input, || env.times(&count, &[input()]))
        };
        for m in [0, 1, 2, 5] {
            assert_eq!(rounds(m), m.max(1) - 1, "-m {m}: the later rounds, as when restarts read as -m less 1");
        }
    }

    #[test]
    fn a_limit_cuts_the_run_only_with_cut_on() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&lang::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        for on in [false, true] {
            start();
            crate::sched::in_default_run(|| {
                if on {
                    step("(on cut)");
                }
                step("time_limit = 1");
                std::thread::sleep(std::time::Duration::from_millis(5));
                step("rewrite");
            });
            assert_eq!(cut(), on);
        }
        start();
        assert!(!cut());
    }

    const SUB: &str = "(Sub (Or (Var \"x\") (Var \"y\")) (And (Var \"x\") (Var \"y\")))";
    const XOR: &str = "(Xor (Var \"x\") (Var \"y\"))";

    fn terms(set: &[Cand]) -> Vec<String> {
        set.iter().map(|c| c.term().to_string()).collect()
    }

    fn expr(s: &str) -> Expr {
        let Pipe::Filter(e) = lang::parse(&format!("(filter ({s}))")).unwrap() else { unreachable!() };
        e
    }

    #[test]
    fn retry_keeps_a_when_b_gives_none() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let step = |p: &str| terms(&go(&lang::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::sched::in_default_run(|| {
            assert_eq!(step("(retry 1 rewrite none)"), [XOR]);
            assert_eq!(step("(retry 1 id rewrite)"), [XOR], "b no larger is taken");
            assert_eq!(step("(retry 1 none rewrite)"), [XOR], "b is taken where a gives none");
            assert_eq!(step("(retry 0 id rewrite)"), [SUB]);
        });
    }

    #[test]
    fn polish_is_a_run_of_its_own() {
        let passes = Passes::parse("polish=rewrite | (save p) | none").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let step = |p: &str| terms(&go(&lang::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::sched::in_default_run(|| {
            assert_eq!(step("(save p) | polish | (load p)"), [SUB], "polish has its own registers");
            assert_eq!(step("(smallest polish)"), [SUB], "an outer smallest sees no candidate made inside polish");
            assert_eq!(step("(smallest rewrite | none | (load p))"), [XOR, SUB], "it sees those of the passes of its own run");
        });
    }

    #[test]
    fn def_is_a_run_of_its_own() {
        let passes = Passes::parse("(def (f) rewrite | (save p) | split_runs = 3 | (if (split_runs == 3) (load p) none)) (def (h) rewrite | none) (def (k) (if (split_runs == 5) id none))").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let mut names = lang::Defs::new();
        for d in &passes.defs {
            names.insert(d.name.clone(), lang::Named { pipe: crate::sched::Call::bare(d), flat: false, run: true, params: Vec::new(), def: Some(d.clone()) });
        }
        for item in ["(def @inline (g) rewrite | (save p) | split_runs = 3)", "(def @inline (h2) rewrite | none)"] {
            let d = lang::parse_definition(item, &names, &mut Vec::new()).unwrap();
            names.insert(d.name, lang::Named { pipe: d.pipe, flat: d.flat, run: false, params: Vec::new(), def: None });
        }
        let step = |p: &str| terms(&go(&lang::parse_with(p, &names, &mut Vec::new()).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::sched::in_default_run(|| {
            assert_eq!(step("f"), [XOR], "a def runs on the candidates, with its own assignments and registers");
            assert_eq!(step("(save p) | f | (load p)"), [SUB], "a def has its own registers");
            assert!(step("f | (if (split_runs == 3) (save s)) | (load s)").is_empty(), "an assignment in a def ends with its run");
            assert_eq!(step("split_runs = 5 | k"), [SUB], "a def reads the caller's bindings");
            assert_eq!(step("(save s) | (smallest h | (load s))"), [SUB], "an outer smallest sees no candidate made inside a def");
            assert_eq!(step("(save s) | (smallest f | none | (load s))"), [XOR, SUB], "it sees what the call gives");
            assert_eq!(step("(save p) | g | (load p)"), [XOR], "an @inline def shares the caller's registers");
            assert_eq!(step("g | (if (split_runs == 3) (save s)) | (load s)"), [XOR], "and its sequence: the assignment reaches the steps after it");
            assert_eq!(step("(save s) | (smallest h2 | (load s))"), [XOR, SUB], "and its smallest");
        });
    }

    /// The candidates `prepass` gives for `SUB` where `spec` defines it.
    fn prepass_of(spec: &str) -> Vec<Cand> {
        let passes = Passes::parse(spec).unwrap_or_else(|e| panic!("{spec}: {e}"));
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::sched::in_default_run(|| go(&passes.prepass, vec![Cand::new(SUB, "input")], &env).unwrap())
    }

    #[test]
    fn pipeline_arguments_are_closures() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let f = "(def (f p) (save t) | p | (union id (load t)))";
        assert_eq!(step(&format!("{f} prepass=(save t) | rewrite | (f (load t))")), [SUB, XOR], "the argument reads the caller's register, the body its own");
        assert_eq!(step("(def (f p) p | none) prepass=rewrite | (f (save s)) | (load s)"), [XOR], "and writes the caller's");
        let nested = "(def (g q) (save u) | none | q) (def (h p) (save u) | none | (g (union (load u) p)))";
        assert_eq!(step(&format!("{nested} prepass=(save t) | rewrite | (h (load t))")), [XOR, SUB], "a parameter in an argument is the enclosing call's argument");
        assert_eq!(step("(def (f r p) (save r) | p | (load r)) prepass=rewrite | (f t none)"), [XOR], "a name parameter as a register of the function's run");
        assert_eq!(step("(def (without n p) (off n) | p) prepass=(without tfunc tfunc)"), [SUB], "a name parameter as a switch");
        assert_eq!(step("prepass=tfunc"), [XOR]);
        let out = prepass_of("(def (named n p) (tag n p)) prepass=(named mine rewrite)");
        assert_eq!(out[0].origin, "mine", "a name parameter as a stats name");
        assert_eq!(step("(def @inline (g r p) (save r) | p) prepass=rewrite | (g s none) | (load s)"), [XOR], "an @inline function shares the caller's registers");
        assert_eq!(step("(def @inline (g p) split_runs = 3 | p) prepass=(g id) | (if (split_runs == 3) id none)"), [SUB], "and its sequence");
        assert_eq!(step("(def (g p) split_runs = 3 | p) prepass=(g id) | (if (split_runs == 3) id none)"), Vec::<String>::new(), "a def's assignment ends with its run");
        assert_eq!(step("(def (w p) (save s) | (smallest p | (load s))) prepass=(w rewrite)"), [XOR, SUB], "an argument's passes are seen by the smallest it runs in");
    }

    #[test]
    fn numeric_parameters() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let budget = "(def (with_budget n p) rewrites = n | p)";
        assert_eq!(step(&format!("{budget} prepass=(with_budget 0 rewrite)")), [SUB], "the argument limits the rewrites");
        assert_eq!(step(&format!("{budget} prepass=(with_budget 8 rewrite)")), [XOR]);
        assert_eq!(step(&format!("{budget} prepass=(with_budget none rewrite)")), [XOR], "none is an argument too");
        assert_eq!(step("(def (f n p) p | (filter (n == 7))) prepass=(f size rewrite)"), [XOR], "evaluated once at the call, on the caller's candidates");
        assert_eq!(step("(def @inline (f n p) p | (filter (n == 7))) prepass=(f size rewrite)"), [XOR], "also for an @inline function");
        assert_eq!(step("(def (f n p) (if (n == 9) p)) prepass=(f (size + 2) rewrite)"), [XOR], "arithmetic in an argument");
        assert_eq!(step("(def (f n p) (if (n == none) p)) prepass=(f (none - 1) rewrite)"), [XOR]);
        assert_eq!(step("(def (f n p) (fix n p)) (def (g m) (f (m - 1) rewrite)) prepass=(g 1)"), [SUB], "a parameter in an argument is read in the caller's frame");
        let closures = "(def (g m q) rewrite | (fix m q)) (def (h k r) (g (k + 1) r)) (def (f n) (h 5 (filter (n == 7))))";
        assert_eq!(step(&format!("{closures} prepass=(f size)")), [XOR], "an argument reads the frame of the function it is written in, through two calls");
        let shape = "(def (if_small k p) (if (size <= k) p)) (def (g q) (save u) | q | (union id (load u))) (def (f n) (if_small (n * 2) (g ((filter (size <= n)) | rewrite))))";
        assert_eq!(step(&format!("{shape} prepass=(f 7)")), [XOR, SUB]);
        assert_eq!(step(&format!("{shape} prepass=(f 3)")), [SUB], "k is 6, under the size");
        assert_eq!(step(&format!("{shape} prepass=(f 4)")), [SUB], "n is 4: the filter drops the input");
        let inline = "(def @inline (lim n p) split_runs = n | p)";
        assert_eq!(step(&format!("{inline} prepass=(lim 3 id) | (if (split_runs == 3) id none)")), [SUB], "an @inline body shares the caller's sequence");
        assert_eq!(step("(def @inline (hold n) (save s) | (filter (size == n))) prepass=rewrite | (hold 3) | (union id (load s))"), [XOR], "and its registers");
        assert_eq!(step("(def @inline (hold n) (save s) | (filter (size == n))) prepass=(hold 4) | (load s)"), [SUB]);
        assert_eq!(step("(def @inline (i m p) p | (filter (m == 1))) (def (f n) (i 1 (filter (n == 7)))) prepass=(f size)"), [SUB], "an argument of an @inline call reads the frame it is written in");
        let passes = Passes::parse("(def (f n) max_leaves = n | rewrite) prepass=(f 8)").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let e = crate::sched::in_default_run(|| go(&passes.prepass, vec![Cand::new(SUB, "input")], &env)).unwrap_err();
        assert!(e.to_string().contains("max_leaves is at most 6"), "{e}");
    }

    #[test]
    fn wins_zero_runs_nothing() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let step = |p: &str| terms(&go(&lang::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::sched::in_default_run(|| {
            assert_eq!(step("(wins 0 (smaller s rewrite))"), [SUB]);
            assert_eq!(step("(wins 0 none)"), [SUB]);
            assert_eq!(step("(wins 1 (smaller s rewrite))"), [XOR]);
        });
    }

    #[test]
    fn functions_give_zero_on_no_candidates() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::sched::in_default_run(|| {
            for f in ["size", "mul", "vars", "mixed", "input", "moved", "tiny", "(size r)", "(same r)", "(any 1)", "(all 1)"] {
                assert_eq!(env.value(&expr(f), &[]), 0, "{f}");
            }
            assert_eq!(env.value(&expr("!tiny"), &[]), 1);
            assert_eq!(env.value(&expr("size < (size r) + 1"), &[]), 1, "a comparison compares the zeros");
            assert_eq!(env.value(&expr("size > (size r)"), &[]), 0);
            let x = [Cand::new(SUB, "input")];
            assert_eq!(env.value(&expr("(size r)"), &x), 0, "an empty register");
            assert_eq!(env.value(&expr("size"), &x), 7);
            assert_eq!(env.value(&expr("split_runs"), &[]), 16, "a variable is read without candidates too");
        });
    }

    #[test]
    fn conditions_are_numbers() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let x = [Cand::new(SUB, "input")];
        let mul = [Cand::new("(Mul (Var \"x\") (Mul (Var \"x\") (Var \"y\")))", "input")];
        crate::sched::in_default_run(|| {
            let v = |s: &str, set: &[Cand]| env.value(&expr(s), set);
            assert_eq!(v("mul", &mul), 2);
            assert_eq!(v("(mul >= 1) + (vars == 2) * 4", &mul), 5);
            assert_eq!(v("!3", &x), 0);
            assert_eq!(v("!!3", &x), 1);
            assert_eq!(v("2 && 5", &x), 1);
            assert_eq!(v("0 || 7", &x), 1);
            assert_eq!(v("vars * (mixed || 1)", &x), 2);
            let step = |p: &str, set: &[Cand]| go(&lang::parse(p).unwrap(), set.to_vec(), &env).unwrap().len();
            assert_eq!(step("(if mul none)", &mul), 0, "a number holds where it is not 0");
            assert_eq!(step("(if mul none)", &x), 1);
            assert_eq!(step("(fix (mul < 1) rewrite) | (filter (size == 5))", &x), 0, "a comparison counts as 1");
        });
    }

    #[test]
    fn none_in_arithmetic() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::sched::in_default_run(|| {
            let v = |s: &str| env.value(&expr(s), &[]);
            for (e, want) in [
                ("none + 1", NONE),
                ("1 + none", NONE),
                ("none * 0", NONE),
                ("none - 1", NONE),
                ("0 - none", 0),
                ("none - none", 0),
                ("3 - 5", 0),
                ("7 / 2", 3),
                ("5 / 0", NONE),
                ("5 / none", 0),
                ("none / 2", NONE),
                ("18446744073709551614 + 1", NONE),
                ("4294967296 * 4294967296", NONE),
                ("none > 18446744073709551614", 1),
                ("none == none", 1),
                ("none != split_runs", 1),
                ("rewrites", NONE),
                ("rewrites == none", 1),
                ("!none", 0),
            ] {
                assert_eq!(v(e), want, "{e}");
            }
            assert_eq!(env.times(&expr("none"), &[]), usize::MAX, "none as a count is no limit");
        });
    }

    #[test]
    fn bookkeeping_matches_the_attribute() {
        for s in crate::builtins::all().iter().filter(|s| !s.is_number()) {
            let call = crate::builtins::sample(s);
            assert_eq!(bookkeeping(&lang::parse(&call).unwrap()), s.bookkeeping, "{}", s.decl());
        }
    }

    #[test]
    fn time_limit_skips_work_but_not_bookkeeping() {
        let passes = Passes::default();
        let x = "(Sub (Or (Var \"x\") (Var \"y\")) (And (Var \"x\") (Var \"y\")))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let step = |p: &str, set: Vec<Cand>| -> Vec<String> {
            go(&lang::parse(p).unwrap(), set, &env).unwrap().iter().map(|c| c.term().to_string()).collect()
        };
        let input = || vec![Cand::new(x, "input")];
        crate::sched::in_default_run(|| {
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"]);
            step("(save t)", input());
            step("time_limit = 1", input());
            std::thread::sleep(std::time::Duration::from_millis(5));
            assert_eq!(step("rewrite", input()), [x], "work past the limit is skipped");
            assert_eq!(step("(load t) | (filter 1)", vec![]), [x], "bookkeeping still runs");
            assert_eq!(step("time_limit = none | rewrite", input()), [x], "a clear restores the limit outside its sequence");
            step("time_limit = none", input());
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"], "a clear lets the rest run");
        });
    }
}
