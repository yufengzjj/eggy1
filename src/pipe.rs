//! Runs a `sched::Pipe`. Every pass maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another: a pass over one term (`linear_mba::TERM_PASSES`, the
//! polish passes as `polish/NAME`) runs on each candidate and replaces it by its result; the
//! other passes take the list whole.

use crate::eval::{Op, Term, parse, show, size};
use crate::linear_mba::{CLUSTERED, Ctx, WIDE};
use crate::sched::{Cond, Limit, Pass, Passes, Pipe, TermAt, Value, limit};
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
    // No candidates once `rewrite` has used up its calls in the enclosing `with`.
    "within",
    // The end of the pre-pass: counts the kept candidates, names their origins `pre/NAME`
    // and gives the main one as the input was written when it equals it (register `t0`).
    "pre_done",
];

/// The named conditions of `if`, `retry` and `filter`, on the candidates they see; the
/// others (`(same R)`, comparisons) are `sched::Cond` forms.
pub const CONDS: [&str; 20] = [
    // The main candidate has a shift, division or mulhi and its rebuild is not tiny.
    "opaque",
    // A candidate is proved minimal: no smaller term equals it (`Passes::minimal`).
    "minimal",
    // The main candidate has arithmetic or a constant directly under a bitwise operation.
    "mixed",
    // The pre-pass changes the main candidate.
    "rebuilds",
    // The last `fix` stopped at its count, the main candidate still changing.
    "moved",
    // The main candidate is the input of `simplify`.
    "input",
    // `Passes::rerun_input`.
    "rerun_input",
    // `Passes::printed` is not 0.
    "printed",
    // The main candidate has at most `linear_mba::TINY` nodes.
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
    // Always, when there are candidates (as every condition).
    "true",
    // The main candidate is a linear region without leaves.
    "no_leaves",
    // The main candidate is a linear region of more than `linear_mba::MAX_LEAVES` leaves.
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

/// The names a `fix` or `best` count can take: `restarts` (`Cli::max_restarts` less the
/// first round), `extra` (`Passes::extra`), `printed` (`Passes::printed` less the first
/// round), `keep` (`Passes::keep`).
pub const COUNTS: [&str; 4] = ["restarts", "extra", "printed", "keep"];

/// The passes as a pipeline writes them, for error messages.
pub fn names() -> Vec<String> {
    let polish = linear_mba::POLISH.iter().map(|(n, _)| format!("polish/{n}"));
    let forms = ["(egglog LABEL)", "(save R)", "(load R)", "(label R)", "(off NAME)"].map(String::from);
    SET_PASSES.iter().map(|n| n.to_string()).chain(forms).chain(linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string())).chain(polish).collect()
}

/// The internal names of the passes a pipeline writes as forms: `(save R)` is `save/R`.
pub const FORM_PASSES: [&str; 5] = ["save", "load", "label", "egglog", "off"];

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
        return crate::sched::INNER.iter().find(|k| **k == n).map(|k| Pass::Off(*k));
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
    egg: String,
    /// The input of the run.
    input: String,
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
    regs: RefCell<HashMap<String, Vec<Cand>>>,
    /// The runs of the enclosing `scope`s, innermost last.
    ctxs: RefCell<Vec<Ctx>>,
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
        let input = input.to_string();
        Env { cli, passes, w, signed, trace, egg, input, moved: Cell::new(false), wins: Cell::new(0), deferred: Default::default(), cofactor: false, seen: Default::default(), regs: Default::default(), ctxs: Default::default() }
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
        self.regs.borrow().get(r).and_then(|s| s.first().cloned())
    }

    fn count(&self, i: usize) -> usize {
        let p = self.passes;
        match COUNTS[i] {
            "restarts" => self.cli("restarts").max_restarts.max(1) - 1,
            "extra" => p.extra,
            "printed" => p.printed.saturating_sub(1),
            "keep" => p.keep,
            n => unreachable!("count {n}"),
        }
    }

    /// `v` for the candidates `set`; `None` where it reads a candidate or register that is
    /// not there, or divides by 0.
    fn value(&self, v: &Value, set: &[Cand]) -> Option<u64> {
        Some(match v {
            Value::Num(n) => *n,
            Value::Count(i) => self.count(*i) as u64,
            Value::Feature(0) => set.first()?.size() as u64,
            Value::Feature(i) => feature(&stats::shape(set.first()?.tree()), *i) as u64,
            Value::Size(r) => self.reg_main(r)?.size() as u64,
            Value::Limit(i) => crate::sched::limit_named(crate::sched::LIMITS[*i].0).unwrap() as u64,
            Value::Bin(op, a, b) => {
                let (a, b) = (self.value(a, set)?, self.value(b, set)?);
                match op {
                    '+' => a.wrapping_add(b),
                    '-' => a.saturating_sub(b),
                    '*' => a.wrapping_mul(b),
                    _ => a.checked_div(b)?,
                }
            }
        })
    }

    /// `v` as a count: 0 where it has no value.
    fn times(&self, v: &Value, set: &[Cand]) -> usize {
        self.value(v, set).unwrap_or(0) as usize
    }}

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
    if !cli.passes.minimal {
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
    let p = env.passes;
    match CONDS[i] {
        "opaque" => opaque(main.tree()) && size_of(&env.prepass_of(main.term()).0) > linear_mba::TINY,
        "minimal" => proved_minimal(set, env).is_some(),
        "mixed" => crate::mixed(main.tree()),
        "rebuilds" => env.prepass_of(main.term()).0 != main.term(),
        "moved" => env.moved.get(),
        "input" => main.term() == env.input,
        "rerun_input" => p.rerun_input,
        "printed" => p.printed > 0,
        "tiny" => main.size() <= linear_mba::TINY,
        "fits_split" => main.size() <= limit(Limit::SplitSize),
        "used_wide" => set.iter().any(|c| c.used & WIDE != 0),
        "used_clustered" => set.iter().any(|c| c.used & CLUSTERED != 0),
        "few_rewrites" => main.rewrites <= limit(Limit::UnclusteredAfter),
        "replaceable" => env.ctx(|c| crate::tfunc::replacement(main.tree(), c).is_some()),
        "abstracted" => linear_mba::ABSTRACTED.contains(&main.origin.as_str()),
        "true" => true,
        "no_leaves" => env.ctx(|w| linear_mba::leaf_count(main.tree(), w) == 0),
        "wide" => env.ctx(|w| linear_mba::leaf_count(main.tree(), w) > linear_mba::MAX_LEAVES),
        "const_bitwise" => env.ctx(|w| linear_mba::const_bitwise(main.tree(), w)),
        "cofactor" => env.cofactor,
        name => unreachable!("condition {name}"),
    }
}

fn holds(c: &Cond, set: &[Cand], env: &Env) -> bool {
    match c {
        Cond::Is(i) => cond(*i, set, env),
        Cond::Same(r) => set.first().zip(env.reg_main(r)).is_some_and(|(m, c)| c.same(m)),
        Cond::Not(c) => !holds(c, set, env),
        Cond::And(cs) => cs.iter().all(|c| holds(c, set, env)),
        Cond::Or(cs) => cs.iter().any(|c| holds(c, set, env)),
        Cond::Cmp(op, a, b) => !set.is_empty() && env.value(a, set).zip(env.value(b, set)).is_some_and(|(a, b)| op.holds(a, b)),
        Cond::Any(c) => set.iter().any(|x| holds(c, std::slice::from_ref(x), env)),
        Cond::All(c) => !set.is_empty() && set.iter().all(|x| holds(c, std::slice::from_ref(x), env)),
    }
}

thread_local! {
    /// When `go` stops starting passes (`Cli::time_limit`).
    static DEADLINE: Cell<Option<std::time::Instant>> = const { Cell::new(None) };
    /// Some pass was skipped at the deadline.
    static CUT: Cell<bool> = const { Cell::new(false) };
    /// Seconds the last egglog round took.
    static LAST_ROUND: Cell<f64> = const { Cell::new(0.0) };
}

/// Starts the time limit of a run on this thread (`None`: no limit).
pub fn set_deadline(seconds: Option<f64>) {
    let at = seconds.map(|s| std::time::Instant::now() + std::time::Duration::from_secs_f64(s.max(0.0)));
    DEADLINE.with(|d| d.set(at));
    CUT.with(|c| c.set(false));
    LAST_ROUND.with(|r| r.set(0.0));
}

/// Whether a pass was skipped at the deadline since `set_deadline`.
pub fn cut() -> bool {
    CUT.with(|c| c.get())
}

/// Whether work taking `secs` more would end past the deadline; records the cut when it
/// would. Results computed then are not memoized (`Ctx::mark_cut`).
fn past_deadline(secs: f64, env: &Env) -> bool {
    let Some(at) = DEADLINE.with(|d| d.get()) else { return false };
    if std::time::Instant::now() + std::time::Duration::from_secs_f64(secs) < at {
        return false;
    }
    CUT.with(|c| c.set(true));
    env.ctx(|c| c.mark_cut());
    true
}

/// The candidates `p` gives for `set`.
pub fn run(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    crate::sched::apply(env.passes);
    go(p, set, env)
}

fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    // Every candidate equals the input, so stopping anywhere keeps the result right.
    if past_deadline(0.0, env) {
        return Ok(set);
    }
    match p {
        Pipe::Pass(p) => pass(p, set, env),
        Pipe::Seq(ps) => ps.iter().try_fold(set, |s, p| go(p, s, env)),
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
        Pipe::Off(names, p) => crate::sched::with_off(names, || go(p, set, env)),
        Pipe::If(c, a, b) => go(if holds(c, &set, env) { a } else { b }, set, env),
        Pipe::Retry(c, a, b) => {
            let out = go(a, set.clone(), env)?;
            if !holds(c, &out, env) {
                return Ok(out);
            }
            let again = go(b, set, env)?;
            let n = |s: &[Cand]| s.first().map(Cand::size);
            Ok(if n(&again) <= n(&out) { again } else { out })
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
        Pipe::Filter(c) => Ok(set.into_iter().filter(|x| holds(c, std::slice::from_ref(x), env)).collect()),
        Pipe::Cand(name, p) => {
            if crate::sched::PRE.contains(&name.as_str()) && !env.passes.pre_on(name) {
                return Ok(Vec::new());
            }
            let clock = std::time::Instant::now();
            let budget = Pipe::With(vec![("bit_splits".into(), "bit_split_budget".into())], p.clone());
            let out = go(&budget, set, env)?;
            stats::add(&format!("pre/{name}/made"), stats::since(clock));
            Ok(out.into_iter().map(|c| Cand { origin: name.clone(), ..c }).collect())
        }
        Pipe::With(kv, p) => {
            let value = |v: &str| v.parse().unwrap_or_else(|_| crate::sched::limit_named(v).unwrap());
            let old: Vec<(&str, usize, usize)> = env.ctx(|c| {
                kv.iter()
                    .map(|(k, v)| {
                        let (was, now) = (c.setting(k).unwrap(), value(v));
                        c.set_setting(k, now);
                        (k.as_str(), was, now)
                    })
                    .collect()
            });
            let out = go(p, set, env);
            env.ctx(|c| {
                for (k, was, set) in old {
                    // The calls made inside count against the calls left outside.
                    let back = if k == "rewrites" { was.saturating_sub(set - c.setting(k).unwrap()) } else { was };
                    c.set_setting(k, back);
                }
            });
            out
        }
        Pipe::Scope(p) => {
            env.ctxs.borrow_mut().push(Ctx::typed(env.w, env.signed));
            let out = go(p, set, env);
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
        Pipe::Wins(n, p) => {
            let (n, outer) = (env.times(n, &set), env.wins.replace(0));
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
    let out = go(p, vec![Cand::of(t.clone(), &Cand::new("", "input"), 0, 0)], &env).expect("a rewrite runs no egglog");
    out.into_iter().next()
}

/// `Passes::polish` of `p` on the egglog term `egg` at width `w` (`signed` as in
/// `linear_mba::Ctx`), and the origin of its result when that is smaller.
pub fn polish(egg: &str, w: u32, signed: Option<bool>, p: &Passes) -> (String, Option<String>) {
    let env = Env::prepass(p, w, signed, false, egg);
    polish_one(&Cand::new(egg, "input"), &env).map_or((egg.to_string(), None), |c| (c.term().to_string(), Some(c.origin)))
}

/// `Passes::polish` on `c` alone, when it makes it smaller.
fn polish_one(c: &Cand, env: &Env) -> Option<Cand> {
    crate::sched::apply(env.passes);
    let out = go(&env.passes.polish, vec![c.clone()], env).expect("polish runs no egglog");
    out.into_iter().next().filter(|r| r.size() < c.size())
}

fn pre(e: &str) -> String {
    format!("pre/{}", stats::source_of(e).unwrap_or_else(|| "unlabeled".into()))
}

fn pass(p: &Pass, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    let name = match p {
        Pass::Save(r) => {
            env.regs.borrow_mut().insert(r.to_string(), set.clone());
            return Ok(set);
        }
        Pass::Load(r) => return Ok(env.regs.borrow().get(r).cloned().unwrap_or_default()),
        Pass::Off(n) => {
            crate::sched::turn_off(n);
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
        "within" => return Ok(if env.ctx(|c| c.setting("rewrites").unwrap()) > 0 { set } else { Vec::new() }),
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
                eprintln!("prepass: input {} chosen {}", size_of(&env.input), kept.join(", then "));
            }
            let t0 = env.reg_main("t0").unwrap_or_else(|| Cand::new(&env.input, "input"));
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
                let (outer, left) = (ctx.swap_used(0), ctx.setting("rewrites").unwrap());
                let r: Option<Term> = match alt {
                    Some(_) => stats::try_pass(name, t, || f.run(t, ctx)),
                    None => stats::pass(name, t, || f.run(t, ctx)),
                };
                let used = ctx.swap_used(0);
                ctx.swap_used(outer | used);
                let made = left.saturating_sub(ctx.setting("rewrites").unwrap());
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
