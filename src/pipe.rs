//! Runs a `sched::Pipe`. Every pass maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another: a pass over one term (`linear_mba::TERM_PASSES`, the
//! polish passes as `polish/NAME`) runs on each candidate and replaces it by its result; the
//! other passes take the list whole.

use crate::eval::{Op, Term, parse, show, size};
use crate::linear_mba::{CLUSTERED, Ctx, WIDE};
use crate::sched::{Cond, Limit, Passes, Pipe, limit};
use crate::{Cli, Error, linear_mba, minimal, stats, width_of};
use std::cell::{Cell, OnceCell, RefCell};
use std::rc::Rc;
use std::collections::HashMap;

/// Passes that take the candidate list whole, besides `save/R`, `load/R` and `label/R`.
const SET_PASSES: [&str; 10] = [
    // The candidates unchanged.
    "id",
    // No candidates.
    "none",
    // The main candidate's pre-pass rebuilds: the main one, then those to union with it.
    "prepass",
    // One egglog round on all candidates unioned: its extraction (`egglog/LABEL` times it
    // as `egglog/LABEL`).
    "egglog",
    // The first candidate proved minimal (`minimal`).
    "take_minimal",
    // The polish passes of `Passes::polish` on each candidate, kept when smaller.
    "polish",
    // The main candidate printed and read back.
    "reprint",
    // Turns off the `sched::GATES` the main candidate does not need (`sched::set_gates`).
    "gates",
    // No candidates once `rewrite` has used up its calls in the enclosing `with`.
    "within",
    // The end of the pre-pass: counts the kept candidates, names their origins `pre/NAME`
    // and gives the main one as the input was written when it equals it (register `t0`).
    "pre_done",
];

/// The conditions of `if`, `retry` and `filter`, on the candidates they see; also `lt:R`,
/// `gt:R` (main candidate smaller, larger than register `R`'s), `eq:R` (equal),
/// `le:P/Q:R` (at most `P/Q` its size).
pub const CONDS: [&str; 16] = [
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
    // Always.
    "true",
];

/// The names a `fix` or `best` count can take: `restarts` (`Cli::max_restarts` less the
/// first round), `extra` (`Passes::extra`), `printed` (`Passes::printed` less the first
/// round), `keep` (`Passes::keep`).
pub const COUNTS: [&str; 4] = ["restarts", "extra", "printed", "keep"];

const REGISTER_PASSES: [&str; 3] = ["save/", "load/", "label/"];

/// The names a `Pipe::Pass` can take, registers written `R`.
pub fn names() -> Vec<String> {
    let polish = linear_mba::POLISH.iter().map(|(n, _)| format!("polish/{n}"));
    let egglog = ["first", "later", "rerun_input"].iter().map(|l| format!("egglog/{l}"));
    let regs = REGISTER_PASSES.iter().map(|p| format!("{p}R"));
    SET_PASSES.iter().map(|n| n.to_string()).chain(egglog).chain(regs).chain(linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string())).chain(polish).collect()
}

/// Whether `name` is a pass.
pub fn is_pass(name: &str) -> bool {
    REGISTER_PASSES.iter().any(|p| name.strip_prefix(p).is_some_and(|r| !r.is_empty())) || name.starts_with("egglog/") || names().iter().any(|n| n == name)
}

/// Whether `name` is a condition.
pub fn is_cond(name: &str) -> bool {
    if CONDS.contains(&name) {
        return true;
    }
    match name.split(':').collect::<Vec<_>>().as_slice() {
        ["lt" | "gt" | "eq", r] => !r.is_empty(),
        ["le", pq, r] => !r.is_empty() && pq.split_once('/').is_some_and(|(p, q)| p.parse::<usize>().is_ok() && q.parse::<usize>().is_ok_and(|q| q > 0)),
        _ => false,
    }
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
    trace: bool,
    /// The egglog program of the numeric type.
    egg: String,
    /// The input of the run.
    input: String,
    moved: Cell<bool>,
    /// The smallest candidate each enclosing `smallest` saw, innermost last.
    seen: RefCell<Vec<Option<(usize, Cand)>>>,
    regs: RefCell<HashMap<String, Vec<Cand>>>,
    /// The runs of the enclosing `scope`s, innermost last.
    ctxs: RefCell<Vec<Ctx>>,
}

impl<'a> Env<'a> {
    pub fn new(cli: &'a Cli, egg: String, input: &str) -> Env<'a> {
        Env::with(Some(cli), &cli.passes, width_of(&cli.num_type), cli.trace, egg, input)
    }

    /// A pre-pass run on `input` at width `w`.
    pub fn prepass(p: &'a Passes, w: u32, trace: bool, input: &str) -> Env<'a> {
        Env::with(None, p, w, trace, String::new(), input)
    }

    fn with(cli: Option<&'a Cli>, passes: &'a Passes, w: u32, trace: bool, egg: String, input: &str) -> Env<'a> {
        let input = input.to_string();
        Env { cli, passes, w, trace, egg, input, moved: Cell::new(false), seen: Default::default(), regs: Default::default(), ctxs: Default::default() }
    }

    fn cli(&self, pass: &str) -> &'a Cli {
        self.cli.unwrap_or_else(|| panic!("{pass} needs a simplify run"))
    }

    fn prepass_of(&self, s: &str) -> (String, Vec<String>) {
        linear_mba::simplify_linear_with(s, self.w, self.trace, self.passes)
    }

    /// `f` on the run of the innermost `scope`, or on a fresh one.
    fn ctx<R>(&self, f: impl FnOnce(&Ctx) -> R) -> R {
        match self.ctxs.borrow().last() {
            Some(c) => f(c),
            None => f(&Ctx::new(self.w)),
        }
    }

    fn reg_main(&self, r: &str) -> Option<Cand> {
        self.regs.borrow().get(r).and_then(|s| s.first().cloned())
    }

    fn count(&self, n: &str) -> usize {
        let p = self.passes;
        match n {
            "restarts" => self.cli("restarts").max_restarts.max(1) - 1,
            "extra" => p.extra,
            "printed" => p.printed.saturating_sub(1),
            "keep" => p.keep,
            _ => n.parse().unwrap(),
        }
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

fn cond(name: &str, set: &[Cand], env: &Env) -> bool {
    let Some(main) = set.first() else { return false };
    let p = env.passes;
    let reg = |r: &str, f: &dyn Fn(&Cand) -> bool| env.reg_main(r).is_some_and(|c| f(&c));
    match name.split(':').collect::<Vec<_>>().as_slice() {
        ["lt", r] => return reg(r, &|c| main.size() < c.size()),
        ["gt", r] => return reg(r, &|c| main.size() > c.size()),
        ["eq", r] => return reg(r, &|c| c.same(main)),
        ["le", pq, r] => {
            let (a, b) = pq.split_once('/').unwrap();
            let (a, b): (usize, usize) = (a.parse().unwrap(), b.parse().unwrap());
            return reg(r, &|c| b * main.size() <= a * c.size());
        }
        _ => {}
    }
    match name {
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
        _ => unreachable!("condition {name}"),
    }
}

fn holds(c: &Cond, set: &[Cand], env: &Env) -> bool {
    c.0.iter().any(|alt| alt.iter().all(|(neg, name)| cond(name, set, env) != *neg))
}

/// The candidates `p` gives for `set`.
pub fn run(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    crate::sched::apply(env.passes);
    go(p, set, env)
}

fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    match p {
        Pipe::Pass(name) => pass(name, set, env),
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
            let mut out = dedup(out);
            out.sort_by_cached_key(|c| c.size());
            out.truncate(env.count(k).max(1));
            Ok(out)
        }
        Pipe::First(ps) => {
            for p in ps {
                let out = go(p, set.clone(), env)?;
                if out != set {
                    return Ok(out);
                }
            }
            Ok(set)
        }
        Pipe::Fix(n, p) => {
            let mut set = set;
            for _ in 0..env.count(n) {
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
            env.ctxs.borrow_mut().push(Ctx::new(env.w));
            let out = go(p, set, env);
            env.ctxs.borrow_mut().pop();
            out
        }
    }
}

fn pre(e: &str) -> String {
    format!("pre/{}", stats::source_of(e).unwrap_or_else(|| "unlabeled".into()))
}

fn pass(name: &str, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    if let Some(r) = name.strip_prefix("save/") {
        env.regs.borrow_mut().insert(r.to_string(), set.clone());
        return Ok(set);
    }
    if let Some(r) = name.strip_prefix("load/") {
        return Ok(env.regs.borrow().get(r).cloned().unwrap_or_default());
    }
    let Some(main) = set.first().cloned() else { return Ok(set) };
    let w = env.w;
    let p = env.passes;
    let new = |term: String, origin: String| Cand::new(&term, &origin);
    let out = match name {
        "id" => return Ok(set),
        "none" => return Ok(Vec::new()),
        "within" => return Ok(if env.ctx(|c| c.setting("rewrites").unwrap()) > 0 { set } else { Vec::new() }),
        "gates" => {
            crate::sched::apply(p);
            crate::sched::set_gates(p, &stats::shape(main.tree()));
            return Ok(set);
        }
        _ if name.starts_with("label/") => {
            let first = env.reg_main(&name["label/".len()..]);
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
        "polish" => set
            .iter()
            .map(|c| match linear_mba::polish_with(c.term(), w, p) {
                (out, used) if !used.is_empty() && size_of(&out) < c.size() => {
                    if env.trace {
                        eprintln!("polish: {} -> {} by {}", c.size(), size_of(&out), used.join(","));
                    }
                    new(out, format!("polish/{}", used.last().unwrap()))
                }
                _ => c.clone(),
            })
            .collect(),
        "reprint" => {
            let cli = env.cli(name);
            let out = crate::egglog_to_infix(main.term(), &|n| crate::norm_const(n, &cli.num_type));
            vec![new(crate::infix_to_egglog(&out, true), main.origin.clone())]
        }
        _ if name == "egglog" || name.starts_with("egglog/") => {
            let cli = env.cli(name);
            let roots: Vec<&str> = set.iter().map(Cand::term).collect();
            let clock = std::time::Instant::now();
            let e = crate::egglog_round(&env.egg, &roots, cli)?;
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
        _ => {
            let f = linear_mba::term_pass(name).unwrap_or_else(|| panic!("unknown pass {name}"));
            env.ctx(|ctx| {
                set.iter()
                    .map(|c| {
                        let t = c.tree();
                        let (outer, left) = (ctx.swap_used(0), ctx.setting("rewrites").unwrap());
                        let r: Option<Term> = stats::pass(name, t, || f(t, ctx));
                        let used = ctx.swap_used(0);
                        ctx.swap_used(outer | used);
                        let made = left.saturating_sub(ctx.setting("rewrites").unwrap());
                        match r {
                            Some(r) if r != *t => Cand::of(r, c, used, made),
                            _ => Cand { used: c.used | used, rewrites: c.rewrites + made, ..c.clone() },
                        }
                    })
                    .collect()
            })
        }
    };
    // A term a pass over the list gives back keeps the origin it came with; passes over one
    // term keep each candidate's own.
    let by_term = linear_mba::term_pass(name).is_some();
    let out: Vec<Cand> = dedup(out)
        .into_iter()
        .map(|c| match set.iter().find(|s| !by_term && s.same(&c)) {
            Some(s) => s.clone(),
            None => c,
        })
        .collect();
    for scope in env.seen.borrow_mut().iter_mut() {
        for c in &out {
            let n = c.size();
            if scope.as_ref().is_none_or(|(m, _)| n < *m) {
                *scope = Some((n, c.clone()));
            }
        }
    }
    Ok(out)
}
