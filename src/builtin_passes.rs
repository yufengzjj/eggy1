//! The built-in functions of the pipeline language that run the passes of the simplification:
//! the passes over one term, the pre-pass, egglog rounds, polish, the conditions on candidates,
//! and the combinators that count stats or need a `linear_mba::Ctx`.

use crate::{Cli, linear_mba, minimal, stats, width_of};
use crate::cand::Cand;
use crate::eval::{Op, Term, parse, show, size};
use crate::lang::ast::Pipe;
use crate::lang::builtins::{Impl, name};
use crate::lang::eval::{Env, Steps, fail, go, in_run, kept, past, scoped};
use crate::linear_mba::{CLUSTERED, Ctx, WIDE};
use crate::passes::Passes;
use crate::rust_vars::{Limit, limit};
use std::cell::Cell;

/// The Rust code of the built-in function `name` that the simplification implements: `IMPLS`,
/// the passes over one term, or the polish passes (`polish_NAME`).
pub(crate) fn implementation(name: &str) -> Option<Impl> {
    if let Some((_, imp)) = IMPLS.iter().find(|(n, _)| *n == name) {
        return Some(*imp);
    }
    if let Some((_, f)) = linear_mba::TERM_PASSES.iter().find(|(n, _)| *n == name) {
        return Some(match linear_mba::ALTERNATIVES.iter().find(|(a, _)| *a == name) {
            Some((_, bit)) => Impl::Alt(*f, *bit),
            None => Impl::Each(*f),
        });
    }
    let (_, f) = linear_mba::POLISH.iter().find(|(n, _)| name.strip_prefix("polish_") == Some(n))?;
    Some(Impl::Polish(*f))
}

/// The built-in functions the simplification implements other than the passes over one term,
/// by name.
pub(crate) const IMPLS: &[(&str, Impl)] = &[
    ("scope", Impl::Group(scope)),
    ("regions", Impl::Group(regions)),
    ("again", Impl::Group(again)),
    ("tag", Impl::Group(tag)),
    ("origin", Impl::Group(origin)),
    ("smaller", Impl::Group(smaller)),
    ("label", Impl::Group(label)),
    ("prepass", Impl::Main(prepass)),
    ("egglog", Impl::Group(egglog)),
    ("take_minimal", Impl::Group(take_minimal)),
    ("polish", Impl::EachCand(polish_one)),
    ("reprint", Impl::Main(reprint)),
    ("within", Impl::Group(|_, set, _| Ok(if crate::lang::vars::get(crate::rust_vars::REWRITES) > 0 { set } else { Vec::new() }))),
    ("pre_done", Impl::Group(pre_done)),
    ("size", Impl::TermNum(|m, _| m.size() as u64)),
    ("vars", Impl::TermNum(|m, _| stats::shape(m.tree()).vars as u64)),
    ("depth", Impl::TermNum(|m, _| stats::shape(m.tree()).depth as u64)),
    ("mul", Impl::TermNum(|m, _| stats::shape(m.tree()).mul as u64)),
    ("bitconst", Impl::TermNum(|m, _| stats::shape(m.tree()).bitconst as u64)),
    ("arith_in_bit", Impl::TermNum(|m, _| stats::shape(m.tree()).arith_in_bit as u64)),
    ("shift", Impl::TermNum(|m, _| stats::shape(m.tree()).shift as u64)),
    ("div", Impl::TermNum(|m, _| stats::shape(m.tree()).div as u64)),
    ("opaque", Impl::TermNum(|m, env| (opaque(m.tree()) && size_of(&env.prepass_of(m.term()).0) > limit(Limit::TinySize)) as u64)),
    ("minimal", Impl::GroupNum(|set, env| proved_minimal(set, env).is_some() as u64)),
    ("mixed", Impl::TermNum(|m, _| crate::mixed(m.tree()) as u64)),
    ("rebuilds", Impl::TermNum(|m, env| (env.prepass_of(m.term()).0 != m.term()) as u64)),
    ("tiny", Impl::TermNum(|m, _| (m.size() <= limit(Limit::TinySize)) as u64)),
    ("fits_split", Impl::TermNum(|m, _| (m.size() <= limit(Limit::SplitSize)) as u64)),
    ("used_wide", Impl::GroupNum(|set, _| set.iter().any(|c| c.used & WIDE != 0) as u64)),
    ("used_clustered", Impl::GroupNum(|set, _| set.iter().any(|c| c.used & CLUSTERED != 0) as u64)),
    ("few_rewrites", Impl::TermNum(|m, _| (m.rewrites <= limit(Limit::UnclusteredAfter)) as u64)),
    ("replaceable", Impl::TermNum(|m, env| env.ctx(|c| crate::tfunc::replacement(m.tree(), c).is_some()) as u64)),
    ("abstracted", Impl::TermNum(|m, _| linear_mba::ABSTRACTED.contains(&m.origin.as_str()) as u64)),
    ("no_leaves", Impl::TermNum(|m, env| env.ctx(|w| linear_mba::leaf_count(m.tree(), w) == 0) as u64)),
    ("wide", Impl::TermNum(|m, env| env.ctx(|w| linear_mba::leaf_count(m.tree(), w) > limit(Limit::MaxLeaves)) as u64)),
    ("const_bitwise", Impl::TermNum(|m, env| env.ctx(|w| linear_mba::const_bitwise(m.tree(), w)) as u64)),
    ("cofactor", Impl::GroupNum(|_, env| env.cofactor as u64)),
];

/// The input features of `stats::shape` that conditions compare (`mul >= 4`).
pub const FEATURES: [&str; 8] = ["size", "vars", "depth", "mul", "bitconst", "arith_in_bit", "shift", "div"];

/// The name a step is counted as: `egglog/LABEL` for `(egglog LABEL)`, else its function's.
pub fn step_name(f: &str, args: &[Pipe]) -> String {
    match args {
        [Pipe::Name(l)] if f == "egglog" => format!("egglog/{l}"),
        _ => f.to_string(),
    }
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

    fn cli(&self, pass: &str) -> &'a Cli {
        self.cli.unwrap_or_else(|| panic!("{pass} needs a simplify run"))
    }

    fn prepass_of(&self, s: &str) -> (String, Vec<String>) {
        linear_mba::simplify_linear_with(s, self.w, self.signed, self.trace, self.passes)
    }

    /// `f` on the run of the innermost `scope`, or on a fresh one.
    pub(crate) fn ctx<R>(&self, f: impl FnOnce(&Ctx) -> R) -> R {
        match self.ctxs.borrow().last() {
            Some(c) => f(c),
            None => f(&Ctx::typed(self.w, self.signed)),
        }
    }

    /// `c` in infix, its constants as the final output prints them for the run's type.
    pub(crate) fn infix(&self, c: &Cand) -> String {
        let (w, signed) = (self.w, self.signed == Some(true));
        match self.cli {
            Some(cli) => crate::egglog_to_infix(c.term(), &|n| crate::norm_const(n, &cli.num_type)),
            None if w >= 64 => crate::egglog_to_infix(c.term(), &|n| n),
            None if signed => crate::egglog_to_infix(c.term(), &|n| (n << (64 - w)) >> (64 - w)),
            None => crate::egglog_to_infix(c.term(), &|n| n & ((1i64 << w) - 1)),
        }
    }
}

pub(crate) fn size_of(s: &str) -> usize {
    size(&parse(s))
}

/// Whether `t` has a shift, division or mulhi.
pub(crate) fn opaque(t: &Term) -> bool {
    match t {
        Term::Op(Op::Shl | Op::Shr | Op::Div | Op::Mod | Op::Mulhi, _) => true,
        Term::Op(_, a) => a.iter().any(opaque),
        _ => false,
    }
}

/// The first candidate of `set` proved minimal. Without a shift, division or mulhi in the
/// candidates, only smaller terms without them need ruling out: no rule makes one.
pub(crate) fn proved_minimal<'s>(set: &'s [Cand], env: &Env) -> Option<&'s Cand> {
    let cli = env.cli?;
    if crate::lang::vars::get(crate::rust_vars::PROVE_MINIMAL) == 0 {
        return None;
    }
    let t_only = !set.iter().any(|c| opaque(c.tree()));
    let ty = crate::eval::NumType::from_name(&cli.num_type);
    set.iter().find(|c| {
        let t = c.tree();
        minimal::is_tidy(t) && (ty.is_some_and(|ty| minimal::is_minimal(t, ty)) || t_only && minimal::is_t_minimal(t))
    })
}

thread_local! {
    /// Some pass was skipped past a limit while the switch `cut` was on.
    static CUT: Cell<bool> = const { Cell::new(false) };
    /// Seconds the last egglog round took.
    static LAST_ROUND: Cell<f64> = const { Cell::new(0.0) };
}

/// Starts a `simplify` run on this thread: no limit, no cut, no egglog round timed yet.
pub fn start() {
    crate::lang::vars::set(crate::rust_vars::DEADLINE, crate::lang::vars::NONE);
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
pub(crate) fn past_deadline(secs: f64, env: &Env) -> bool {
    past(secs) && {
        skipped(env);
        true
    }
}

/// Counts a step skipped past the time limit, as `past_deadline` does.
pub(crate) fn skipped(env: &Env) {
    stats::add("time_limit/skipped", 0.0);
    if crate::rust_vars::is_on("cut") {
        CUT.with(|c| c.set(true));
    }
    env.ctx(|c| c.mark_cut());
}

pub(crate) fn scope(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    env.ctxs.borrow_mut().push(Ctx::typed(env.w, env.signed));
    let out = scoped(|| go(&args[0], set, env));
    env.ctxs.borrow_mut().pop();
    out
}

pub(crate) fn tag(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [n, p] = args else { unreachable!() };
    let name = name(n);
    let clock = std::time::Instant::now();
    let before = set.first().cloned();
    let mut out = go(p, set, env)?;
    stats::add(&format!("{name}/run"), stats::since(clock));
    if let Some(m) = out.first_mut().filter(|m| !before.as_ref().is_some_and(|b| b.same(m))) {
        stats::add(&format!("{name}/won/{}", m.origin), 0.0);
        m.origin = name.to_string();
    }
    Ok(out)
}

pub(crate) fn origin(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [n, p] = args else { unreachable!() };
    let name = name(n);
    let clock = std::time::Instant::now();
    let out = go(p, set, env)?;
    stats::add(&format!("pre/{name}/made"), stats::since(clock));
    Ok(out.into_iter().map(|c| Cand { origin: name.to_string(), ..c }).collect())
}

pub(crate) fn smaller(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [n, p] = args else { unreachable!() };
    let name = name(n);
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
    m.origin = name.to_string();
    env.wins.set(env.wins.get() + 1);
    Ok(out)
}

pub(crate) fn regions(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let p = &args[0];
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

pub(crate) fn again(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let mut out = go(&args[0], set.clone(), env)?;
    if let (Some(m), Some(t)) = (out.first_mut(), set.first()) {
        if let Some(r) = env.ctx(|w| linear_mba::again(t.tree(), m.tree(), w)) {
            *m = Cand::of(r, m, 0, 0);
        }
    }
    Ok(out)
}

/// A `won` to count: the winning pass, each pass's size, the input's size.
pub(crate) type Won = (String, Vec<(String, usize)>, usize);

/// Counts `won` for the alternative pass (`linear_mba::ALTERNATIVES`, the origin of its
/// candidates) whose candidate `best` keeps; inside a `regions`, leaves it for that to count.
pub(crate) fn count_won(out: &[Cand], set: &[Cand], env: &Env) {
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

pub(crate) fn run_on(p: &Pipe, t: &Term, w: &Ctx, cofactor: bool) -> Option<Cand> {
    let passes = crate::passes::current();
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

/// `Passes::polish` on `c` alone, as a run of its own (its group variables, `smallest`, `wins`),
/// when it makes it smaller.
pub(crate) fn polish_one(c: &Cand, env: &Env) -> Option<Cand> {
    let run = Env::with(env.cli, env.passes, env.w, env.signed, env.trace, String::new(), c.term());
    let out = scoped(|| go(&env.passes.polish, vec![c.clone()], &run));
    out.inspect_err(fail).ok()?.into_iter().next().filter(|r| r.size() < c.size())
}

fn pre(e: &str) -> String {
    format!("pre/{}", stats::source_of(e).unwrap_or_else(|| "unlabeled".into()))
}

pub(crate) fn label(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    if set.is_empty() {
        return Ok(set);
    }
    let first = env.reg_main(name(&args[0]));
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
    Ok(set)
}

pub(crate) fn pre_done(_: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    if set.is_empty() {
        return Ok(set);
    }
    if env.trace {
        let kept: Vec<String> = set.iter().map(|c| format!("{} {}", c.origin, c.size())).collect();
        eprintln!("prepass: input {} chosen {}", size_of(&env.lex.borrow().input), kept.join(", then "));
    }
    let t0 = env.reg_main("t0").unwrap_or_else(|| Cand::new(&env.lex.borrow().input, "input"));
    Ok(set
        .iter()
        .enumerate()
        .map(|(i, c)| {
            stats::add(&format!("pre/{}/{}", c.origin, if i == 0 { "main" } else { "kept" }), 0.0);
            let term = if i == 0 && c.same(&t0) { t0.term().to_string() } else { show(c.tree()) };
            Cand::new(&term, &format!("pre/{}", c.origin))
        })
        .collect())
}

pub(crate) fn prepass(main: &Cand, env: &Env) -> Steps {
    let (alt, other) = env.prepass_of(main.term());
    Ok(std::iter::once(alt).chain(other).map(|e| Cand::new(&e, &pre(&e))).collect())
}

pub(crate) fn take_minimal(_: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    if set.is_empty() {
        return Ok(set);
    }
    let out = match proved_minimal(&set, env) {
        Some(c) => {
            stats::add("round/minimal", 0.0);
            vec![c.clone()]
        }
        None => set.clone(),
    };
    Ok(kept(out, &set))
}

pub(crate) fn reprint(main: &Cand, env: &Env) -> Steps {
    let cli = env.cli("reprint");
    let out = crate::egglog_to_infix(main.term(), &|n| crate::norm_const(n, &cli.num_type));
    Ok(vec![Cand::new(&crate::infix_to_egglog(&out, true), &main.origin)])
}

pub(crate) fn egglog(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let Some(main) = set.first() else { return Ok(set) };
    let name = step_name("egglog", args);
    let cli = env.cli(&name);
    if past_deadline(LAST_ROUND.with(|r| r.get()), env) {
        return Ok(set);
    }
    let roots: Vec<&str> = set.iter().map(Cand::term).collect();
    let clock = std::time::Instant::now();
    let e = crate::egglog_round(&env.egg, &roots, cli)?;
    LAST_ROUND.with(|r| r.set(clock.elapsed().as_secs_f64()));
    stats::add(&name, stats::since(clock));
    if env.trace {
        eprintln!("{name}: root {} extracted {}", main.size(), size_of(&e));
    }
    let origin = match stats::source_of(&e) {
        Some(src) => format!("pre/{src}"),
        None => name.clone(),
    };
    Ok(kept(vec![Cand::new(&e, &origin)], &set))
}

/// The pass over one term `f` on each candidate of `set`, which keeps its own origin.
pub(crate) fn term_pass(name: &str, f: impl Fn(&Term, &Ctx) -> Option<Term>, alt: Option<u8>, set: &[Cand], env: &Env) -> Vec<Cand> {
    env.ctx(|ctx| {
        set.iter()
            .filter_map(|c| {
                let t = c.tree();
                let (outer, left) = (ctx.swap_used(0), crate::lang::vars::get(crate::rust_vars::REWRITES) as usize);
                let r: Option<Term> = match alt {
                    Some(_) => stats::try_pass(name, t, || f(t, ctx)),
                    None => stats::pass(name, t, || f(t, ctx)),
                };
                let used = ctx.swap_used(0);
                ctx.swap_used(outer | used);
                let made = left.saturating_sub(crate::lang::vars::get(crate::rust_vars::REWRITES) as usize);
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
