//! The built-in functions of the pipeline language that run the passes of the simplification:
//! the passes over one term, the pre-pass, egglog rounds, polish, the conditions on candidates,
//! and the combinators that count stats or need a `linear_mba::Ctx`.

use crate::{linear_mba, minimal, stats};
use crate::cand::Cand;
use crate::eval::{Op, Term, parse, show, size};
use crate::lang::ast::{Fun, Holds, Pipe, Slot};
use crate::lang::builtins::{Builtin, Impl, name};
use crate::lang::eval::{Env, Lex, Steps, Value, fail, failed, go, kept, past, reads, scoped};
use crate::lang::types::Ty;
use crate::linear_mba::{CLUSTERED, Ctx, WIDE};
use crate::passes::Passes;
use crate::rust_vars::{Limit, limit, num_type};
use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;

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
    ("prepass", Impl::Join(prepass)),
    ("egglog", Impl::Group(egglog)),
    ("take_minimal", Impl::Group(take_minimal)),
    ("polish", Impl::EachCand(polish_one)),
    ("reprint", Impl::Join(|_, m, env| reprint(m, env))),
    ("settle", Impl::Group(settle)),
    ("parse", Impl::FromText(parse_text)),
    ("show", Impl::TermText(|c, _| crate::egglog_to_infix(c.term(), &|n| crate::norm_const(n, num_type())))),
    ("was_cut", Impl::GroupNum(|_, _| cut() as u64)),
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
    ("opaque", Impl::Num(|a, set, env| set.first().is_some_and(|m| opaque(m.tree()) && size_of(&env.prepass_of(&a[0], m.term()).0) > limit(Limit::TinySize)) as u64)),
    ("minimal", Impl::GroupNum(|set, env| proved_minimal(set, env).is_some() as u64)),
    ("mixed", Impl::TermNum(|m, _| crate::mixed(m.tree()) as u64)),
    ("rebuilds", Impl::Num(|a, set, env| set.first().is_some_and(|m| env.prepass_of(&a[0], m.term()).0 != m.term()) as u64)),
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
    /// A pre-pass run on `input` at width `w`, `signed` as in `linear_mba::Ctx`.
    pub fn prepass(p: &'a Passes, w: u32, signed: Option<bool>, trace: bool, input: &str) -> Env<'a> {
        Env::with(p, w, signed, trace, input)
    }

    /// The pre-pass `p`, written in this run, on the egglog term `s`.
    fn prepass_of(&self, p: &Pipe, s: &str) -> (String, Vec<String>) {
        let f = Sub::new(p, Some(&self.lex.borrow()), self.passes);
        prepass_run(&f, s, self.w, self.signed, self.trace)
    }

    /// `f` on the run of the innermost `scope`, or on a fresh one.
    pub(crate) fn ctx<R>(&self, f: impl FnOnce(&Ctx) -> R) -> R {
        match self.ctxs.borrow().last() {
            Some(c) => f(c),
            None => f(&Ctx::typed(self.w, self.signed)),
        }
    }

    /// `c` in infix, its constants as `show` prints them for the type `num_type`.
    pub(crate) fn infix(&self, c: &Cand) -> String {
        crate::egglog_to_infix(c.term(), &|n| crate::norm_const(n, num_type()))
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
pub(crate) fn proved_minimal<'s>(set: &'s [Cand], _: &Env) -> Option<&'s Cand> {
    if crate::lang::vars::get(crate::rust_vars::PROVE_MINIMAL) == 0 {
        return None;
    }
    let t_only = !set.iter().any(|c| opaque(c.tree()));
    let ty = crate::eval::NumType::from_name(num_type());
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

/// Starts a program on this thread: no limit, no cut, no egglog round timed yet.
pub fn start() {
    crate::lang::vars::set(crate::rust_vars::DEADLINE, crate::lang::vars::NONE);
    CUT.with(|c| c.set(false));
    LAST_ROUND.with(|r| r.set(0.0));
}

/// Whether a step was skipped past a limit with `cut` on since the program started.
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
    let (sub, p) = (Sub::of(&args[0], env), &args[1]);
    let w = env.ctx(|c| c.narrow(c.w));
    let mut out = Vec::with_capacity(set.len());
    for c in set {
        let outer = w.swap_used(0);
        let (mut err, mut won) = (None, None);
        let r = linear_mba::on_region(c.tree(), &w, &sub, || {
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
    let sub = Sub::of(&args[0], env);
    let mut out = go(&args[1], set.clone(), env)?;
    if let (Some(m), Some(t)) = (out.first_mut(), set.first()) {
        if let Some(r) = env.ctx(|w| linear_mba::again(t.tree(), m.tree(), w, &sub)) {
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

/// A function of the language that a pass runs on parts of its term: the argument of a
/// parameter such as `sub` in `(relate sub:pipe t:term) term`, resolved where the pass is
/// called.
pub(crate) struct Sub<'a> {
    /// Tells functions apart in memo keys: the definition run, or the term written; `None` for
    /// one that reads variables of the run it is written in, whose results are not memoized.
    pub(crate) id: Option<u64>,
    passes: &'a Passes,
    body: Body<'a>,
    /// The run it is written in; `None` for the body of a function without parameters, which
    /// is a run of its own.
    lex: Option<Rc<Lex>>,
    /// The function arguments of a `Body::Def` that is one pass over one term, made on first
    /// use: they are the same at every call.
    fns: std::cell::OnceCell<Box<Fns<'a>>>,
}

/// What a `Sub` runs.
enum Body<'a> {
    /// A function without parameters of `Sub::passes`.
    Def(&'a crate::lang::defs::Def),
    /// A term as written, and the function without parameters it is the body of, if any.
    Term(Pipe, Option<Arc<crate::lang::defs::Def>>),
}

impl Body<'_> {
    fn pipe(&self) -> &Pipe {
        match self {
            Body::Def(d) => &d.body,
            Body::Term(p, _) => p,
        }
    }
}

impl<'a> Sub<'a> {
    /// The function `arg` written in the run `lex`: a parameter's argument or a function
    /// variable's closure, as written where they come from, and a function without
    /// parameters by the definition a call runs.
    pub(crate) fn new(arg: &Pipe, lex: Option<&Rc<Lex>>, passes: &'a Passes) -> Sub<'a> {
        let (mut at, mut p, mut lex) = (arg as *const Pipe as u64, arg.clone(), lex.cloned());
        loop {
            (at, p, lex) = match &p {
                Pipe::Var(Slot::Param(i, _)) => {
                    let f = lex.as_ref().and_then(|l| l.frame.clone()).expect("a parameter outside the body of its function");
                    (&f.args[*i] as *const Pipe as u64, f.args[*i].clone(), Some(f.caller.clone()))
                }
                Pipe::Var(Slot::Local(n, Holds::Fn(_))) => {
                    let c = match lex.as_ref().and_then(|l| l.regs.borrow().get(n).cloned()) {
                        Some(Value::Fn(c)) => c,
                        _ => unreachable!("{n} holds no function value"),
                    };
                    (Arc::as_ptr(&c.body) as u64, (*c.body).clone(), Some(c.lex.clone()))
                }
                Pipe::App(Fun::Def(c), _) if c.def.late() => {
                    let d = c.latest_def(&passes.defs);
                    if !d.bare() {
                        at ^= (Arc::as_ptr(d) as u64).rotate_left(32);
                        break;
                    }
                    let id = Some(Arc::as_ptr(d) as u64);
                    let body = match passes.defs.get(d.slot.unwrap_or(usize::MAX)).filter(|e| Arc::ptr_eq(e, d)) {
                        Some(d) => Body::Def(d),
                        None => Body::Term((*d.body).clone(), Some(d.clone())),
                    };
                    return Sub { id, passes, body, lex: None, fns: Default::default() };
                }
                _ => break,
            };
        }
        let bare = lex.as_ref().is_none_or(|l| l.frame.is_none() && l.regs.borrow().is_empty());
        let closed = || {
            let (mut names, mut params) = (Vec::new(), Vec::new());
            reads(&p, &mut names, &mut params);
            names.is_empty() && params.is_empty()
        };
        let id = (bare || closed()).then_some(at);
        Sub { id, passes, body: Body::Term(p, None), lex, fns: Default::default() }
    }

    /// `new` for an argument of a call in the run `env`.
    pub(crate) fn of(arg: &Pipe, env: &Env<'a>) -> Sub<'a> {
        Sub::new(arg, Some(&env.lex.borrow()), env.passes)
    }

    /// The candidates it gives for `set` in the run `env`; it reads the variables of the run
    /// it is written in.
    pub(crate) fn run_in(&self, set: Vec<Cand>, env: &Env) -> Steps {
        crate::lang::eval::deeper(|| self.name(), || self.run_body(set, env))
    }

    fn run_body(&self, set: Vec<Cand>, env: &Env) -> Steps {
        match &self.lex {
            None => go(self.body.pipe(), set, env),
            Some(l) => {
                let outer = env.lex.replace(l.clone());
                let out = go(self.body.pipe(), set, env);
                env.lex.replace(outer);
                out
            }
        }
    }

    /// The function's name, or the term written, for errors.
    fn name(&self) -> String {
        match &self.body {
            Body::Def(d) => d.name.clone(),
            Body::Term(_, Some(d)) => d.name.clone(),
            Body::Term(p, None) => crate::lang::ast::show(p),
        }
    }

    /// Its main result on the term `t` of the run `w` and the `State::used` bits of that
    /// result: a pass over one term runs at once, without the counts of a step; anything else
    /// as a run of its own (`cofactor`: `Env::cofactor`).
    fn on(&self, t: &Term, w: &Ctx, cofactor: bool) -> Option<(Term, u8)> {
        crate::lang::eval::deeper(|| self.name(), || Ok(self.on_once(t, w, cofactor))).unwrap_or_else(|e| {
            fail(&e);
            None
        })
    }

    fn on_once(&self, t: &Term, w: &Ctx, cofactor: bool) -> Option<(Term, u8)> {
        if let Pipe::App(Fun::Builtin(b), args) = self.body.pipe()
            && matches!(b.imp, Impl::Each(_) | Impl::Polish(_))
        {
            if b.sig.switch && crate::rust_vars::is_off(b.name) {
                return Some((t.clone(), 0));
            }
            let run = |fns: &Fns| match b.imp {
                Impl::Each(f) => f(t, w, fns).unwrap_or_else(|| t.clone()),
                Impl::Polish(f) => f(t, w, fns),
                _ => unreachable!(),
            };
            let r = match &self.body {
                &Body::Def(d) => match &*d.body {
                    Pipe::App(Fun::Builtin(b), args) => run(self.fns.get_or_init(|| Box::new(Fns::new(b, args, None, self.passes)))),
                    _ => unreachable!(),
                },
                Body::Term(..) => run(&Fns::new(b, args, self.lex.as_ref(), self.passes)),
            };
            return Some((r, 0));
        }
        let mut env = Env::with(self.passes, w.w, w.signed, false, "");
        env.cofactor = cofactor;
        env.ctxs.borrow_mut().push(w.narrow(w.w));
        let input = Cand::of(t.clone(), &Cand::new("", "input"), 0, 0);
        let out = scoped(|| self.run_body(vec![input], &env));
        let c = out.inspect_err(fail).ok()?.into_iter().next()?;
        let used = c.used;
        Some((c.into_tree(), used))
    }

    /// Its main result on `t`, or `t` when it gives none.
    pub(crate) fn term(&self, t: &Term, w: &Ctx) -> Term {
        self.on(t, w, false).map_or_else(|| t.clone(), |(r, _)| r)
    }

    /// Its main result on `t`, `None` when it gives none; the `State::used` bits of that result
    /// count for the run.
    pub(crate) fn alt(&self, t: &Term, w: &Ctx) -> Option<Term> {
        self.alt_as(t, w, false)
    }

    /// `alt` for a linear cofactor of `poly_mba` (`Env::cofactor`).
    pub(crate) fn cofactor(&self, t: &Term, w: &Ctx) -> Option<Term> {
        self.alt_as(t, w, true)
    }

    fn alt_as(&self, t: &Term, w: &Ctx, cofactor: bool) -> Option<Term> {
        let (r, used) = self.on(t, w, cofactor)?;
        w.swap_used(w.swap_used(0) | used);
        Some(r)
    }
}

/// The function arguments of a call of a pass over one term, and the name it is counted as:
/// its name argument where its first parameter is a name (`memo`), else its own.
pub(crate) struct Fns<'a> {
    pub(crate) name: &'a str,
    /// In order; no pass takes more than two (`poly_mba`).
    subs: [Option<Sub<'a>>; 2],
}

impl<'a> Fns<'a> {
    pub(crate) fn new(b: &Builtin, args: &'a [Pipe], lex: Option<&Rc<Lex>>, passes: &'a Passes) -> Fns<'a> {
        let name = match (b.sig.params.first(), args.first()) {
            (Some(p), Some(a)) if p.ty == Ty::Name => crate::lang::builtins::name(a),
            _ => b.name,
        };
        let mut subs = [None, None];
        let fns = args.iter().enumerate().filter(|(i, _)| b.sig.param(*i).ty.is_step());
        for (s, (_, a)) in subs.iter_mut().zip(fns) {
            *s = Some(Sub::new(a, lex, passes));
        }
        Fns { name, subs }
    }

    /// `new` for a call in the run `env`.
    pub(crate) fn of(b: &Builtin, args: &'a [Pipe], env: &Env<'a>) -> Fns<'a> {
        Fns::new(b, args, Some(&env.lex.borrow()), env.passes)
    }

    /// The function argument `i`, counted among the function parameters.
    pub(crate) fn sub(&self, i: usize) -> &Sub<'a> {
        self.subs[i].as_ref().expect("a function argument")
    }
}

/// `f` given the functions `default.pipe` defines by `names`, as a pass is given them, in the
/// run under way.
#[cfg(test)]
pub(crate) fn with_fns<R>(names: &[&str], f: impl FnOnce(&[Sub]) -> R) -> R {
    let passes = crate::passes::current();
    let calls: Vec<Pipe> = names.iter().map(|n| crate::lang::defs::Call::bare(passes.defs.iter().find(|d| d.name == *n).unwrap())).collect();
    let subs: Vec<Sub> = calls.iter().map(|c| Sub::new(c, None, &passes)).collect();
    f(&subs)
}

/// The polish `args[0]` on `c` alone, as a run of its own (its group variables, `smallest`,
/// `wins`), when it makes it smaller.
pub(crate) fn polish_one(args: &[Pipe], c: &Cand, env: &Env) -> Option<Cand> {
    let f = Sub::of(&args[0], env);
    let run = Env::with(env.passes, env.w, env.signed, env.trace, c.term());
    let out = scoped(|| f.run_in(vec![c.clone()], &run));
    out.inspect_err(fail).ok()?.into_iter().next().filter(|r| r.size() < c.size())
}

/// The pre-pass `f` on the egglog term `egg` at width `w` (`signed` as in `Ctx`), as a run of
/// its own: its main rebuild and the others to union with it, candidates to stderr when
/// `trace` is set; `egg` itself when it gives none. The result for the last input is kept on
/// this thread, since a round asks the conditions and the step for the same one.
fn prepass_run(f: &Sub, egg: &str, w: u32, signed: Option<bool>, trace: bool) -> (String, Vec<String>) {
    type Result = (String, Vec<String>);
    type Last = Option<(String, u32, Option<bool>, bool, Passes, u64, Vec<u64>, Result)>;
    thread_local! {
        static LAST: std::cell::RefCell<Last> = const { std::cell::RefCell::new(None) };
    }
    // A variable bound where it is called (an assignment, `(off NAME)`) changes the result as the program does.
    let vars = crate::lang::vars::key();
    let hit = |(e, bits, s, t, q, id, v, _): &&(String, u32, Option<bool>, bool, Passes, u64, Vec<u64>, Result)| e == egg && *bits == w && *s == signed && *t == trace && f.id == Some(*id) && q == f.passes && *v == vars;
    if let Some(r) = LAST.with(|c| c.borrow().as_ref().filter(hit).map(|l| l.7.clone())) {
        return r;
    }
    let env = Env::with(f.passes, w, signed, trace, egg);
    let out = scoped(|| f.run_in(vec![Cand::new(egg, "input")], &env)).and_then(|out| failed().map_or(Ok(out), Err));
    let mut out = out.inspect_err(fail).unwrap_or_default().into_iter().map(|c| c.term().to_string());
    let r = (out.next().unwrap_or_else(|| egg.to_string()), out.collect());
    if failed().is_some() {
        return r;
    }
    if let Some(id) = f.id {
        LAST.with(|c| *c.borrow_mut() = Some((egg.to_string(), w, signed, trace, f.passes.clone(), id, vars, r.clone())));
    }
    r
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

pub(crate) fn prepass(args: &[Pipe], main: &Cand, env: &Env) -> Steps {
    let (alt, other) = env.prepass_of(&args[0], main.term());
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

pub(crate) fn reprint(main: &Cand, _: &Env) -> Steps {
    let out = crate::egglog_to_infix(main.term(), &|n| crate::norm_const(n, num_type()));
    Ok(vec![Cand::new(&crate::infix_to_egglog(&out, true), &main.origin)])
}

pub(crate) fn settle(_: &[Pipe], set: Vec<Cand>, _: &Env) -> Steps {
    if let Some(r) = set.first() {
        stats::add(&format!("final/{}", r.origin), 0.0);
        stats::settle(r.tree());
    }
    if cut() {
        stats::add("time/cut", 0.0);
    }
    Ok(set)
}

/// The candidate `s` stands for: an egglog term as written, or an infix expression read in
/// egglog form.
fn parse_text(s: &str, _: &Env) -> Steps {
    let s = s.trim();
    let egg = match crate::expr_convert::is_egglog(s) {
        true => crate::eval::check(s).map(|_| s.to_string()).map_err(|e| crate::Error::BackendError(format!("parse: {s:?}: {e}")))?,
        false => crate::expr_convert::parse_infix(s).map_err(|e| crate::Error::BackendError(format!("parse: {s:?}: {e}")))?,
    };
    Ok(vec![Cand::new(&egg, "input")])
}

pub(crate) fn egglog(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let Some(main) = set.first() else { return Ok(set) };
    let name = step_name("egglog", args);
    if past_deadline(LAST_ROUND.with(|r| r.get()), env) {
        return Ok(set);
    }
    let roots: Vec<&str> = set.iter().map(Cand::term).collect();
    let clock = std::time::Instant::now();
    let e = crate::egglog_round(&crate::egg_program(num_type()), &roots)?;
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
