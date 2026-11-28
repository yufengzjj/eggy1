//! Runs an `ast::Pipe`. Every step maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another; an expression gives a number for a list. A built-in
//! function runs through its entry of `builtins::BUILTINS`, which converts the input as its
//! calling kind says (`types::Kind`): a pass over one term (`linear_mba::TERM_PASSES`, the polish
//! passes as `polish_NAME`) runs on each candidate and replaces it by its result, the other
//! steps take the list whole.

use super::ast::{Fun, Holds, Pipe, Slot};
use super::builtins::{Builtin, Impl, Operator};
use super::host::{self, Cand, Ctx, Error, Passes, Won, skipped, term_pass};
use super::types::Ty;
use super::vars::NONE;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

pub(crate) type Steps = Result<Vec<Cand>, Error>;

/// What the passes of one run share.
pub struct Env<'a> {
    pub(crate) passes: &'a Passes,
    pub(crate) w: u32,
    pub(crate) signed: Option<bool>,
    pub(crate) trace: bool,
    /// The run's input, group variables and arguments; those of the call where a pipeline argument
    /// is written while it runs.
    pub(crate) lex: RefCell<Rc<Lex>>,
    pub(crate) moved: Cell<bool>,
    /// Results the `smaller` inside the innermost `wins` took.
    pub(crate) wins: Cell<usize>,
    /// Set inside a `regions`: the `won` its `best` would count, left for `regions` to count
    /// with the form it builds.
    pub(crate) deferred: RefCell<Option<Option<Won>>>,
    /// The run rebuilds a linear cofactor of `poly_mba`.
    pub(crate) cofactor: bool,
    /// The runs of the enclosing `scope`s, innermost last.
    pub(crate) ctxs: RefCell<Vec<Ctx>>,
}

/// What a term of the language gives: a number, candidates, a text, or a function value.
#[derive(Clone)]
pub enum Value {
    Num(u64),
    Group(Vec<Cand>),
    Text(String),
    Fn(Closure),
}

impl Value {
    fn group(self) -> Vec<Cand> {
        match self {
            Value::Group(g) => g,
            _ => unreachable!("a value that is not candidates where candidates are wanted"),
        }
    }

    fn num(self) -> u64 {
        match self {
            Value::Num(n) => n,
            _ => unreachable!("a value that is not a number where a number is wanted"),
        }
    }
}

/// A function value: a term that takes the input implicitly (`size`, `(under 20)`,
/// `(with_budget 8 rewrite)`) and what it reads of the run it is written in: the values its
/// local variables had then and the call's arguments, wherever it is applied.
#[derive(Clone)]
pub struct Closure {
    pub(crate) body: std::sync::Arc<Pipe>,
    pub(crate) lex: Rc<Lex>,
}

/// The input a function is applied to: the candidates a step takes, or those an expression
/// reads.
pub(crate) enum In<'s> {
    Own(Vec<Cand>),
    Ref(&'s [Cand]),
}

impl In<'_> {
    fn slice(&self) -> &[Cand] {
        match self {
            In::Own(v) => v,
            In::Ref(s) => s,
        }
    }

    fn vec(self) -> Vec<Cand> {
        match self {
            In::Own(v) => v,
            In::Ref(s) => s.to_vec(),
        }
    }
}

/// What a function value or pipeline argument takes along from the run where it is written
/// (a closure): the run's input and variables and the arguments of the call that run is.
pub(crate) struct Lex {
    pub(crate) input: String,
    /// The group variables (`(save R)`, `R = p`) and function variables (`f = size`); shared
    /// with the caller in the call of an `@inline` function, as `notes` is.
    pub(crate) regs: Rc<RefCell<HashMap<String, Value>>>,
    /// The open note registers, newest last, and the candidate each keeps.
    pub(crate) notes: Rc<RefCell<Vec<(String, Option<Cand>)>>>,
    pub(crate) frame: Option<Frame>,
}

impl Lex {
    pub(crate) fn new(input: &str, frame: Option<Frame>) -> Rc<Lex> {
        Rc::new(Lex { input: input.to_string(), regs: Default::default(), notes: Default::default(), frame })
    }
}

/// The arguments of a call of a function with parameters.
#[derive(Clone)]
pub(crate) struct Frame {
    pub(crate) call: std::sync::Arc<super::defs::Call>,
    pub(crate) args: std::sync::Arc<[Pipe]>,
    /// The run where the call is written, which its pipeline arguments run with.
    pub(crate) caller: Rc<Lex>,
    /// By parameter position, the values of the numeric arguments; empty without any.
    pub(crate) values: Vec<u64>,
}

impl<'a> Env<'a> {
    pub(crate) fn with(passes: &'a Passes, w: u32, signed: Option<bool>, trace: bool, input: &str) -> Env<'a> {
        let lex = RefCell::new(Lex::new(input, None));
        Env { passes, w, signed, trace, lex, moved: Cell::new(false), wins: Cell::new(0), deferred: Default::default(), cofactor: false, ctxs: Default::default() }
    }

    /// The text `p` gives on `set`: a string literal, or a function that gives a text on its
    /// input written or on the main candidate of `set`.
    pub(crate) fn text_of(&self, p: &Pipe, set: &[Cand]) -> Result<String, Error> {
        match p {
            Pipe::Text(t) => Ok(t.clone()),
            Pipe::App(Fun::Builtin(b), args) => {
                let Impl::TermText(f) = b.imp else { unreachable!("{} gives no text", b.name) };
                let input = match args.first() {
                    Some(x) => self.group_of(x, set),
                    None => set.to_vec(),
                };
                failed().map_or(Ok(()), Err)?;
                Ok(input.first().map(|m| f(m, self)).unwrap_or_default())
            }
            p => unreachable!("{p:?} gives no text"),
        }
    }

    pub(crate) fn reg(&self, r: &str) -> Vec<Cand> {
        match self.lex.borrow().regs.borrow().get(r) {
            Some(Value::Group(g)) => g.clone(),
            _ => Vec::new(),
        }
    }

    pub(crate) fn reg_main(&self, r: &str) -> Option<Cand> {
        match self.lex.borrow().regs.borrow().get(r) {
            Some(Value::Group(g)) => g.first().cloned(),
            _ => None,
        }
    }

    /// The function `f` written in the run `lex` applied to `input`: a number where `number`,
    /// else candidates. Every function value and pipeline argument is applied through it.
    fn apply_in(&self, f: &Pipe, lex: Rc<Lex>, input: In, number: bool) -> Result<Value, Error> {
        let outer = self.lex.replace(lex);
        let out = match number {
            true => Ok(Value::Num(self.value(f, input.slice()))),
            false => go(f, input.vec(), self).map(Value::Group),
        };
        self.lex.replace(outer);
        out
    }

    /// The argument of parameter `i` of the call whose body runs, applied to `input` in the
    /// run where the call is written.
    fn apply_param(&self, i: usize, input: In, number: bool) -> Result<Value, Error> {
        let (call, caller) = {
            let lex = self.lex.borrow();
            let f = lex.frame.as_ref().expect("a parameter outside the body of its function");
            (f.args.clone(), f.caller.clone())
        };
        self.apply_in(&call[i], caller, input, number)
    }

    /// The function value the variable `name` of the run holds applied to `input`.
    fn apply_var(&self, name: &str, input: In, number: bool) -> Result<Value, Error> {
        let f = match self.lex.borrow().regs.borrow().get(name) {
            Some(Value::Fn(c)) => c.clone(),
            _ => unreachable!("{name} holds no function value"),
        };
        self.apply_in(&f.body, f.lex, input, number)
    }

    /// `e` for the candidates `set`: a number or `NONE`.
    pub(crate) fn value(&self, e: &Pipe, set: &[Cand]) -> u64 {
        match e {
            Pipe::Num(n) => *n,
            Pipe::App(Fun::Op(o, _), args) => match (o, &args[..]) {
                (Operator::Arith(op), [x, y]) => super::builtins::arith(*op, self.value(x, set), self.value(y, set)),
                (Operator::Cmp(op), [x, y]) => op.holds(self.value(x, set), self.value(y, set)) as u64,
                (Operator::Not, [x]) => !self.holds(x, set) as u64,
                (Operator::And, xs) => xs.iter().all(|c| self.holds(c, set)) as u64,
                (Operator::Or, xs) => xs.iter().any(|c| self.holds(c, set)) as u64,
                _ => unreachable!("{o:?} applied to {} operands", args.len()),
            },
            Pipe::App(Fun::Builtin(b), args) => match b.input_at(args) {
                None => apply(b, args, In::Ref(set), self).map_or(0, Value::num),
                Some(k) => apply(b, &args[..k], In::Ref(&self.group_of(&args[k], set)), self).map_or(0, Value::num),
            },
            Pipe::Var(Slot::Global(i)) if *i == host::DEADLINE => match super::vars::read(*i) {
                NONE => NONE,
                at => at.saturating_sub(super::vars::epoch_ns()) / 1_000_000,
            },
            Pipe::Var(Slot::Global(i)) if *i == host::KEEP => super::vars::read(*i).max(1),
            Pipe::Var(Slot::Global(i)) => super::vars::read_var(*i),
            Pipe::Var(Slot::Param(i, _)) => {
                let v = match self.lex.borrow().frame.as_ref().expect("a parameter outside the body of its function") {
                    f if f.call.def.params[*i].ty == Ty::Num => Some(f.values[*i]),
                    _ => None,
                };
                v.unwrap_or_else(|| self.apply_param(*i, In::Ref(set), true).map_or(0, Value::num))
            }
            Pipe::Var(Slot::Local(n, Holds::Fn(_))) => self.apply_var(n, In::Ref(set), true).map_or(0, Value::num),
            Pipe::Var(Slot::Local(n, _)) => match self.lex.borrow().regs.borrow().get(n) {
                Some(Value::Num(v)) => *v,
                _ => 0,
            },
            Pipe::Seq(ps) => {
                let (e, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
                let set = match steps {
                    [Pipe::Var(Slot::Local(r, Holds::Group))] => self.reg(r),
                    steps => scoped(|| steps.iter().try_fold(set.to_vec(), |s, p| go(p, s, self))).unwrap_or_else(|e| {
                        fail(&e);
                        Vec::new()
                    }),
                };
                self.value(e, &set)
            }
            Pipe::App(Fun::Def(c), args) => {
                let input = args.get(c.def.params.len()).map(|p| self.group_of(p, set));
                let set = input.as_deref().unwrap_or(set);
                if c.def.steps {
                    let run = self.call_env(c, args, set);
                    return scoped(|| run.value(c.def.value.as_ref().unwrap(), set));
                }
                let caller = self.lex.borrow().clone();
                let frame = Frame { call: c.clone(), args: args.clone(), caller: caller.clone(), values: arg_values(c, args, set, self) };
                let lex = Lex { input: caller.input.clone(), regs: Default::default(), notes: caller.notes.clone(), frame: Some(frame) };
                bind_args(c, args, &lex, set, &caller);
                let outer = self.lex.replace(Rc::new(lex));
                let v = self.value(c.def.value.as_ref().expect("a function whose body is an expression"), set);
                self.lex.replace(outer);
                v
            }
            e => unreachable!("{e:?} gives no number"),
        }
    }

    /// The candidates `p` gives on `set`: a group value, or steps of this run; none after an
    /// error, which the run then gives.
    pub(crate) fn group_of(&self, p: &Pipe, set: &[Cand]) -> Vec<Cand> {
        match p {
            Pipe::Var(Slot::Local(r, Holds::Group)) => self.reg(r),
            Pipe::Seq(ps) if matches!(&ps[..], [Pipe::Var(Slot::Local(_, Holds::Group)), Pipe::App(Fun::Builtin(b), _)] if b.name == "main") => match &ps[0] {
                Pipe::Var(Slot::Local(r, _)) => self.reg_main(r).into_iter().collect(),
                _ => unreachable!(),
            },
            p => scoped(|| go(p, set.to_vec(), self)).unwrap_or_else(|e| {
                fail(&e);
                Vec::new()
            }),
        }
    }

    /// The run of a call of `c` on `set`, with its own group variables and the call's arguments.
    fn call_env(&self, c: &std::sync::Arc<super::defs::Call>, args: &std::sync::Arc<[Pipe]>, set: &[Cand]) -> Env<'a> {
        let input = set.first().map_or_else(String::new, |c| c.term().to_string());
        let mut run = Env::with(self.passes, self.w, self.signed, self.trace, &input);
        run.cofactor = self.cofactor;
        if !args.is_empty() || c.def.input.is_some() {
            let caller = self.lex.borrow().clone();
            let frame = Frame { call: c.clone(), args: args.clone(), caller: caller.clone(), values: arg_values(c, args, set, self) };
            let lex = Lex::new(&input, Some(frame));
            bind_args(c, args, &lex, set, &caller);
            run.lex = RefCell::new(lex);
        }
        if let Some(c) = self.ctxs.borrow().last() {
            run.ctxs.borrow_mut().push(c.narrow(c.w));
        }
        run
    }

    /// Whether `e` is not 0 for the candidates `set`.
    pub(crate) fn holds(&self, e: &Pipe, set: &[Cand]) -> bool {
        self.value(e, set) != 0
    }

    /// `e` as a count: `none` is no limit.
    pub(crate) fn times(&self, e: &Pipe, set: &[Cand]) -> usize {
        self.value(e, set).try_into().unwrap_or(usize::MAX)
    }
}

pub(crate) fn dedup(set: Vec<Cand>) -> Vec<Cand> {
    let mut out: Vec<Cand> = Vec::with_capacity(set.len());
    for c in set {
        if !out.iter().any(|o| o.same(&c)) {
            out.push(c);
        }
    }
    out
}

pub(crate) fn past(secs: f64) -> bool {
    let at = super::vars::get(host::DEADLINE);
    at != super::vars::NONE && super::vars::epoch_ns().saturating_add((secs * 1e9) as u64) >= at
}

/// Whether `p` calls an `@uncounted` function, whose skip past the time limit `skipped`
/// does not count.
pub(crate) fn uncounted(p: &Pipe) -> bool {
    matches!(p, Pipe::App(Fun::Builtin(b), _) if b.uncounted)
}

/// `f` as a scope (a sequence, `scope` or a pipeline run): an assignment inside it ends
/// with it.
pub(crate) fn scoped<R>(f: impl FnOnce() -> R) -> R {
    super::vars::in_scope(f)
}

thread_local! {
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

/// Forgets the error `fail` recorded, for a program that starts.
pub(crate) fn clear_failed() {
    FAILED.with(|f| f.borrow_mut().take());
}

/// The candidates `p` gives for `set`, as a scope of the program under way.
pub fn run(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    scoped(|| go(p, set, env)).and_then(|out| failed().map_or(Ok(out), Err))
}

/// `time_limit = ms` in the scope under way.
fn assign_time_limit(ms: u64) {
    let at = match ms {
        super::vars::NONE => super::vars::NONE,
        _ => super::vars::epoch_ns().saturating_add(ms.saturating_mul(1_000_000)),
    };
    super::vars::bind(host::DEADLINE, at);
}

/// Whether `p` calls a `@timed` function (a built-in, `def` or macro), which past the time
/// limit is skipped and gives its input.
pub(crate) fn timed(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => b.timed,
        Pipe::App(Fun::Def(c), _) => c.def.timed,
        Pipe::Expanded(m) => m.timed,
        _ => false,
    }
}

/// Whether `p` is a step that computes candidates: a call of a `@timed` built-in function
/// that is not `@uncounted` and takes no pipeline, or of a `def` that is not `inline`.
pub(crate) fn computes(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => b.timed && !b.uncounted && !b.sig.params.iter().any(|q| q.ty.is_step()),
        Pipe::App(Fun::Def(c), _) => !c.def.inline,
        _ => false,
    }
}

pub(crate) fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Steps {
    // Every candidate equals the input, so stopping anywhere keeps the result right.
    if let Some(e) = failed() {
        return Err(e);
    }
    if timed(p) && past(0.0) {
        if !uncounted(p) {
            skipped(env);
        }
        return Ok(set);
    }
    match p {
        Pipe::App(Fun::Builtin(b), args) => apply(b, args, In::Own(set), env).map(Value::group),
        Pipe::Seq(ps) => scoped(|| ps.iter().try_fold(set, |s, p| go(p, s, env))),
        Pipe::Expanded(m) => {
            let steps = || m.steps.iter().try_fold(set, |s, p| go(p, s, env));
            if m.scoped { scoped(steps) } else { steps() }
        }
        Pipe::App(Fun::Def(c), args) if c.def.inline => {
            let caller = env.lex.borrow().clone();
            let values = arg_values(c, args, &set, env);
            let frame = Frame { call: c.clone(), args: args.clone(), caller: caller.clone(), values };
            let lex = Lex { input: caller.input.clone(), regs: caller.regs.clone(), notes: caller.notes.clone(), frame: Some(frame) };
            let outer = env.lex.replace(Rc::new(lex));
            let out = match &*c.body {
                Pipe::Seq(ps) if c.def.flat => ps.iter().try_fold(set, |s, p| go(p, s, env)),
                body => go(body, set, env),
            };
            env.lex.replace(outer);
            out
        }
        Pipe::App(Fun::Def(c), args) => {
            let run = env.call_env(c, args, &set);
            scoped(|| go(&c.body, set, &run))
        }
        Pipe::Var(Slot::Param(i, _)) => env.apply_param(*i, In::Own(set), false).map(Value::group),
        Pipe::Var(Slot::Local(n, Holds::Fn(_))) => env.apply_var(n, In::Own(set), false).map(Value::group),
        Pipe::Var(Slot::Local(r, Holds::Group)) => Ok(env.reg(r)),
        Pipe::Bind(x, e) => {
            match x {
                Slot::Global(i) => {
                    let v = match &**e {
                        Pipe::Name(t) => host::NUM_TYPES.iter().position(|n| n == t).map_or(NONE, |k| k as u64),
                        e => env.value(e, &set),
                    };
                    match *i {
                        host::DEADLINE => assign_time_limit(v),
                        i if super::vars::is_switch(i) => super::vars::bind(i, (v != 0) as u64),
                        i => super::vars::bind(i, v),
                    }
                }
                Slot::Local(r, held) => {
                    let v = match held {
                        Holds::Num => Value::Num(env.value(e, &set)),
                        Holds::Group => Value::Group(scoped(|| go(e, set.clone(), env))?),
                        Holds::Fn(_) => Value::Fn(capture(e, &env.lex.borrow())),
                    };
                    env.lex.borrow().regs.borrow_mut().insert(r.clone(), v);
                }
                Slot::Param(..) => unreachable!("a parameter is not assigned"),
            }
            Ok(set)
        }
        p => unreachable!("{p:?} is not a step"),
    }
}

/// The closure of `body` written in the run `lex`: the values of the local variables it reads
/// now, and the call's arguments where it reads parameters (the caller only for those that
/// are not numbers), so it holds no table it may be stored in.
fn capture(body: &std::sync::Arc<Pipe>, lex: &Lex) -> Closure {
    let (mut names, mut params) = (Vec::new(), Vec::new());
    reads(body, &mut names, &mut params);
    let regs: HashMap<String, Value> = {
        let all = lex.regs.borrow();
        names.into_iter().filter_map(|n| all.get(&n).cloned().map(|v| (n, v))).collect()
    };
    let frame = lex.frame.as_ref().filter(|_| !params.is_empty()).map(|f| match params.iter().all(|i| f.call.def.params[*i].ty == Ty::Num) {
        true => Frame { caller: Lex::new("", None), ..f.clone() },
        false => f.clone(),
    });
    let lex = Lex { input: lex.input.clone(), regs: Rc::new(RefCell::new(regs)), notes: lex.notes.clone(), frame };
    Closure { body: body.clone(), lex: Rc::new(lex) }
}

/// The names `p` may read as variables, and the parameters it reads, by position; inside the
/// body of an `@inline` call too, which shares the run.
fn reads(p: &Pipe, names: &mut Vec<String>, params: &mut Vec<usize>) {
    let mut all = |ps: &[Pipe]| ps.iter().for_each(|q| reads(q, names, params));
    match p {
        Pipe::Name(n) | Pipe::Var(Slot::Local(n, _)) => names.push(n.clone()),
        Pipe::Var(Slot::Param(i, _)) => params.push(*i),
        Pipe::App(f, ps) => {
            all(ps);
            if let Fun::Def(c) = f
                && c.def.inline
            {
                reads(&c.body, names, params);
            }
        }
        Pipe::Seq(ps) => all(ps),
        Pipe::Expanded(m) => all(&m.steps),
        Pipe::Bind(_, q) => reads(q, names, params),
        Pipe::Num(_) | Pipe::Text(_) | Pipe::Var(Slot::Global(_)) => {}
    }
}

/// The built-in function `b` applied to `args` and `input`, the input converted as its
/// calling kind says.
fn apply(b: &Builtin, args: &[Pipe], input: In, env: &Env) -> Result<Value, Error> {
    let set = match b.imp {
        Impl::Operator(_) => unreachable!("{} is evaluated by Env::value", b.name),
        Impl::TermNum(f) => return Ok(Value::Num(input.slice().first().map_or(0, |m| f(m, env)))),
        Impl::GroupNum(f) => return Ok(Value::Num(if input.slice().is_empty() { 0 } else { f(input.slice(), env) })),
        Impl::Num(f) => return Ok(Value::Num(f(args, input.slice(), env))),
        Impl::FromText(f) => return f(&env.text_of(&args[0], input.slice())?, env).map(Value::Group),
        Impl::TermText(f) => return Ok(Value::Text(input.slice().first().map(|m| f(m, env)).unwrap_or_default())),
        _ => input.vec(),
    };
    Ok(Value::Group(match b.imp {
        Impl::Group(f) => f(args, set, env)?,
        Impl::Each(f) => dedup(term_pass(b.name, f, None, &set, env)),
        Impl::Alt(f, bit) => dedup(term_pass(b.name, f, Some(bit), &set, env)),
        Impl::Polish(f) => dedup(term_pass(b.name, |t, w| Some(f(t, w)), None, &set, env)),
        Impl::Main(f) => match set.first() {
            Some(main) => kept(f(main, env)?, &set),
            None => set,
        },
        Impl::EachCand(_) if set.is_empty() => set,
        Impl::EachCand(f) => kept(set.iter().map(|c| f(c, env).unwrap_or_else(|| c.clone())).collect(), &set),
        _ => unreachable!("{} is not a step", b.name),
    }))
}

/// `out` without repeats, a term given back from `set` keeping the origin it came with.
pub(crate) fn kept(out: Vec<Cand>, set: &[Cand]) -> Vec<Cand> {
    dedup(out)
        .into_iter()
        .map(|c| match set.iter().find(|s| s.same(&c)) {
            Some(s) => s.clone(),
            None => c,
        })
        .collect()
}

/// The values of the numeric arguments of `c` on the caller's candidates `set`, by parameter
/// position; empty without any.
fn arg_values(c: &super::defs::Call, args: &[Pipe], set: &[Cand], env: &Env) -> Vec<u64> {
    if !c.def.params.iter().any(|p| p.ty == Ty::Num) {
        return Vec::new();
    }
    args.iter().zip(&c.def.params).map(|(a, p)| if p.ty == Ty::Num { env.value(a, set) } else { 0 }).collect()
}

/// Binds in the run `lex` of the call `c` its group parameters to the caller's group
/// variables and its input parameter to `set`.
fn bind_args(c: &super::defs::Call, args: &[Pipe], lex: &Lex, set: &[Cand], caller: &Lex) {
    let mut regs = lex.regs.borrow_mut();
    for (p, a) in c.def.params.iter().zip(args) {
        if let (Ty::Group, Pipe::Var(Slot::Local(r, _))) = (&p.ty, a) {
            let g = match caller.regs.borrow().get(r) {
                Some(Value::Group(g)) => g.clone(),
                _ => Vec::new(),
            };
            regs.insert(p.name.clone(), Value::Group(g));
        }
    }
    if let Some(g) = &c.def.input {
        regs.insert(g.clone(), Value::Group(set.to_vec()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin_passes::{cut, past_deadline, start};
    use crate::lang::builtins::PRINTED;
    use crate::rust_vars::{Limit, limit};

    #[test]
    fn assert_and_print() {
        let run_on = |spec: &str, input: &str, w: u32, signed: Option<bool>| {
            let p = Passes::parse(spec).unwrap();
            let input = Cand::new(input, "input");
            PRINTED.with(|l| l.borrow_mut().clear());
            let r = crate::lang::run::prepass_of(&p, input.clone(), w, signed);
            (r.map(|c| c.iter().map(|c| c.term().to_string()).collect::<Vec<_>>()).map_err(|e| e.to_string()), PRINTED.with(|l| l.take()))
        };
        let x3 = "(Add (Var \"x\") (Num 253))";
        let run = |spec: &str| run_on(spec, x3, 64, None);
        assert_eq!(run("prepass=(assert (size == 3) \"three\")"), (Ok(vec![x3.to_string()]), vec![]));
        assert_eq!(run("prepass=(assert (size > 3) \"not \\\"big\\\" \\\\ (#)\") | rewrite").0, Err("not \"big\" \\ (#)".into()));
        assert_eq!(run("prepass=time_limit = 0 | (assert 0 \"past the limit too\")").0, Err("past the limit too".into()));
        let (r, lines) = run_on("prepass=(save t) | (print \"size\" size none max_leaves (size * 2) t rewrite some_name) | (print t)", x3, 8, Some(false));
        assert_eq!(r, Ok(vec![x3.to_string()]), "print passes the candidates on");
        assert_eq!(lines, ["size 3 none 6 6 (x + 0xfd) (rewrite t:term) term some_name", "(x + 0xfd)"]);
        assert_eq!(run_on("num_type=i8 prepass=(save t) | (print t)", x3, 8, Some(true)).1, ["(x - 3)"], "constants as the type num_type prints them");
        let two = "(Add (And (Var \"x\") (Var \"y\")) (Or (Var \"x\") (Var \"y\")))";
        assert_eq!(run_on("prepass=(union id rewrite) | (save u) | (print u)", two, 64, None).1, ["((x & y) + (x | y)), (x + y)"]);
        let (_, lines) = run("(def (g) id) prepass=f:term->num = size | (print f g) | g");
        assert_eq!(lines, ["f:term->num (g g:group) group"]);
        for (bad, msg) in [("prepass=(assert 1)", "assert takes"), ("prepass=(assert 1 x)", "msg:text"), ("prepass=(print)", "print takes"), ("prepass=(print \"a)", "unclosed string"), ("prepass=(print \"a\\n\")", "unknown escape")] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
        assert_eq!(Passes::parse_noting("prepass=(save t) | (print t) | (assert (size (main t)) \"m\")").unwrap().1, Vec::<String>::new(), "print and assert read their group variables");
        let p = Passes::parse("prepass=(print \"a \\\"b\\\" c\" 1) | (assert 1 \"x;y z\")").unwrap();
        assert_eq!(crate::lang::ast::show(&p.prepass), "(print \"a \\\"b\\\" c\" 1) | (assert 1 \"x;y z\")");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "strings are written back as read");
        let (_, lines) = run("(let l rewrite | lowbits) (def @inline (k p) p | rewrite) prepass=(print fix l k rewrite)");
        assert_eq!(lines, ["(fix n:num p:pipe g:group) group (l g:group) group (k p:pipe g:group) group (rewrite t:term) term"], "a function value prints as its signature");
        let p = Passes::parse("prepass=f:term->num = size | (print f rewrite)").unwrap();
        let Pipe::Seq(steps) = &p.prepass else { panic!() };
        let Pipe::App(_, args) = &steps[1] else { panic!() };
        assert!(matches!(&args[0], Pipe::Var(Slot::Local(n, Holds::Fn(_))) if n == "f") && matches!(&args[1], Pipe::App(Fun::Builtin(b), a) if b.name == "rewrite" && a.is_empty()));
    }

    #[test]
    fn main_and_index_pick_a_candidate() {
        let printed = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            let input = Cand::new("(Add (Xor (Var \"x\") (Var \"y\")) (Mul (Num 2) (And (Var \"x\") (Var \"y\"))))", "input");
            PRINTED.with(|l| l.borrow_mut().clear());
            crate::lang::run::prepass_of(&p, input.clone(), 64, None).unwrap();
            PRINTED.with(|l| l.take())
        };
        let groups = "prepass=(save t) | (union id rewrite) | (save u) | none | (save e) | (load t)";
        assert_eq!(printed(&format!("{groups} | (print u (size (main t)) (size (main e)) (size (index 0 u)) (size (index 1 u)) (size (index 2 u)) (size (index none u)))")), ["((x ^ y) + (2 * (x & y))), (x + y) 9 0 9 3 0 0"]);
        assert_eq!(printed(&format!("{groups} | (print (same (main t)) (same (main e)) (same (index 1 u)) (rewrite | (same (index 1 u))))")), ["1 0 0 1"]);
        assert_eq!(printed(&format!("{groups} | none | (print (size (main t)) size (same (main t)) ((main t) | size) ((index 1 u) | size))")), ["9 0 0 9 3"], "on no candidates");
    }

    #[test]
    fn and_or_evaluate_later_operands_only_while_needed() {
        let printed = |cond: &str| {
            let p = Passes::parse(&format!("prepass=(if ({cond}) id)")).unwrap();
            let input = Cand::new("(Var \"x\")", "input");
            PRINTED.with(|l| l.borrow_mut().clear());
            crate::lang::run::prepass_of(&p, input.clone(), 64, None).unwrap();
            PRINTED.with(|l| l.take())
        };
        let b = "((print \"b\") | size)";
        let c = "((print \"c\") | size)";
        assert_eq!(printed(&format!("0 && {b} && {c}")), Vec::<String>::new());
        assert_eq!(printed(&format!("1 && {b} && {c}")), ["b", "c"]);
        assert_eq!(printed(&format!("1 || {b} || {c}")), Vec::<String>::new());
        assert_eq!(printed(&format!("0 || {b} || {c}")), ["b"], "size is 1, so c is not needed");
        assert_eq!(printed(&format!("{b} + {c} > 0")), ["b", "c"], "other operators evaluate every operand");
    }

    #[test]
    fn time_limit_ends_with_its_sequence() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let limit = |ms| Pipe::assign(crate::rust_vars::DEADLINE, Pipe::Num(if ms > 0 { ms } else { NONE }));
        let wait = || std::thread::sleep(std::time::Duration::from_millis(5));
        crate::rust_vars::in_default_run(|| {
            go(&limit(1), vec![], &env).unwrap();
            wait();
            assert!(past_deadline(0.0, &env));
            scoped(|| {
                go(&limit(0), vec![], &env).unwrap();
                assert!(past_deadline(0.0, &env), "a clear inside keeps the outer limit");
                go(&limit(100_000), vec![], &env).unwrap();
                assert!(past_deadline(0.0, &env), "an inner limit is never later than the outer one");
            });
            assert!(past_deadline(0.0, &env));
            go(&limit(0), vec![], &env).unwrap();
            assert!(!past_deadline(0.0, &env));
            go(&limit(1), vec![], &env).unwrap();
        });
        wait();
        assert!(!past_deadline(0.0, &env), "a limit ends with its sequence");
        assert!(!cut());
    }

    #[test]
    fn off_ends_with_its_sequence() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        crate::rust_vars::in_default_run(|| {
            step("((off relate) | id)");
            assert!(!crate::rust_vars::is_off("relate"), "a group ends its off");
            step("(rewrites = 8 | (off relate))");
            assert!(!crate::rust_vars::is_off("relate"), "a sequence ends its off");
            step("(scope (off relate))");
            assert!(!crate::rust_vars::is_off("relate"), "scope ends its off");
            step("(if 1 (off relate))");
            assert!(crate::rust_vars::is_off("relate"), "a branch that is no sequence does not");
        });
        assert!(!crate::rust_vars::is_off("relate"));
    }

    #[test]
    fn on_and_off_switches() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        use crate::rust_vars::{is_off, is_on};
        crate::rust_vars::in_default_run(|| {
            step("(off relate tfunc)");
            assert!(is_off("relate") && is_off("tfunc"), "several names in one off");
            step("(on relate)");
            assert!(!is_off("relate") && is_off("tfunc"), "the later switch counts");
            assert!(crate::lang::run::within(&passes, || !is_off("relate") && is_off("tfunc")), "a run started here keeps them");
            crate::rust_vars::with_off(&["relate"], || {
                assert!(is_off("relate"));
                step("(on relate)");
                assert!(!is_off("relate"));
            });
            assert!(!is_off("relate"));
            assert!(!is_on("cut"));
            step("(on cut)");
            assert!(is_on("cut"));
        });
        assert!(crate::lang::vars::get(crate::rust_vars::CUT) == crate::lang::vars::NONE && !is_off("tfunc"));
    }

    #[test]
    fn assignments_bind_in_their_scope() {
        use crate::lang::vars::{NONE, get};
        use crate::rust_vars::{BIT_SPLIT_BUDGET, REWRITES, is_off, is_on};
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Sub (Var \"x\") (Var \"y\"))");
        let step = |p: &str| go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input")], &env).unwrap();
        crate::rust_vars::in_default_run(|| {
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
            step("(origin x (bit_split_budget = bit_split_budget + 1))");
            assert_eq!(get(BIT_SPLIT_BUDGET), NONE, "a pipeline argument is a scope");
        });
        assert_eq!(get(crate::lang::vars::var_index("split_runs").unwrap()), NONE);
        assert!(!is_off("relate") && get(crate::rust_vars::CUT) == NONE);
    }

    #[test]
    fn cand_is_defined_in_the_language() {
        let x = "(Sub (Var \"x\") (Var \"y\"))";
        let run = |spec: &str| {
            let p = Passes::parse(&format!("prepass={spec}")).unwrap();
            let env = Env::prepass(&p, 32, None, false, x);
            PRINTED.with(|l| l.borrow_mut().clear());
            let out = crate::lang::run::within(&p, || go(&p.prepass, vec![Cand::new(x, "input")], &env).unwrap());
            (out.iter().map(|c| c.origin.clone()).collect::<Vec<_>>(), PRINTED.with(|l| l.take()))
        };
        assert_eq!(run("(cand pre_unified unified (print bit_split_budget) | rewrite)"), (vec!["unified".to_string()], vec!["8".to_string()]), "origin n, bit_split_budget = cand_bit_splits inside");
        assert_eq!(run("(cand pre_unified unified (print bit_split_budget)) | (print bit_split_budget)"), (vec!["unified".to_string()], vec!["8".to_string(), "none".to_string()]), "the budget ends with cand");
        assert_eq!(run("pre_unified = 0 | (cand pre_unified unified (print 1))"), (vec![], vec![]), "a switch at 0 gives none and runs nothing");
        assert_eq!(run("(cand 1 first id) | (origin second id)"), (vec!["second".to_string()], vec![]));
        for off in ["1", "0"] {
            assert_eq!(run(&format!("pre_unified = {off} | time_limit = 0 | (cand pre_unified unified none)")).0, ["input"], "skipped past the time limit, as a step");
        }
        let p = Passes::parse("pre=no_wide").unwrap();
        let on = |n: &str| crate::lang::run::within(&p, || crate::lang::vars::get(crate::lang::vars::var_index(n).unwrap()));
        assert_eq!((on("pre_unified"), on("pre_no_wide"), on("pre_halve_input")), (0, 1, 0), "pre= is an assignment to the pre_ switches");
    }

    #[test]
    fn only_timed_defs_are_skipped_past_the_time_limit() {
        let x = "(Var \"x\")";
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            let env = Env::prepass(&p, 32, None, false, x);
            PRINTED.with(|l| l.borrow_mut().clear());
            crate::lang::run::within(&p, || go(&p.prepass, vec![Cand::new(x, "input")], &env).unwrap());
            PRINTED.with(|l| l.take())
        };
        let defs = "(def (f) (print 1)) (def @timed (g) (print 2)) (def @inline @timed (h) (print 3)) (def @inline @timed (k n) (print n))";
        assert_eq!(run(&format!("{defs} prepass=f | g | h | (k 4)")), ["1", "2", "3", "4"]);
        assert_eq!(run(&format!("{defs} prepass=time_limit = 0 | f | g | h | (k 4)")), ["1"]);
        for (bad, msg) in [("(def @timed (n) size + 1)", "@timed is for a function that gives candidates"), ("(def @timed (prepass) id)", "takes no @timed")] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn run_settings_are_variables() {
        use crate::lang::vars::{NONE, get, var_index};
        use crate::rust_vars::{KEEP, RESTARTS};
        let passes = Passes::default();
        let x = "(Sub (Var \"x\") (Var \"y\"))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let input = || Cand::new(x, "input");
        let step = |p: &str| go(&crate::lang::parser::parse(p).unwrap(), vec![input()], &env).unwrap();
        let extra = var_index("extra").unwrap();
        crate::lang::run::within(&passes, || {
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
        assert_eq!(get(extra), NONE, "the bindings of the program end with it");
        let mut cli = crate::Cli { max_restarts: 4, iter_limit: 7, ..Default::default() };
        let counts = |cli: &crate::Cli| crate::lang::run::within(&crate::cli::parse(cli, None).unwrap().0, || (get(RESTARTS), get(crate::rust_vars::ITER_LIMIT), get(extra)));
        assert_eq!(counts(&cli), (4, 7, 2));
        cli.passes = "extra=9 restarts=restarts+1".into();
        assert_eq!(counts(&cli), (5, 7, 9), "--passes items come after -m and -i");
        cli.passes = String::new();
        assert_eq!(counts(&cli), (4, 7, 2), "nothing leaks between programs");
    }

    #[test]
    fn restarts_less_one_counts_the_later_rounds() {
        let passes = Passes::default();
        let x = "(Var \"x\")";
        let env = Env::prepass(&passes, 32, None, false, x);
        let input = || Cand::new(x, "input");
        let Pipe::App(_, args) = crate::lang::parser::parse("(fix (restarts - 1) id)").unwrap() else { unreachable!() };
        let count = &args[0];
        let rounds = |m: usize| {
            let cli = crate::Cli { max_restarts: m, ..Default::default() };
            crate::lang::run::within(&crate::cli::parse(&cli, None).unwrap().0, || env.times(&count, &[input()]))
        };
        for m in [0, 1, 2, 5] {
            assert_eq!(rounds(m), m.max(1) - 1, "-m {m}: the later rounds, as when restarts read as -m less 1");
        }
    }

    #[test]
    fn a_limit_cuts_the_run_only_with_cut_on() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        for on in [false, true] {
            start();
            crate::rust_vars::in_default_run(|| {
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
        crate::rust_vars::in_default_run(|| {
            step("(on cut) | (clear r) | time_limit = 0 | (note r) | (take_min r)");
            assert!(!cut(), "a note skipped past the limit does not cut the run");
            step("(on cut) | (smallest time_limit = 0 | rewrite)");
            assert!(cut(), "the pass skipped there does");
        });
        start();
        assert!(!cut());
    }

    const SUB: &str = "(Sub (Or (Var \"x\") (Var \"y\")) (And (Var \"x\") (Var \"y\")))";
    const XOR: &str = "(Xor (Var \"x\") (Var \"y\"))";

    fn terms(set: &[Cand]) -> Vec<String> {
        set.iter().map(|c| c.term().to_string()).collect()
    }

    fn expr(s: &str) -> Pipe {
        let Pipe::App(_, args) = crate::lang::parser::parse(&format!("(filter ({s}))")).unwrap() else { unreachable!() };
        args[0].clone()
    }

    #[test]
    fn retry_keeps_a_when_b_gives_none() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let step = |p: &str| terms(&go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::rust_vars::in_default_run(|| {
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
        let step = |p: &str| terms(&go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::rust_vars::in_default_run(|| {
            assert_eq!(step("(save p) | polish | (load p)"), [SUB], "polish has its own registers");
            assert_eq!(step("(smallest polish)"), [SUB], "an outer smallest sees no candidate made inside polish");
            assert_eq!(step("(smallest rewrite | none | (load p))"), [XOR, SUB], "it sees those of the passes of its own run");
        });
    }

    #[test]
    fn def_is_a_run_of_its_own() {
        let passes = Passes::parse("(def (f) rewrite | (save p) | split_runs = 3 | (if (split_runs == 3) (load p) none)) (def (h) rewrite | none) (def (k) (if (split_runs == 5) id none))").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let mut names = crate::lang::defs::Defs::new();
        for d in &passes.defs {
            names.insert(d.name.clone(), crate::lang::defs::Named { pipe: crate::lang::defs::Call::bare(d), flat: false, run: true, params: Vec::new(), def: Some(d.clone()) });
        }
        for item in ["(def @inline (g) rewrite | (save p) | split_runs = 3)", "(def @inline (h2) rewrite | none)"] {
            let d = crate::lang::defs::parse_definition(item, &names, &mut Vec::new()).unwrap();
            names.insert(d.name, crate::lang::defs::Named { pipe: d.pipe, flat: d.flat, run: false, params: Vec::new(), def: None });
        }
        let step = |p: &str| terms(&go(&crate::lang::parser::parse_with(p, &names, &mut Vec::new()).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::rust_vars::in_default_run(|| {
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
        crate::rust_vars::in_default_run(|| go(&passes.prepass, vec![Cand::new(SUB, "input")], &env).unwrap())
    }

    #[test]
    fn pipeline_arguments_are_closures() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let f = "(def (f p) (save t) | p | (union id (load t)))";
        assert_eq!(step(&format!("{f} prepass=(save t) | rewrite | (f (load t))")), [SUB, XOR], "the argument reads the caller's register, the body its own");
        assert_eq!(step("(def (f p) p | none) prepass=rewrite | (f (save s)) | (load s)"), [XOR], "and writes the caller's");
        let nested = "(def (g q) (save u) | none | q) (def (h p) (save u) | none | (g (union (load u) p)))";
        assert_eq!(step(&format!("{nested} prepass=(save t) | rewrite | (h (load t))")), [XOR, SUB], "a parameter in an argument is the enclosing call's argument");
        assert_eq!(step("(def (f r p) p | (load r)) prepass=rewrite | (save t) | (f t none)"), [XOR], "a group parameter is the caller's group, by value");
        assert_eq!(step("(def (without n p) (off n) | p) prepass=(without tfunc tfunc)"), [SUB], "a name parameter as a switch");
        assert_eq!(step("prepass=tfunc"), [XOR]);
        let out = prepass_of("(def (named n p) (tag n p)) prepass=(named mine rewrite)");
        assert_eq!(out[0].origin, "mine", "a name parameter as a stats name");
        assert_eq!(step("(def @inline (g r p) p | (load r)) prepass=rewrite | (save s) | (g s none)"), [XOR], "an @inline function shares the caller's group variables");
        assert_eq!(step("(def @inline (g p) split_runs = 3 | p) prepass=(g id) | (if (split_runs == 3) id none)"), [SUB], "and its sequence");
        assert_eq!(step("(def (g p) split_runs = 3 | p) prepass=(g id) | (if (split_runs == 3) id none)"), Vec::<String>::new(), "a def's assignment ends with its run");
        assert_eq!(step("(def (w p) (save s) | (smallest p | (load s))) prepass=(w rewrite)"), [XOR, SUB], "a smallest in a def body notes what a parameter's argument returns");
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
        let passes = Passes::parse("(def (f n) max_leaves = n | check_limits | rewrite) prepass=(f 8)").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let e = crate::rust_vars::in_default_run(|| run(&passes.prepass, vec![Cand::new(SUB, "input")], &env)).unwrap_err();
        assert!(e.to_string().contains("max_leaves is at most 6"), "{e}");
    }

    #[test]
    fn local_variables() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let both = "(union id rewrite)";
        assert_eq!(step("prepass=n = (size - 5) | (fix n rewrite)"), [XOR], "a number local read by fix");
        assert_eq!(step("prepass=n = (size * 2) | (if (n > 20) rewrite)"), [SUB], "and by a condition, evaluated once where it is bound");
        assert_eq!(step("prepass=n = size | rewrite | (if (n > size) relate none)"), [XOR], "n keeps the size of the input");
        assert_eq!(step(&format!("prepass=n = 5 | small:term->num = (size <= n) | n = 0 | {both} | (filter small)")), [XOR], "a closure captures the value the local has when it is bound");
        assert_eq!(step(&format!("prepass=(save t) | small:term->num = (same (main t)) | t = rewrite | {both} | (filter small)")), [SUB], "and a group variable's");
        assert_eq!(step(&format!("(def (under2 k:num) n = (k + 1) | size <= n) prepass={both} | (filter (under2 4))")), [XOR], "a def returning a function that reads its own local");
        let keep_if = "(def @pipe (keep_if pred g) g | (filter pred))";
        assert_eq!(step(&format!("{keep_if} (def (mk k:num) n = (k + 1) | f:term->num = (size <= n) | {both} | (keep_if f)) prepass=(mk 4)")), [XOR], "a closure passed on reads the local of the def it is written in");
        let p = Passes::parse("prepass=n = (size * 2) | f:term->num = (size <= n) | (fix n (filter f))").unwrap();
        assert_eq!(p.prepass.to_string(), "n = size * 2 | f:term->num = size <= n | (fix n (filter f))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let w = Passes::parse_noting("prepass=n = 3 | f:term->num = size | rewrite").unwrap().1;
        assert!(w.iter().any(|w| w.contains("number variable n is bound and never read")) && w.iter().any(|w| w.contains("function variable f is bound and never read")), "{w:?}");
        for (bad, msg) in [("prepass=relate = rewrite", "relate is a variable that holds a number"), ("prepass=n = 1 | n = rewrite", "n is a number variable, so it cannot be bound to candidates"), ("prepass=size = 3", "cannot be assigned")] {
            let e = Passes::parse(bad).err().unwrap_or_else(|| panic!("{bad} parses"));
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn function_values() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let both = "(union id rewrite)";
        let keep_if = "(def @pipe (keep_if pred g) g | (filter pred))";
        assert_eq!(step(&format!("{keep_if} prepass={both} | (keep_if (size <= 5))")), [XOR], "the condition is a function applied to each candidate");
        assert_eq!(step(&format!("prepass=small:term->num = (size <= 5) | {both} | (filter small)")), [XOR], "a stored function value");
        assert_eq!(step(&format!("prepass=f:term->num = size | {both} | (filter (f < 5))")), [XOR], "a stored function applied to the input of the step");
        assert!(step(&format!("prepass=(save t) | f:term->num = size | {both} | (filter ((f t) < 5))")).is_empty(), "or to a group");
        let under = "(def (under k) (size <= k))";
        assert_eq!(step(&format!("{under} prepass={both} | (filter (under 5))")), [XOR], "a def that returns a function");
        assert_eq!(step(&format!("{under} {keep_if} prepass={both} | (keep_if (under 5))")), [XOR]);
        assert_eq!(step(&format!("{under} prepass=(if (under 5) rewrite)")), [SUB], "the same def called in an expression gives a number");
        assert_eq!(step(&format!("{keep_if} (def (f n) small:term->num = (size <= n) | {both} | (keep_if small)) prepass=(f 5)")), [XOR], "a closure reads the frame of the def it is written in");
        assert_eq!(step(&format!("{keep_if} (def (f n) small:term->num = (size <= n) | {both} | (keep_if small)) prepass=(f 9)")), [SUB, XOR]);
        let each = "(def @pipe (each f:term->term g) g | f)";
        assert_eq!(step(&format!("{each} prepass=(each rewrite)")), [XOR], "a built-in without its input is a function value");
        assert_eq!(step("prepass=f:term->term = rewrite | f"), [XOR], "and can be stored");
        assert_eq!(step("(def (with_budget n p) rewrites = n | p) (def @pipe (app p g) g | p) prepass=(app (with_budget 0 rewrite)) | (app (with_budget 8 rewrite))"), [XOR], "a def without its last argument");
        let big = "(def @pipe (big k g) (size (main g)) > k)";
        assert_eq!(step(&format!("{big} {keep_if} prepass={both} | (keep_if (big 5))")), [SUB], "group->num where term->num is wanted: on each candidate alone");
        let when = "(def (when c:group->num p) (if (c > 5) p))";
        assert_eq!(step(&format!("{when} prepass=(when size rewrite)")), [XOR], "term->num where group->num is wanted: on the main candidate");
        assert_eq!(step(&format!("{when} prepass=(when vars rewrite)")), [SUB]);
        let pick = "(def (pick pred) (save t) | (if ((pred t) > 5) rewrite))";
        assert_eq!(step(&format!("{pick} prepass=(pick size)")), [XOR], "a parameter called on a group is a function");
        assert_eq!(step(&format!("{pick} prepass=(pick vars)")), [SUB]);
        let spec = format!("{pick} {under} {each} {keep_if} prepass=f:term->num = (size <= 5) | g:term->term = rewrite | (each g) | (keep_if f) | (filter (under 5)) | (pick size)");
        let p = Passes::parse(&spec).unwrap();
        let sigs: Vec<String> = p.defs[p.default_defs..].iter().map(|d| crate::lang::defs::sig_of(d).decl()).collect();
        assert_eq!(sigs, ["(extern @pipe (pick pred:group->num g:group) group)", "(extern @pipe (under k:num t:term) num)", "(extern @pipe (each f:term->term g:group) group)", "(extern @pipe (keep_if pred:term->num g:group) group)"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "{p}");
        for (bad, msg) in [
            (format!("{each} prepass=(each (best 1 rewrite))"), "each takes f:term->term: (each f:term->term g:group) group; (best 1 rewrite) is pipe"),
            (format!("{keep_if} prepass=f:term->term = rewrite | (keep_if f)"), "keep_if takes pred:term->num: (keep_if pred:term->num g:group) group; f is term->term"),
            (format!("prepass=f:term->num = size | {both} | f"), "| f gives a number, not candidates"),
            (format!("prepass=f:term->num = size | (best 1 f)"), "f gives a number, not candidates: it holds term->num"),
            ("prepass=f:term->term = (best 1 rewrite)".into(), "f holds term->term; (best 1 rewrite) is pipe"),
            ("prepass=f:term->num = size | (save f)".into(), "f is a function variable, so it cannot name a group variable"),
            ("prepass=f = size | (save f)".into(), "f is a number variable, so it cannot name a group variable"),
            ("prepass=f:term->num = size | f = 3".into(), "f is a function variable, so it cannot hold a number"),
            ("prepass=(save f) | f:term->num = size".into(), "f is a group variable, so it cannot hold a function value"),
            ("prepass=keep:term->num = size".into(), "keep"),
            ("prepass=(save f) | f = size".into(), "f is a group variable, so it cannot hold a number"),
            ("(def (f p) (filter p) | (best 1 p))".into(), "parameter p is used as term->num and as pipe"),
        ] {
            let e = Passes::parse(&bad).err().unwrap_or_else(|| panic!("{bad} parses"));
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn group_variables() {

        let step = |spec: &str| terms(&prepass_of(spec));
        assert_eq!(step("prepass=t = (lowbits | unshift) | (filter (size == (size (main t)))) | (load t)"), [SUB]);
        assert_eq!(step("prepass=t = rewrite"), [SUB], "the input passes on");
        assert_eq!(step("prepass=t = rewrite | (load t)"), [XOR]);
        assert_eq!(step("prepass=t = rewrite | (filter (size > (size (main t)) && !(same (main t))))"), [SUB]);
        assert_eq!(step("prepass=rewrite | t = id | none | (load t)"), step("prepass=rewrite | (save t) | none | (load t)"), "(save t) is t = id");
        assert_eq!(step("prepass=t = (relate = 0 | rewrite) | t = (union (load t) id) | (load t)"), [XOR, SUB]);
        assert_eq!(step("(def (f) t = rewrite | (load t)) prepass=t = id | f | none | (load t)"), [SUB], "a def binds its own group variables");
        assert_eq!(step("(def (f) rewrite) prepass=t = f | (load t)"), [XOR]);
        assert_eq!(step("(def (f p) p | none) prepass=(f t = rewrite) | (load t)"), [XOR], "an argument binds the caller's");
        assert_eq!(step("(def (f r p) u = (r | p) | (load u)) prepass=(save t) | (f t rewrite)"), [XOR], "a group parameter as a value");
        assert_eq!(step("(def @inline (g p) u = p) prepass=(g rewrite) | (load u)"), [XOR], "an @inline function binds the caller's");
        assert_eq!(step("prepass=(smallest t = rewrite)"), [XOR, SUB], "smallest notes the steps of a right side");
        assert_eq!(step("prepass=time_limit = 0 | t = rewrite | (load t)"), [SUB], "past the limit the right side's steps are skipped");
        assert_eq!(step("prepass=rewrite | t = id | u = t | none | (load u)"), [XOR], "a group variable on the right side");
        assert_eq!(step("(def (f r) u = r | (load u)) prepass=rewrite | (save t) | (f t)"), [XOR]);
        assert_eq!(step("prepass=t = (off tfunc) | tfunc"), [XOR], "the right side is a scope");
        assert_eq!(step("prepass=(off tfunc) | tfunc"), [SUB]);
        assert_eq!(step("prepass=t = (split_runs = 3 | id) | (if (split_runs == 3) none)"), [SUB]);
    }

    #[test]
    fn explicit_inputs_and_function_values() {
        let step = |spec: &str| terms(&prepass_of(spec));
        let f = "(def @pipe (f p g) g | p)";
        assert_eq!(step(&format!("{f} prepass=(f rewrite)")), [XOR], "| fills in the input");
        assert_eq!(step(&format!("{f} prepass=rewrite | (save t) | none | (f id t)")), [XOR], "an explicit input");
        assert_eq!(step(&format!("{f} prepass=rewrite | (save t) | none | (t | (f id))")), [XOR], "a pipeline starting with a value");
        let twice = "(def (twice p g) (p (p g)))";
        assert_eq!(step(&format!("{twice} prepass=(save t) | u = (twice rewrite t) | (load u)")), [XOR], "a function value called as (p g)");
        assert!(Passes::parse(&format!("{twice} prepass=(save t) | (twice rewrite t)")).unwrap_err().contains("twice is not @pipe"), "a function without @pipe after |");
        let big = "(def @pipe (big k g) (size (main g)) > k)";
        assert_eq!(step(&format!("{big} prepass=(if (big 5) rewrite)")), [XOR], "a function giving a number, its input the step's");
        assert_eq!(step(&format!("{big} prepass=(if (big 9) rewrite)")), [SUB]);
        assert_eq!(step(&format!("{big} prepass=rewrite | (save t) | none | (if (big 2 t) (load t))")), [XOR], "its input written");
        assert_eq!(step(&format!("{big} prepass=(filter (big 9))")), Vec::<String>::new());
        assert_eq!(step("(def @pipe (m g) (mixed (main g)) || (size (main g)) > 100) prepass=(if (m) rewrite)"), [SUB]);
        assert_eq!(step("(def (k n:num) split_runs = n | (if (split_runs == 3) rewrite)) prepass=(k 3)"), [XOR], "an annotated parameter");
        assert_eq!(step(&format!("{f} prepass=(f rewrite (lowbits | unshift))")), [XOR], "an input that is a pipeline on the step's input");
        assert_eq!(step(&format!("{f} (def (h a:group) (f id a)) prepass=rewrite | (save t) | none | u = (h t) | (load u)")), [XOR], "a group parameter as an input");
        assert_eq!(step("prepass=(if ((size (main (rewrite))) < size) rewrite)"), [XOR], "an input of a number function");
        let k = "(def @inline @pipe (k p g) g | p | (union id g))";
        assert_eq!(step(&format!("{k} prepass=(k rewrite)")), [XOR, SUB], "@inline with @pipe: the input bound in the caller's group variables");
        assert_eq!(step(&format!("{k} prepass=(k (k rewrite))")), [XOR, SUB], "each call binds its own");
        assert_eq!(step(&format!("{k} prepass=rewrite | (save t) | none | (k id t)")), [XOR], "an explicit input");
        assert_eq!(step("(def @inline @pipe (k g) g | (save u)) prepass=rewrite | k | none | (load u)"), [XOR], "it shares the caller's group variables");
    }

    #[test]
    fn pipelines_that_give_a_number() {
        let step = |spec: &str| terms(&prepass_of(spec));
        assert_eq!(step("prepass=(if ((rewrite | size) < size) rewrite)"), [XOR], "steps on the input, then a number");
        assert_eq!(step("prepass=(if ((rewrite | size) > size) rewrite)"), [SUB]);
        assert_eq!(step("prepass=split_runs = (rewrite | size) | (if (split_runs < size) rewrite)"), [XOR], "an assignment's right side");
        assert_eq!(step("prepass=(if ((t = rewrite | size) > 0) (load t))"), [XOR], "its steps bind the caller's group variables");
        assert_eq!(step("prepass=rewrite | (save t) | none | (if ((t | size) > 0) (load t))"), [XOR], "starting with a value");
        assert_eq!(step("prepass=(filter ((rewrite | size) < size))"), [SUB], "on each candidate alone");
        assert_eq!(step("prepass=(fix ((rewrite | size) - 2) id)"), [SUB]);
        assert_eq!(step("(def (f) rewrite | size) prepass=(if (f < size) rewrite)"), [XOR], "a function that gives a number from steps");
        assert_eq!(step("(def @pipe (f g) g | rewrite | size) prepass=(if (f < size) rewrite)"), [XOR]);
        assert_eq!(step("(def (f) (save t) | size) prepass=rewrite | (save t) | none | (if (f == 0) (load t))"), [XOR], "a run of its own: its own group variables");
        assert_eq!(step("prepass=(save s) | (smallest split_runs = (rewrite | size) | (load s))"), [XOR, SUB], "smallest notes its steps");
        assert_eq!(step("(def (f) rewrite | size) prepass=(save s) | (smallest split_runs = f | (load s))"), [SUB], "but not those of a function's body");
        assert_eq!(step("prepass=time_limit = 0 | split_runs = (rewrite | size) | time_limit = none | (if (split_runs == size) rewrite)"), [XOR], "past the limit its steps are skipped");
    }

    #[test]
    fn smallest_keeps_the_first_strictly_smallest_returned() {
        let passes = Passes::parse("(def (f p) p | none) (def @inline (g n) (if (n == 1) rewrite) | none)").unwrap();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let mut names = crate::lang::defs::Defs::new();
        for d in &passes.defs {
            names.insert(d.name.clone(), crate::lang::defs::Named { pipe: crate::lang::defs::Call::bare(d), flat: d.flat, run: !d.inline, params: d.params.clone(), def: Some(d.clone()) });
        }
        let on = |p: &str, set: Vec<Cand>| terms(&go(&crate::lang::parser::parse_with(p, &names, &mut Vec::new()).unwrap(), set, &env).unwrap());
        let step = |p: &str| on(p, vec![Cand::new(SUB, "input")]);
        let xor2 = "(Xor (Var \"y\") (Var \"x\"))";
        crate::rust_vars::in_default_run(|| {
            assert_eq!(step("(save s) | (smallest rewrite | none | (load s))"), [XOR, SUB]);
            assert_eq!(step("(smallest rewrite | none)"), Vec::<String>::new(), "an empty result stays empty");
            assert_eq!(step("(smallest none)"), Vec::<String>::new());
            assert_eq!(step("(smallest id)"), [SUB], "the input is not noted");
            assert_eq!(step("(save s) | (smallest (smallest rewrite | none | (load s)) | none | (load s))"), [XOR, SUB], "nested: the outer one sees the inner steps");
            assert_eq!(step("(save s) | (smallest (f rewrite) | (load s))"), [XOR, SUB], "an argument of a def is noted where it is written");
            assert_eq!(step("(save s) | (smallest (g 1) | (load s))"), [XOR, SUB], "an @inline body is noted");
            on("(clear r) | (note r)", vec![Cand::new(XOR, "input")]);
            assert_eq!(on("(take_min r)", vec![Cand::new(xor2, "input")]), [xor2], "take_min needs a strictly smaller candidate");
            on("(clear r) | (note r)", vec![Cand::new(xor2, "input"), Cand::new(XOR, "input")]);
            on("(note r)", vec![Cand::new(XOR, "input")]);
            assert_eq!(on("(take_min r)", vec![Cand::new(SUB, "input")]), [xor2, SUB], "the first smallest is kept");
            assert_eq!(on("(take_min r)", vec![Cand::new(SUB, "input")]), [SUB], "take_min closes the register");
            assert_eq!(on("(note r) | (take_min r)", vec![Cand::new(XOR, "input")]), [XOR], "a note without clear keeps nothing");
            on("(clear r) | (note r) | (clear r)", vec![Cand::new(XOR, "input")]);
            assert_eq!(on("(take_min r)", vec![Cand::new(SUB, "input")]), [SUB], "a clear of an open name opens another");
            assert_eq!(on("(take_min r)", vec![Cand::new(SUB, "input")]), [XOR, SUB]);
            let both = || vec![Cand::new(SUB, "input"), Cand::new(XOR, "input")];
            assert_eq!(on("(smallest (save b) | rewrite | none | (load b))", both()), [XOR, SUB], "the smallest candidate of a group a step returns is noted");
            assert_eq!(on("(smallest time_limit = 0 | rewrite)", both()), [SUB, XOR], "past the time limit note is skipped too");
        });
    }

    #[test]
    fn wins_zero_runs_nothing() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let step = |p: &str| terms(&go(&crate::lang::parser::parse(p).unwrap(), vec![Cand::new(SUB, "input")], &env).unwrap());
        crate::rust_vars::in_default_run(|| {
            assert_eq!(step("(wins 0 (smaller s rewrite))"), [SUB]);
            assert_eq!(step("(wins 0 none)"), [SUB]);
            assert_eq!(step("(wins 1 (smaller s rewrite))"), [XOR]);
        });
    }

    #[test]
    fn functions_give_zero_on_no_candidates() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::rust_vars::in_default_run(|| {
            for f in ["size", "mul", "vars", "mixed", "input", "moved", "tiny", "(size (main r))", "(same (main r))", "(any 1)", "(all 1)"] {
                assert_eq!(env.value(&expr(f), &[]), 0, "{f}");
            }
            assert_eq!(env.value(&expr("!tiny"), &[]), 1);
            assert_eq!(env.value(&expr("size < (size (main r)) + 1"), &[]), 1, "a comparison compares the zeros");
            assert_eq!(env.value(&expr("size > (size (main r))"), &[]), 0);
            let x = [Cand::new(SUB, "input")];
            assert_eq!(env.value(&expr("(size (main r))"), &x), 0, "an empty register");
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
        crate::rust_vars::in_default_run(|| {
            let v = |s: &str, set: &[Cand]| env.value(&expr(s), set);
            assert_eq!(v("mul", &mul), 2);
            assert_eq!(v("(mul >= 1) + (vars == 2) * 4", &mul), 5);
            assert_eq!(v("!3", &x), 0);
            assert_eq!(v("!!3", &x), 1);
            assert_eq!(v("2 && 5", &x), 1);
            assert_eq!(v("0 || 7", &x), 1);
            assert_eq!(v("vars * (mixed || 1)", &x), 2);
            let step = |p: &str, set: &[Cand]| go(&crate::lang::parser::parse(p).unwrap(), set.to_vec(), &env).unwrap().len();
            assert_eq!(step("(if mul none)", &mul), 0, "a number holds where it is not 0");
            assert_eq!(step("(if mul none)", &x), 1);
            assert_eq!(step("(fix (mul < 1) rewrite) | (filter (size == 5))", &x), 0, "a comparison counts as 1");
        });
    }

    #[test]
    fn none_in_arithmetic() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::rust_vars::in_default_run(|| {
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
    fn time_limit_skips_only_timed_calls() {
        let passes = Passes::default();
        let x = "(Sub (Or (Var \"x\") (Var \"y\")) (And (Var \"x\") (Var \"y\")))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let step = |p: &str, set: Vec<Cand>| -> Vec<String> {
            go(&crate::lang::parser::parse(p).unwrap(), set, &env).unwrap().iter().map(|c| c.term().to_string()).collect()
        };
        let input = || vec![Cand::new(x, "input")];
        crate::rust_vars::in_default_run(|| {
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"]);
            step("(save t)", input());
            step("time_limit = 1", input());
            std::thread::sleep(std::time::Duration::from_millis(5));
            assert_eq!(step("rewrite", input()), [x], "work past the limit is skipped");
            assert_eq!(step("(load t) | (filter 1)", vec![]), [x], "untimed functions still run");
            assert_eq!(step("time_limit = none | rewrite", input()), [x], "a clear restores the limit outside its sequence");
            step("time_limit = none", input());
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"], "a clear lets the rest run");
        });
    }
}
