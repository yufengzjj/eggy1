//! Runs an `ast::Pipe`. Every step maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another; an expression gives a number for a list. A built-in
//! function runs through its entry of `builtins::BUILTINS`, which converts the input as its
//! calling kind says (`types::Kind`): a pass over one term (`linear_mba::TERM_PASSES`, the polish
//! passes as `polish_NAME`) runs on each candidate and replaces it by its result, the other
//! steps take the list whole.

use super::ast::{Fun, Holds, Pipe, Slot};
use super::builtins::{Builtin, Impl, Operator};
use super::host::{self, Cand, Ctx, Error, Fns, Passes, Won, skipped, term_pass};
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
    /// input written or on the first element of `set`.
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
        deeper(|| super::ast::show(f), || {
            let outer = self.lex.replace(lex);
            let out = match number {
                true => Ok(Value::Num(self.value(f, input.slice()))),
                false => go(f, input.vec(), self).map(Value::Group),
            };
            self.lex.replace(outer);
            out
        })
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
                let v = match steps {
                    [Pipe::Var(Slot::Local(r, Holds::Group))] => Value::Group(self.reg(r)),
                    steps => scoped(|| run_seq(steps, Value::Group(set.to_vec()), self)).unwrap_or_else(|e| {
                        fail(&e);
                        Value::Group(Vec::new())
                    }),
                };
                match v {
                    Value::Group(g) => self.value(e, &g),
                    v => step_on(e, v, self).map_or_else(
                        |e| {
                            fail(&e);
                            0
                        },
                        Value::num,
                    ),
                }
            }
            Pipe::App(Fun::Def(c), args) => {
                let c = &c.latest(args, &self.passes.defs);
                let input = args.get(c.def.params.len()).map(|p| self.group_of(p, set));
                let set = input.as_deref().unwrap_or(set);
                let v = deeper(|| c.def.name.clone(), || {
                    if c.def.steps {
                        let run = self.call_env(c, args, set);
                        return Ok(scoped(|| run.value(c.def.value.as_ref().unwrap(), set)));
                    }
                    let caller = self.lex.borrow().clone();
                    let frame = Frame { call: c.clone(), args: args.clone(), caller: caller.clone(), values: arg_values(c, args, set, self) };
                    let lex = Lex { input: caller.input.clone(), regs: Default::default(), notes: caller.notes.clone(), frame: Some(frame) };
                    bind_args(c, args, &lex, set, &caller, self);
                    let outer = self.lex.replace(Rc::new(lex));
                    let v = self.value(c.def.value.as_ref().expect("a function whose body is an expression"), set);
                    self.lex.replace(outer);
                    Ok(v)
                });
                v.unwrap_or_else(|e| {
                    fail(&e);
                    0
                })
            }
            e => unreachable!("{e:?} gives no number"),
        }
    }

    /// The candidates `p` gives on `set`: a group value, or steps of this run; none after an
    /// error, which the run then gives.
    pub(crate) fn group_of(&self, p: &Pipe, set: &[Cand]) -> Vec<Cand> {
        match p {
            Pipe::Var(Slot::Local(r, Holds::Group)) => self.reg(r),
            Pipe::Seq(ps) if matches!(&ps[..], [Pipe::Var(Slot::Local(_, Holds::Group)), first] if is_first(first)) => match &ps[0] {
                Pipe::Var(Slot::Local(r, _)) => self.reg_main(r).into_iter().collect(),
                _ => unreachable!(),
            },
            p if is_first(p) => set.first().cloned().into_iter().collect(),
            Pipe::Expanded(m) if m.is_call() && m.steps.len() == 1 => self.group_of(&m.steps[0], set),
            p => scoped(|| go(p, set.to_vec(), self)).unwrap_or_else(|e| {
                fail(&e);
                Vec::new()
            }),
        }
    }

    /// The run of a call of `c` on `set`, with its own group variables and the call's arguments.
    fn call_env(&self, c: &std::sync::Arc<super::defs::Call>, args: &std::sync::Arc<[Pipe]>, set: &[Cand]) -> Env<'a> {
        let run = self.run_env(set);
        if !args.is_empty() || c.def.input.is_some() {
            let caller = self.lex.borrow().clone();
            let frame = Frame { call: c.clone(), args: args.clone(), caller: caller.clone(), values: arg_values(c, args, set, self) };
            let lex = Lex::new(&run.lex.borrow().input, Some(frame));
            bind_args(c, args, &lex, set, &caller, self);
            run.lex.replace(lex);
        }
        run
    }

    /// The run of a call on `set` without arguments.
    fn run_env(&self, set: &[Cand]) -> Env<'a> {
        let input = set.first().map_or_else(String::new, |c| c.term().to_string());
        let mut run = Env::with(self.passes, self.w, self.signed, self.trace, &input);
        run.cofactor = self.cofactor;
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

/// Whether `p` is `(index 0)` on the step's input, the expansion of `main`.
fn is_first(p: &Pipe) -> bool {
    matches!(p, Pipe::App(Fun::Builtin(b), a) if b.name == "index" && matches!(&a[..], [Pipe::Num(0)]))
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

/// The deepest nesting of calls (of `def`s, function values and the functions a pass runs) a
/// program may reach; past it the run ends with an error. Programs nest calls about as deep as
/// the terms they rebuild (128 at most over the deep, Tigress and LLVM data).
pub const MAX_DEPTH: u32 = 2000;

/// The stack a call needs left, else it continues on a new one of `STACK_SEGMENT` bytes: more
/// than the work between two nested calls takes (an egglog run, a pass), which ran on 1 MB
/// stacks (a Windows main thread) before.
const RED_ZONE: usize = 1 << 20;
const STACK_SEGMENT: usize = 8 << 20;

thread_local! {
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

/// `f` one call deeper, the call one of `name`; past `MAX_DEPTH` the error that ends the run.
pub(crate) fn deeper<R>(name: impl FnOnce() -> String, f: impl FnOnce() -> Result<R, Error>) -> Result<R, Error> {
    struct Up;
    impl Drop for Up {
        fn drop(&mut self) {
            DEPTH.with(|d| d.set(d.get() - 1));
        }
    }
    if DEPTH.with(|d| d.replace(d.get() + 1)) >= MAX_DEPTH {
        DEPTH.with(|d| d.set(d.get() - 1));
        return Err(Error::BackendError(format!("recursion deeper than {MAX_DEPTH} calls in {}", name())));
    }
    let _up = Up;
    stacker::maybe_grow(RED_ZONE, STACK_SEGMENT, f)
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
/// that is not `@uncounted` and is no combinator of pipelines (a pass given functions is not
/// one), or of a `def` that is not `inline`.
pub(crate) fn computes(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => b.timed && !b.uncounted && (b.sig.kind() != super::types::Kind::Group || !b.sig.params.iter().any(|q| q.ty.is_step())),
        Pipe::App(Fun::Def(c), _) => !c.def.inline,
        _ => false,
    }
}

/// What a step of a sequence passes on.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum StepKind {
    /// Candidates.
    Group,
    /// A number or a text.
    Value,
    /// Nothing of its own: the value it is given (`print`, assignments, switches).
    Nothing,
}

pub(crate) fn step_kind(p: &Pipe) -> StepKind {
    match p {
        Pipe::Bind(..) => StepKind::Nothing,
        Pipe::Expanded(m) if m.switch_names().is_some() => StepKind::Nothing,
        Pipe::App(Fun::Builtin(b), _) if b.sig.kind() == super::types::Kind::Effect => StepKind::Nothing,
        Pipe::Text(_) => StepKind::Value,
        Pipe::App(Fun::Builtin(b), _) if b.sig.is_text() => StepKind::Value,
        Pipe::Seq(ps) => match ps.iter().rev().map(step_kind).find(|k| *k != StepKind::Nothing) {
            Some(StepKind::Value) => StepKind::Value,
            Some(_) => StepKind::Group,
            None => StepKind::Nothing,
        },
        p if super::flow::is_expr(p) => StepKind::Value,
        _ => StepKind::Group,
    }
}

/// The steps `ps` in turn, each on the value the one before gives.
pub(crate) fn run_seq(ps: &[Pipe], v: Value, env: &Env) -> Result<Value, Error> {
    ps.iter().try_fold(v, |v, p| step_on(p, v, env))
}

/// The step `p` on the value `v` the step before gave: candidates go to `p` as they are, a
/// number or a text is the input of the function `p` calls without it, and a step that gives
/// nothing passes `v` on.
pub(crate) fn step_on(p: &Pipe, v: Value, env: &Env) -> Result<Value, Error> {
    match (step_kind(p), v) {
        (StepKind::Group | StepKind::Nothing, Value::Group(g)) => go(p, g, env).map(Value::Group),
        (StepKind::Nothing, v) => {
            go(p, Vec::new(), env)?;
            Ok(v)
        }
        (StepKind::Value, Value::Group(g)) => {
            let v = match p {
                Pipe::Text(_) => Value::Text(env.text_of(p, &g)?),
                Pipe::App(Fun::Builtin(b), _) if b.sig.is_text() => Value::Text(env.text_of(p, &g)?),
                p => Value::Num(env.value(p, &g)),
            };
            failed().map_or(Ok(v), Err)
        }
        (kind, v) => {
            let input = match v {
                Value::Num(n) => Pipe::Num(n),
                Value::Text(t) => Pipe::Text(t),
                _ => unreachable!("a step is given candidates, a number or a text"),
            };
            let Pipe::App(f, args) = p else { unreachable!("{p:?} takes no number or text") };
            let call = Pipe::App(f.clone(), args.iter().cloned().chain([input]).collect());
            match kind {
                StepKind::Group => go(&call, Vec::new(), env).map(Value::Group),
                _ => step_on(&call, Value::Group(Vec::new()), env),
            }
        }
    }
}

pub(crate) fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Steps {
    // Every candidate equals the input, so stopping anywhere keeps the result right.
    if let Some(e) = failed() {
        return Err(e);
    }
    let late = match p {
        Pipe::App(Fun::Def(c), _) if c.def.late() => Some(c.latest_def(&env.passes.defs)),
        _ => None,
    };
    if late.map_or_else(|| timed(p), |d| d.timed) && past(0.0) {
        if !uncounted(p) {
            skipped(env);
        }
        return Ok(set);
    }
    match p {
        Pipe::App(Fun::Builtin(b), args) => apply(b, args, In::Own(set), env).map(Value::group),
        Pipe::Seq(ps) => match scoped(|| run_seq(ps, Value::Group(set), env))? {
            Value::Group(g) => Ok(g),
            _ => Err(Error::BackendError(format!("{} gives a number or a text where a group is wanted", super::ast::show(p)))),
        },
        Pipe::Expanded(m) => {
            let steps = || m.steps.iter().try_fold(set, |s, p| go(p, s, env));
            if m.scoped { scoped(steps) } else { steps() }
        }
        Pipe::App(Fun::Def(c), _) if c.def.implicit == Some(Ty::Term) && c.def.value.is_none() && set.len() > 1 => {
            let mut out = Vec::new();
            for t in &set {
                out.extend(kept(go(p, vec![t.clone()], env)?, std::slice::from_ref(t)));
            }
            Ok(dedup(out))
        }
        Pipe::App(Fun::Def(c), args) if c.def.inline => deeper(|| c.def.name.clone(), || {
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
        }),
        Pipe::App(Fun::Def(c), args) => {
            let d = late.unwrap_or(&c.def);
            deeper(|| d.name.clone(), || {
                // Without arguments or input a call has no frame, and its body is the definition's.
                if args.is_empty() && d.input.is_none() {
                    let run = env.run_env(&set);
                    return scoped(|| go(&d.body, set, &run));
                }
                let c = c.latest(args, &env.passes.defs);
                let run = env.call_env(&c, args, &set);
                scoped(|| go(&c.body, set, &run))
            })
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
pub(crate) fn reads(p: &Pipe, names: &mut Vec<String>, params: &mut Vec<usize>) {
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
        Pipe::Num(_) | Pipe::Text(_) | Pipe::Var(Slot::Global(_)) | Pipe::FnValue(_) => {}
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
        Impl::Each(f) => {
            let fns = Fns::of(b, args, env);
            dedup(term_pass(fns.name, |t, w| f(t, w, &fns), None, &set, env))
        }
        Impl::Alt(f, bit) => {
            let fns = Fns::of(b, args, env);
            dedup(term_pass(fns.name, |t, w| f(t, w, &fns), Some(bit), &set, env))
        }
        Impl::Polish(f) => {
            let fns = Fns::of(b, args, env);
            dedup(term_pass(fns.name, |t, w| Some(f(t, w, &fns)), None, &set, env))
        }
        Impl::Join(f) => match &set[..] {
            [one] => kept(f(args, one, env)?, &set),
            set => {
                let mut out = Vec::new();
                for c in set {
                    out.extend(kept(f(args, c, env)?, std::slice::from_ref(c)));
                }
                dedup(out)
            }
        },
        Impl::EachCand(_) if set.is_empty() => set,
        Impl::EachCand(f) => kept(set.iter().map(|c| f(args, c, env).unwrap_or_else(|| c.clone())).collect(), &set),
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
/// variables, its term parameters to the first term their arguments give on `set` in the
/// caller's run `env`, and its input parameter to `set`.
fn bind_args(c: &super::defs::Call, args: &[Pipe], lex: &Lex, set: &[Cand], caller: &Lex, env: &Env) {
    let terms: Vec<(String, Vec<Cand>)> = c.def.params.iter().zip(args).filter(|(p, _)| p.ty == Ty::Term).map(|(p, a)| (p.name.clone(), env.group_of(a, set).into_iter().take(1).collect())).collect();
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
    for (n, t) in terms {
        regs.insert(n, Value::Group(t));
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

    /// `s` parsed with the names `default.pipe` defines, as a pipeline on one term.
    fn parse_default(s: &str) -> Pipe {
        crate::lang::parser::parse_on(s, &crate::passes::DEFAULT.1, &mut Vec::new(), crate::lang::flow::Flow::One).unwrap()
    }

    #[test]
    fn print_and_assert_read_back() {
        let p = Passes::parse("prepass=main | (print \"a \\\"b\\\" c\" 1) | (assert 1 \"x;y z\")").unwrap();
        assert_eq!(crate::lang::ast::show(&p.prepass()), "main | (print \"a \\\"b\\\" c\" 1) | (assert 1 \"x;y z\")");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "strings are written back as read");
        let p = Passes::parse("prepass=main | f:term->num = size | (print f rewrite)").unwrap();
        let Pipe::Seq(steps) = &p.prepass() else { panic!() };
        let Pipe::App(_, args) = &steps[2] else { panic!() };
        assert!(matches!(&args[0], Pipe::Var(Slot::Local(n, Holds::Fn(_))) if n == "f") && matches!(&args[1], Pipe::App(Fun::Def(c), a) if c.def.name == "rewrite" && a.is_empty()));
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
    fn switches_reach_the_runs_started_inside() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, "(Var \"x\")");
        let step = |p: &str| go(&parse_default(p), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
        use crate::rust_vars::is_off;
        crate::rust_vars::in_default_run(|| {
            step("(off relate tfunc)");
            step("(on relate)");
            assert!(crate::lang::run::within(&passes, || !is_off("relate") && is_off("tfunc")), "a run started here keeps them");
            crate::rust_vars::with_off(&["relate"], || {
                assert!(is_off("relate"));
                step("(on relate)");
                assert!(!is_off("relate"));
            });
            assert!(!is_off("relate"));
            step("(on cut)");
        });
        assert!(crate::lang::vars::get(crate::rust_vars::CUT) == crate::lang::vars::NONE && !is_off("tfunc"));
    }

    #[test]
    fn cand_is_defined_in_the_language() {
        let x = "(Sub (Var \"x\") (Var \"y\"))";
        let run = |spec: &str| {
            let p = Passes::parse(&format!("prepass=main | {spec}")).unwrap();
            let env = Env::prepass(&p, 32, None, false, x);
            PRINTED.with(|l| l.borrow_mut().clear());
            let out = crate::lang::run::within(&p, || go(&p.prepass(), vec![Cand::new(x, "input")], &env).unwrap());
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
    fn run_settings_come_from_the_command_line() {
        use crate::lang::vars::{NONE, get, var_index};
        use crate::rust_vars::RESTARTS;
        let passes = Passes::default();
        let x = "(Sub (Var \"x\") (Var \"y\"))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let extra = var_index("extra").unwrap();
        crate::lang::run::within(&passes, || {
            go(&parse_default("extra = 0"), vec![Cand::new(x, "input")], &env).unwrap();
            assert_eq!(get(extra), 0);
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
        let step = |p: &str| go(&parse_default(p), vec![Cand::new("(Var \"x\")", "input")], &env).unwrap();
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

    /// The elements `prepass` gives for `SUB` where `spec` defines it.
    fn prepass_of(spec: &str) -> Vec<Cand> {
        let passes = Passes::parse(spec).unwrap_or_else(|e| panic!("{spec}: {e}"));
        let env = Env::prepass(&passes, 32, None, false, SUB);
        crate::rust_vars::in_default_run(|| go(&passes.prepass(), vec![Cand::new(SUB, "input")], &env).unwrap())
    }

    #[test]
    fn a_name_parameter_names_the_origin() {
        let out = prepass_of("(def (named n p) (tag n p)) prepass=main | (named mine rewrite)");
        assert_eq!(out[0].origin, "mine", "a name parameter as a stats name");
    }

    #[test]
    fn locals_and_function_values_read_back() {
        let p = Passes::parse("prepass=main | n = (size * 2) | f:term->num = (size <= n) | (fix n (filter f))").unwrap();
        assert_eq!(p.prepass().to_string(), "main | n = size * 2 | f:term->num = size <= n | (fix n (filter f))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let spec = "(def (pick pred) (save t) | (if ((pred t) > 5) rewrite)) (def (under k) (size <= k)) (def (each f:term->term g:group) g | f) (def (keep_if pred g:group) g | (filter pred)) prepass=main | f:term->num = (size <= 5) | g:term->term = (rewrite_top rewrite) | (each g) | (keep_if f) | (filter (under 5)) | (pick (size main))";
        let p = Passes::parse(spec).unwrap();
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "{p}");
    }

    #[test]
    fn none_as_a_count_is_no_limit() {
        let passes = Passes::default();
        let env = Env::prepass(&passes, 32, None, false, SUB);
        let Pipe::App(_, args) = crate::lang::parser::parse("(filter none)").unwrap() else { unreachable!() };
        crate::rust_vars::in_default_run(|| assert_eq!(env.times(&args[0], &[]), usize::MAX));
    }

    #[test]
    fn time_limit_skips_only_timed_calls() {
        let passes = Passes::default();
        let x = "(Sub (Or (Var \"x\") (Var \"y\")) (And (Var \"x\") (Var \"y\")))";
        let env = Env::prepass(&passes, 32, None, false, x);
        let step = |p: &str, set: Vec<Cand>| -> Vec<String> {
            go(&parse_default(p), set, &env).unwrap().iter().map(|c| c.term().to_string()).collect()
        };
        let input = || vec![Cand::new(x, "input")];
        crate::rust_vars::in_default_run(|| {
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"]);
            step("(save t)", input());
            step("time_limit = 1", input());
            std::thread::sleep(std::time::Duration::from_millis(5));
            assert_eq!(step("rewrite", input()), [x], "work past the limit is skipped");
            assert_eq!(step("(save t) | none | (seq t) | (filter 1)", input()), [x], "untimed functions still run");
            assert_eq!(step("time_limit = none | rewrite", input()), [x], "a clear restores the limit outside its sequence");
            step("time_limit = none", input());
            assert_eq!(step("rewrite", input()), ["(Xor (Var \"x\") (Var \"y\"))"], "a clear lets the rest run");
        });
    }
}
