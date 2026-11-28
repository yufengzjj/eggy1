//! The parser of the pipeline language (`docs/lang/`): `a | b` runs `b` on the
//! candidates of `a`, `(FORM args...)` is a combinator or a pass with arguments, `NAME = VALUE`
//! assigns a variable, conditions are expressions (`(if (mul >= 4 && shift < 1) (off
//! small_blocks))`). Parsed into `ast::Pipe`, names resolved by their signatures.

use super::ast::{Fun, Holds, Pipe, Slot, show, show_expr, stage, starts_with_value};
use super::builtins::{MACROS, get, number_names, resolve, step_names};
use super::defs::{Call, Def, Defs, def_sig};
use super::infer::ParamUse;
use super::host::FEATURES;
use super::lexer::{NO_EXTERN, Tok, lex, name_char, name_start, show_tok};
use super::macros::smallest;
use super::types::{Kind, Param, Rep, Sig, Ty};
use super::run::{Gives, Top};
use super::vars::{NONE, is_switch, var_index};
use std::sync::Arc;

const NO_WITH: &str = "(with KEY=VALUE ... p) is no longer read: write (KEY = VALUE | ... | p), as in (rewrites = 8 | semi_leaves = 2 | rewrite); with's bit_splits=N is bit_split_budget = N";
const NO_TIME_LIMIT: &str = "(time-limit N) is no longer read: write time_limit = N, or time_limit = none for no limit";
const NO_TRUE: &str = "true is no longer a condition: write 1, or (any 1) for true only on a group that is not empty";

/// An argument of a call, as its parameter's type reads it.
#[derive(Clone)]
pub(crate) enum Arg {
    Num(Pipe),
    Name(String),
    Pipe(Pipe),
    Pipes(Vec<Pipe>),
    Absent,
}

/// The application of the built-in function `f` to the arguments read by its parameters:
/// for `seq` a sequence, for `smallest` the macro expanded, for `if` without its second
/// branch `id` there; `None` when no Rust code implements `f`.
fn construct(f: &str, args: Vec<Arg>) -> Option<Pipe> {
    let b = super::builtins::builtin(f).filter(|b| !matches!(b.imp, super::builtins::Impl::Missing))?;
    let mut out = Vec::with_capacity(args.len());
    for a in args {
        match a {
            Arg::Num(e) | Arg::Pipe(e) => out.push(e),
            Arg::Name(n) => out.push(Pipe::Name(n)),
            Arg::Pipes(ps) => out.extend(ps),
            Arg::Absent if f == "if" => out.push(Pipe::id()),
            Arg::Absent => {}
        }
    }
    Some(match f {
        "seq" => Pipe::Seq(out),
        "smallest" => smallest(out.pop().unwrap()),
        _ => Pipe::App(Fun::Builtin(b), out.into()),
    })
}

/// The group variable `n` read: its candidates.
pub(crate) fn group(n: String) -> Pipe {
    Pipe::Var(Slot::Local(n, Holds::Group))
}

fn param_var(i: usize, n: String) -> Pipe {
    Pipe::Var(Slot::Param(i, n))
}

/// The operator `op` applied to its operands.
pub(crate) fn op(op: &str, args: Vec<Pipe>) -> Pipe {
    Pipe::app(op, args)
}

fn unimplemented(s: &Sig) -> String {
    format!("{s} is declared in src/builtins.pipe but nothing implements it")
}

/// The expression a name stands for: a variable, a function of the candidates or `none`.
fn name_expr(n: &str) -> Result<Pipe, String> {
    if let Some(s) = get(n).filter(|s| s.is_number()) {
        if s.required() {
            return Err(format!("{n} needs parentheses: ({n} ...); {s}"));
        }
        return construct(n, vec![Arg::Absent; s.params.len()]).ok_or_else(|| unimplemented(s));
    }
    if let Some(i) = var_index(n) {
        Ok(Pipe::global(i))
    } else if n == "none" {
        Ok(Pipe::Num(NONE))
    } else if n == "true" {
        Err(NO_TRUE.into())
    } else if let Some(s) = get(n) {
        Err(format!("{n} gives a group, not a number: {s}; an expression reads variables and number functions"))
    } else {
        Err(format!("unknown name {n} in an expression; known: {} and the variables", number_names().join(" ")))
    }
}

/// The right side of an assignment, by the type of what it gives.
enum Rhs {
    Num(Pipe),
    Group(Pipe),
}

pub(crate) struct Parser<'a> {
    pub(crate) toks: Vec<Tok>,
    pub(crate) at: usize,
    pub(crate) defs: &'a Defs,
    /// The names of `defs` expanded.
    pub(crate) used: Vec<String>,
    pub(crate) params: Vec<ParamUse>,
    /// The group variables bound so far in the text, which a name alone can read as a value.
    pub(crate) groups: Vec<String>,
    /// The function variables bound so far in the text (`f:term->num = size`) and their types.
    pub(crate) fns: Vec<(String, Ty)>,
    /// The local variables that hold a number bound so far in the text (`n = (size * 2)`).
    pub(crate) locals: Vec<String>,
    /// The stage read follows a `|`.
    pub(crate) after_bar: bool,
    /// An atom already read, which the expression read next starts with.
    pub(crate) pending: Option<Pipe>,
    /// Reading a top-level statement, whose last step may give a text.
    pub(crate) text_tail: bool,
}

/// The local variables the top-level statements of a program bound so far, which the later
/// ones read.
#[derive(Clone, Default)]
pub(crate) struct TopNames {
    groups: Vec<String>,
    locals: Vec<String>,
    fns: Vec<(String, Ty)>,
}

pub(crate) fn seq_of(mut stages: Vec<Pipe>) -> Pipe {
    if stages.len() == 1 { stages.pop().unwrap() } else { Pipe::Seq(stages) }
}

/// The pipeline `p | e` that gives the number `e` gives, `p` a sequence written out: `p` and
/// its steps are one scope alike, and it shows the same.
pub(crate) fn number_seq(p: Pipe, e: Pipe) -> Pipe {
    let mut ps = match p {
        Pipe::Seq(ps) if ps.len() > 1 => ps,
        p => vec![p],
    };
    ps.push(e);
    Pipe::Seq(ps)
}

impl<'a> Parser<'a> {
    pub(crate) fn new(toks: Vec<Tok>, defs: &'a Defs) -> Parser<'a> {
        Parser { toks, at: 0, defs, used: Vec::new(), params: Vec::new(), groups: Vec::new(), fns: Vec::new(), locals: Vec::new(), after_bar: false, pending: None, text_tail: false }
    }

    /// Whether `n` is a group value: a group parameter, or a group variable bound before in
    /// the text that names nothing else.
    fn group_value(&self, n: &str) -> bool {
        match self.param(n) {
            Some(i) => matches!(self.params[i].ty, Some(Ty::Group | Ty::Term)),
            None => self.groups.iter().any(|g| g == n) && !self.defs.contains_key(n) && !known_name(n) && resolve(n).is_none(),
        }
    }

    /// An explicit input ahead: a group value's name, a parenthesized stage (run on the
    /// step's input unless it starts with a value), or with `loose` a name that names nothing
    /// else, read as a group variable (the checks find it unbound); `None` (nothing read)
    /// otherwise.
    pub(crate) fn group_input(&mut self, loose: bool) -> Result<Option<Pipe>, String> {
        match self.peek().cloned() {
            Some(Tok::Name(n)) if self.input_def(&n) => {
                self.at += 1;
                self.used.push(n.clone());
                self.call_of(&n, Vec::new(), None).map(Some)
            }
            Some(Tok::Name(n)) if self.input_name(&n, loose) => {
                self.at += 1;
                self.use_param(&n, Ty::Group)?;
                Ok(Some(group(n)))
            }
            Some(Tok::Open) => self.stage().map(Some),
            _ => Ok(None),
        }
    }

    fn input_name(&self, n: &str, loose: bool) -> bool {
        self.group_value(n) || self.param(n).is_some_and(|i| self.params[i].ty.is_none()) || loose && self.param(n).is_none() && self.unknown(n)
    }

    /// Whether `n` is a function put in place that takes only its input (`main`), which
    /// `group_input` reads as an explicit input.
    fn input_def(&self, n: &str) -> bool {
        self.param(n).is_none() && self.defs.get(n).is_some_and(|d| d.input.is_some() && d.params.is_empty())
    }

    /// Whether an explicit input is ahead, as `group_input` reads it.
    pub(crate) fn input_ahead(&self, loose: bool) -> bool {
        match self.peek() {
            Some(Tok::Name(n)) => self.input_name(n, loose) || self.input_def(n),
            Some(Tok::Open) => true,
            _ => false,
        }
    }

    /// Whether `n` names no variable, function, definition or word of the language.
    fn unknown(&self, n: &str) -> bool {
        !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || ["none", "true", "def", "extern"].contains(&n))
    }

    /// Whether an expression is ahead, for the body of a function: a number, `!`, or a name
    /// of a variable, number function or numeric parameter, maybe after `(`.
    pub(crate) fn expr_ahead(&self) -> bool {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        match self.peek_at(k) {
            Some(Tok::Num(_) | Tok::Not) => true,
            Some(Tok::Name(n)) if self.peek_at(k + 1) != Some(&Tok::Assign) => match self.param(n) {
                Some(i) => self.params[i].ty.as_ref().is_some_and(Ty::is_expr),
                None => {
                    let number_def = self.defs.get(n).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_some());
                    number_def || n == "none" || get(n).map_or(var_index(n).is_some() && !self.defs.contains_key(n), |s| s.is_number())
                }
            },
            _ => false,
        }
    }

    pub(crate) fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn peek_at(&self, k: usize) -> Option<&Tok> {
        self.toks.get(self.at + k)
    }

    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.at).cloned();
        self.at += 1;
        t
    }

    pub(crate) fn expect(&mut self, t: Tok, what: &str) -> Result<(), String> {
        match self.next() {
            Some(x) if x == t => Ok(()),
            x => Err(format!("expected {what}, found {}", show_tok(x.as_ref()))),
        }
    }

    pub(crate) fn name(&mut self, what: &str) -> Result<String, String> {
        match self.next() {
            Some(Tok::Name(n)) => Ok(n),
            x => Err(format!("expected {what}, found {}", show_tok(x.as_ref()))),
        }
    }

    /// The type of the function variable `n` bound before in the text.
    fn fn_var(&self, n: &str) -> Option<Ty> {
        self.fns.iter().rev().find(|(f, _)| f == n).map(|(_, t)| t.clone())
    }

    /// Whether `n` is a parameter or function variable that holds a function giving a number.
    fn number_fn_name(&self, n: &str) -> bool {
        let gives_number = |t: &Ty| matches!(t, Ty::Fn(_, b) if **b == Ty::Num);
        match self.param(n) {
            Some(i) => self.params[i].ty.as_ref().is_some_and(gives_number),
            None => self.fn_var(n).as_ref().is_some_and(gives_number),
        }
    }

    /// The function a name alone ahead stands for where a function of type `want` is wanted:
    /// a parameter not typed otherwise, which gets that type unless annotated, or a function
    /// variable; `None` (nothing read) for another name. `whose` names the parameter the
    /// argument is for.
    fn function_name(&mut self, want: &Ty, whose: &dyn Fn() -> String) -> Result<Option<Pipe>, String> {
        let Some(Tok::Name(n)) = self.peek().cloned() else { return Ok(None) };
        if let Some(i) = self.param(&n) {
            if self.params[i].ty.as_ref().is_some_and(|t| !matches!(t, Ty::Fn(..))) {
                return Ok(None);
            }
            self.at += 1;
            self.use_param(&n, want.clone())?;
            return Ok(Some(param_var(i, n)));
        }
        let Some(t) = self.fn_var(&n) else { return Ok(None) };
        self.at += 1;
        if !t.fits(want) {
            return Err(format!("{}; {n} is {t}", whose()));
        }
        Ok(Some(Pipe::Var(Slot::Local(n, Holds::Fn(t)))))
    }

    /// The function variable `n` read.
    fn fn_read(&self, n: String) -> Pipe {
        let t = self.fn_var(&n).unwrap_or_else(Ty::pipe);
        Pipe::Var(Slot::Local(n, Holds::Fn(t)))
    }

    /// The type of the function a stage is: a built-in function without its input, a
    /// parameter, a function variable, else `pipe`.
    fn stage_ty(&self, p: &Pipe) -> Ty {
        match p {
            Pipe::App(Fun::Builtin(b), _) => match &b.sig.input {
                Some(i) if i.ty == Ty::MaybeTerm => Ty::Fn(Box::new(Ty::Term), Box::new(b.sig.result.clone())),
                Some(i) => Ty::Fn(Box::new(i.ty.clone()), Box::new(b.sig.result.clone())),
                None => Ty::pipe(),
            },
            Pipe::Var(Slot::Param(i, _)) => self.params[*i].ty.clone().unwrap_or_else(Ty::pipe),
            Pipe::Var(Slot::Local(_, Holds::Fn(t))) => t.clone(),
            Pipe::App(Fun::Def(c), _) if c.def.implicit == Some(Ty::Term) && c.def.value.is_none() => Ty::Fn(Box::new(Ty::Term), Box::new(Ty::Group)),
            _ => Ty::pipe(),
        }
    }

    /// The input the expression `e` reads where it is not written: `term` where it reads only
    /// one term, `group` where it reads more, `None` where it reads none.
    pub(crate) fn input_ty(&self, e: &Pipe) -> Option<Ty> {
        let join = |a: Option<Ty>, b: Option<Ty>| match (a, b) {
            (Some(Ty::Group), _) | (_, Some(Ty::Group)) => Some(Ty::Group),
            (a, b) => a.or(b),
        };
        let input = |t: &Ty| match t {
            Ty::Fn(a, _) => Some((**a).clone()),
            _ => None,
        };
        let steps = |p: &Pipe| (!starts_with_value(p)).then_some(Ty::Group);
        match e {
            Pipe::App(Fun::Builtin(b), args) => match b.input_at(args) {
                Some(k) => steps(&args[k]),
                None => {
                    let own = b.sig.input.as_ref().map(|i| if i.ty == Ty::MaybeTerm { Ty::Term } else { i.ty.clone() });
                    args.iter().fold(own, |acc, a| join(acc, self.input_ty(a)))
                }
            },
            Pipe::App(Fun::Op(..), args) => args.iter().fold(None, |acc, a| join(acc, self.input_ty(a))),
            Pipe::Seq(_) => steps(e),
            Pipe::App(Fun::Def(c), args) => {
                let own = match args.get(c.def.params.len()) {
                    Some(p) => steps(p),
                    None if c.def.step => Some(c.def.implicit.clone().unwrap_or(Ty::Group)),
                    None => None,
                };
                args.iter().zip(&c.def.params).filter(|(_, p)| p.ty == Ty::Num).fold(own, |acc, (a, _)| join(acc, self.input_ty(a)))
            }
            Pipe::Var(Slot::Param(i, _)) => self.params.get(*i).and_then(|p| p.ty.as_ref()).and_then(input),
            Pipe::Var(Slot::Local(_, Holds::Fn(t))) => input(t),
            _ => None,
        }
    }

    /// `n:TYPE = f` after the `:`: the variable `n` bound to the function `f` of that type.
    fn typed_bind(&mut self, n: &str) -> Result<Pipe, String> {
        let mut t = self.name("a type after :")?;
        while self.peek() == Some(&Tok::Arrow) {
            self.at += 1;
            t = format!("{t}->{}", self.name("a type after ->")?);
        }
        let ty = Ty::parse(&t).ok().filter(Ty::is_function).ok_or_else(|| format!("{n}:{t} = ...: a function variable takes a function type, as in term->num or term->term"))?;
        self.expect(Tok::Assign, &format!("= after {n}:{t}"))?;
        let f = match ty.is_step() {
            true => {
                self.no_bar(&format!("{n}:{t} ="))?;
                let q = self.stage()?;
                if let Pipe::Var(Slot::Param(i, m)) = &q
                    && self.params[*i].ty.is_none()
                {
                    self.use_param(&m.clone(), ty.clone())?;
                }
                let have = self.stage_ty(&q);
                if !have.fits(&ty) {
                    return Err(format!("{n} holds {ty}; {} is {have}", stage(&q)));
                }
                q
            }
            false => self.or()?,
        };
        self.no_assign()?;
        self.bind_fn(n, f, ty)
    }

    /// An error where `n` cannot be a new local variable: a parameter, or the name of a
    /// variable of `VARS`, a function, a definition or a word of the language.
    fn local_name(&self, n: &str) -> Result<(), String> {
        if self.param(n).is_some() {
            return Err(format!("parameter {n} cannot be assigned"));
        }
        if self.defs.contains_key(n) {
            return Err(format!("{n} is defined by let or def @inline and cannot be assigned"));
        }
        if known_name(n) || resolve(n).is_some() || ["none", "def", "extern"].contains(&n) {
            return Err(assignable(n).err().unwrap_or_else(|| format!("{n} cannot be assigned")));
        }
        Ok(())
    }

    /// `n = f`: the function value `f` of type `ty` bound to the local variable `n`.
    fn bind_fn(&mut self, n: &str, f: Pipe, ty: Ty) -> Result<Pipe, String> {
        if self.groups.iter().any(|g| g == n) {
            return Err(format!("{n} is a group variable, so it cannot hold a function value"));
        }
        if self.locals.iter().any(|l| l == n) {
            return Err(format!("{n} is a number variable, so it cannot hold a function value"));
        }
        self.local_name(n)?;
        self.fns.push((n.to_string(), ty.clone()));
        Ok(Pipe::Bind(Slot::Local(n.to_string(), Holds::Fn(ty)), Arc::new(f)))
    }

    /// `n = e`: the number `e` gives bound to the local variable `n`.
    fn bind_num(&mut self, n: &str, e: Pipe) -> Result<Pipe, String> {
        self.local_name(n)?;
        self.locals.push(n.to_string());
        Ok(Pipe::Bind(Slot::Local(n.to_string(), Holds::Num), Arc::new(e)))
    }

    pub(crate) fn pipe(&mut self) -> Result<Pipe, String> {
        let (stages, tail) = self.stages_of_pipe()?;
        let p = seq_of(stages);
        match tail {
            Some(e) => Err(format!("{} | {} gives a number, not a group: a pipeline that ends in a number goes where a number does, as in x = (a | size)", show(&p), show_expr(&e, 1))),
            None => Ok(p),
        }
    }

    /// Whether a step that gives a number is ahead, maybe after `(`: a number, `!`, a number
    /// function, a function defined that gives a number, or a variable that holds a number and
    /// names no step.
    fn number_step_ahead(&self) -> bool {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        match self.peek_at(k) {
            Some(Tok::Num(_) | Tok::Not) => true,
            Some(Tok::Name(_)) if matches!(self.peek_at(k + 1), Some(Tok::Assign | Tok::Colon)) => false,
            Some(Tok::Name(n)) if self.param(n).is_some() => self.number_fn_name(n) || self.params[self.param(n).unwrap()].ty == Some(Ty::Num),
            Some(Tok::Name(n)) if self.fn_var(n).is_some() => self.number_fn_name(n),
            Some(Tok::Name(n)) if self.locals.iter().any(|l| l == n) => true,
            Some(Tok::Name(n)) => get(n).is_some_and(|s| s.is_number()) || self.number_def(n) || var_index(n).is_some() && get(n).is_none() && !self.defs.contains_key(n) && !self.group_value(n),
            _ => false,
        }
    }

    /// The input the step ahead takes, for an error after a step that gives no group: its
    /// input parameter, or `a group`.
    fn takes_ahead(&self) -> String {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        let input = match self.peek_at(k) {
            Some(Tok::Name(n)) if self.param(n).is_none() => match get(n) {
                Some(s) => s.input.as_ref().map(|i| i.to_string()),
                None => self.defs.get(n).map(|_| self.sig_named(n)).and_then(|s| s.input.map(|i| i.to_string())),
            },
            _ => None,
        };
        let what = match self.peek_at(k) {
            Some(t @ Tok::Name(_)) => show_tok(Some(t)),
            t => show_tok(t),
        };
        format!("{what} takes {}", input.unwrap_or_else(|| "a group".into()))
    }

    /// The stages of a pipeline `a | b | ...`, and the expression of a last step that gives a
    /// number (`a | size`).
    pub(crate) fn stages_of_pipe(&mut self) -> Result<(Vec<Pipe>, Option<Pipe>), String> {
        self.stages_after(Vec::new())
    }

    /// The stages of a pipeline whose first `stages` are read already.
    pub(crate) fn stages_after(&mut self, mut stages: Vec<Pipe>) -> Result<(Vec<Pipe>, Option<Pipe>), String> {
        if !stages.is_empty() {
            if self.peek() != Some(&Tok::Bar) {
                return Ok((stages, None));
            }
            self.at += 1;
        }
        loop {
            if !stages.is_empty() && self.text_tail && self.text_ahead() {
                let e = self.text_value()?;
                if self.peek() == Some(&Tok::Bar) {
                    self.at += 1;
                    return Err(format!("{} gives text; {}", show(&e), self.takes_ahead()));
                }
                return Ok((stages, Some(e)));
            }
            if !stages.is_empty() && self.number_step_ahead() {
                let e = self.or()?;
                if self.input_ty(&e).is_none() {
                    stages.push(Pipe::Drop(Arc::new(e), true));
                    if self.peek() != Some(&Tok::Bar) {
                        break;
                    }
                    self.at += 1;
                    continue;
                }
                if self.peek() == Some(&Tok::Bar) {
                    self.at += 1;
                    return Err(format!("{} gives num; {}", show_expr(&e, 1), self.takes_ahead()));
                }
                return Ok((stages, Some(e)));
            }
            let flat = match (self.peek(), self.peek_at(1)) {
                (Some(Tok::Name(n)), _) => self.defs.get(n).is_some_and(|d| d.flat && d.params.is_empty()),
                (Some(Tok::Open), Some(Tok::Name(n))) => self.defs.get(n).is_some_and(|d| d.flat && !d.params.is_empty()),
                _ => false,
            };
            self.after_bar = !stages.is_empty();
            match self.stage()? {
                Pipe::Seq(ps) if flat => stages.extend(ps),
                p => stages.push(p),
            }
            if self.peek() != Some(&Tok::Bar) {
                break;
            }
            self.at += 1;
        }
        Ok((stages, None))
    }

    fn stage(&mut self) -> Result<Pipe, String> {
        let after_bar = std::mem::take(&mut self.after_bar);
        if let (Some(Tok::Name(n)), Some(Tok::Assign)) = (self.peek().cloned(), self.peek_at(1)) {
            self.at += 2;
            return self.assign(&n);
        }
        if let (Some(Tok::Name(n)), Some(Tok::Colon)) = (self.peek().cloned(), self.peek_at(1)) {
            self.at += 2;
            return self.typed_bind(&n);
        }
        let k = usize::from(self.peek() == Some(&Tok::Open));
        if let Some(e) = self.old_form(k) {
            return Err(e.into());
        }
        let mut paren = false;
        let p = self.stage_of(&mut paren)?;
        self.note_bound(&p);
        Ok(if after_bar && !paren && starts_with_value(&p) { Pipe::Drop(Arc::new(p), false) } else { p })
    }

    /// Adds the group variables `p` binds in this run to those a name can read: those of the
    /// bodies of `let` and `@inline` functions put in place, which share it.
    fn note_bound(&mut self, p: &Pipe) {
        let mut found = Vec::new();
        fn walk(p: &Pipe, found: &mut Vec<String>) {
            match p {
                Pipe::Bind(Slot::Local(n, Holds::Group), _) => found.push(n.clone()),
                Pipe::App(Fun::Builtin(b), a) if b.name == "save" => {
                    if let Some(Pipe::Name(n)) = a.first() {
                        found.push(n.clone());
                    }
                }
                Pipe::App(Fun::Def(c), _) if c.def.inline => walk(&c.body, found),
                Pipe::Expanded(m) => m.steps.iter().for_each(|q| walk(q, found)),
                _ => {}
            }
            p.each(&mut |q| walk(q, found));
        }
        walk(p, &mut found);
        for n in found {
            if !n.contains('#') && !self.groups.contains(&n) && self.param(&n).is_none() {
                self.groups.push(n);
            }
        }
    }

    /// A stage as `stage` reads it, its own value or not; `paren` set for a pipeline in
    /// parentheses, which starts from a value it starts with.
    fn stage_of(&mut self, paren: &mut bool) -> Result<Pipe, String> {
        let args_follow = |p: &Self| matches!(p.peek_at(1), Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not));
        match self.next() {
            Some(Tok::Name(n)) if self.group_value(&n) => {
                self.use_param(&n, Ty::Group)?;
                Ok(group(n))
            }
            Some(Tok::Name(n)) if self.param(&n).is_none() && self.fn_var(&n).is_some() => match self.fn_var(&n).unwrap() {
                t if t.is_step() => Ok(Pipe::Var(Slot::Local(n, Holds::Fn(t)))),
                t => Err(format!("{n} gives a number, not a group: it holds {t}; a step calls a function that gives a group")),
            },
            Some(Tok::Name(n)) if self.param(&n).is_some() => {
                self.step_param(&n)?;
                Ok(param_var(self.param(&n).unwrap(), n))
            }
            Some(Tok::Name(n)) if self.defs.get(&n).is_some_and(|d| d.input.is_some() && d.params.is_empty()) => {
                self.used.push(n.clone());
                self.call_of(&n, Vec::new(), None)
            }
            Some(Tok::Name(n)) if self.defs.contains_key(&n) => {
                let d = &self.defs[&n];
                if !d.params.is_empty() {
                    return Err(format!("{n} needs parentheses: ({n} ...); {}", self.sig_named(&n)));
                }
                if self.number_def(&n) {
                    return Err(format!("{n} gives a number, not a group: {}; a step calls a function that gives a group", self.sig_named(&n)));
                }
                if d.def.as_ref().is_some_and(|d| d.inline && d.input.is_some()) {
                    let p = self.call_of(&n, Vec::new(), None)?;
                    self.used.push(n);
                    return Ok(p);
                }
                let p = d.pipe.clone();
                self.used.push(n);
                Ok(p)
            }
            Some(Tok::Name(n)) => bare(&n),
            Some(Tok::Open) => {
                let p = match self.peek().cloned() {
                    Some(Tok::Name(n)) if n == "on" || n == "off" => {
                        self.at += 1;
                        self.switches(&n)?
                    }
                    // `(relate = 0 | ...)` assigns the switch of a pass that takes arguments.
                    Some(Tok::Name(_)) if self.peek_at(1) == Some(&Tok::Assign) => {
                        *paren = true;
                        self.pipe()?
                    }
                    Some(Tok::Name(n)) if self.defs.get(&n).is_some_and(|d| !d.params.is_empty() || (d.run || d.input.is_some()) && args_follow(self)) => {
                        self.at += 1;
                        self.def_call(&n)?
                    }
                    Some(Tok::Name(n)) if self.param(&n).is_none() && self.fn_var(&n).is_some_and(|t| t.is_step()) && args_follow(self) => {
                        self.at += 1;
                        let Some(input) = self.group_input(true)? else { return Err(format!("{n} takes a group value: ({n} g)")) };
                        Pipe::Seq(vec![input, self.fn_read(n)])
                    }
                    Some(Tok::Name(n)) if self.param(&n).is_some_and(|i| self.params[i].ty != Some(Ty::Group)) && args_follow(self) => {
                        self.at += 1;
                        let Some(input) = self.group_input(true)? else { return Err(format!("parameter {n} takes a group value: ({n} g)")) };
                        self.step_param(&n)?;
                        Pipe::Seq(vec![input, param_var(self.param(&n).unwrap(), n)])
                    }
                    Some(Tok::Name(n)) if n == "import" => return Err(NO_IMPORT.into()),
                    Some(Tok::Name(n)) => match get(&n) {
                        Some(s) if s.is_number() => return Err(not_a_step(s)),
                        Some(s) if s.is_text() => return Err(text_step(s)),
                        Some(s) if s.kind() == Kind::FromText => {
                            self.at += 1;
                            let t = self.text_value()?;
                            Pipe::App(Fun::Builtin(super::builtins::builtin(&n).unwrap()), vec![t].into())
                        }
                        Some(s) if !s.params.is_empty() => {
                            self.at += 1;
                            *paren = s.name == "seq";
                            self.call(s)?
                        }
                        Some(s) if args_follow(self) => {
                            self.at += 1;
                            let Some(input) = self.group_input(false)? else { return Err(format!("{n} takes {}: {s}", s.arity())) };
                            explicit(input, construct(&n, Vec::new()).ok_or_else(|| unimplemented(s))?)
                        }
                        _ => {
                            *paren = true;
                            self.pipe()?
                        }
                    },
                    _ => {
                        *paren = true;
                        self.pipe()?
                    }
                };
                self.expect(Tok::Close, ")")?;
                Ok(p)
            }
            x => Err(format!("expected a pass or (, found {}", show_tok(x.as_ref()))),
        }
    }

    /// Whether a function that gives a text is ahead, alone or called in parentheses.
    fn text_ahead(&self) -> bool {
        let k = usize::from(self.peek() == Some(&Tok::Open));
        matches!(self.peek_at(k), Some(Tok::Name(n)) if self.param(n).is_none() && get(n).is_some_and(Sig::is_text))
    }

    /// A text: a string literal, or a function that gives one, alone (on the step's input) or
    /// with its input written (`(show (main t))`).
    fn text_value(&mut self) -> Result<Pipe, String> {
        if let Some(Tok::Str(t)) = self.peek().cloned() {
            self.at += 1;
            return Ok(Pipe::Text(t));
        }
        if !self.text_ahead() {
            return Err(format!("expected a text, as in \"x + y\" or (show (main t)), found {}", show_tok(self.peek())));
        }
        let open = self.peek() == Some(&Tok::Open);
        self.at += usize::from(open);
        let n = self.name("a function")?;
        let s = get(&n).unwrap();
        let f = Fun::Builtin(super::builtins::builtin(&n).unwrap());
        if !open {
            return Ok(Pipe::App(f, Vec::new().into()));
        }
        let input = self.group_input(true)?;
        self.expect(Tok::Close, ")")?;
        match input {
            Some(x) => {
                self.input_fits(s, s.input.as_ref().unwrap(), &x)?;
                Ok(Pipe::App(f, vec![x].into()))
            }
            None => Ok(Pipe::App(f, Vec::new().into())),
        }
    }

    /// A top-level statement: its steps, each with what it gives.
    fn statement(&mut self) -> Result<Vec<Top>, String> {
        let one = |pipe: Pipe, gives: Gives| Ok(vec![Top { pipe, gives }]);
        if matches!(self.peek(), Some(Tok::Str(_))) || self.text_ahead() && self.text_is_whole() {
            let t = self.text_value()?;
            self.end()?;
            return one(t, Gives::Text);
        }
        if let (Some(Tok::Name(n)), None) = (self.peek().cloned(), self.peek_at(1))
            && self.fn_var(&n).is_some()
        {
            self.at += 1;
            return one(self.fn_read(n), Gives::Fn);
        }
        if self.peek_at(1) != Some(&Tok::Colon) && self.number_ahead(false) {
            let e = self.or()?;
            self.end()?;
            return one(e, Gives::Num);
        }
        self.text_tail = true;
        let r = self.stages_of_pipe();
        self.text_tail = false;
        let (stages, tail) = r?;
        self.end()?;
        let mut out: Vec<Top> = stages.into_iter().map(Top::step).collect();
        if let Some(e) = tail {
            let gives = if matches!(e, Pipe::App(Fun::Builtin(b), _) if b.sig.is_text()) { Gives::Text } else { Gives::Num };
            out.push(Top { pipe: e, gives });
        }
        Ok(out)
    }

    /// Whether the text function ahead is the whole statement: nothing follows its call.
    fn text_is_whole(&self) -> bool {
        if self.peek() != Some(&Tok::Open) {
            return self.peek_at(1).is_none();
        }
        let mut depth = 0;
        for (k, t) in self.toks[self.at..].iter().enumerate() {
            match t {
                Tok::Open => depth += 1,
                Tok::Close if depth == 1 => return self.at + k + 1 == self.toks.len(),
                Tok::Close => depth -= 1,
                _ => {}
            }
        }
        false
    }

    /// Whether `n` is a function defined whose body is an expression.
    fn number_def(&self, n: &str) -> bool {
        self.defs.get(n).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_some())
    }

    /// The error for a form no longer read starting `k` tokens ahead.
    fn old_form(&self, k: usize) -> Option<&'static str> {
        let name = |j: usize, s: &str| matches!(self.peek_at(k + j), Some(Tok::Name(n)) if n == s);
        if name(0, "with") {
            Some(NO_WITH)
        } else if name(0, "time") && self.peek_at(k + 1) == Some(&Tok::Arith('-')) && name(2, "limit") {
            Some(NO_TIME_LIMIT)
        } else {
            None
        }
    }

    /// The right side of `n = ...`, read once and taken by the type of what it gives: an
    /// expression up to `|`, `)` or the end for a variable that holds a number, one step that
    /// gives candidates for a group variable. Where a name fits both (`relate`, a parameter
    /// `r`), `n` decides.
    fn assign(&mut self, n: &str) -> Result<Pipe, String> {
        if let Some(d) = self.defs.get(n).filter(|d| d.run) {
            return Err(format!("{n} is a function and cannot be assigned: {}", def_sig(n, &d.params)));
        }
        if self.param(n).is_some() {
            return Err(format!("parameter {n} cannot be assigned"));
        }
        if var_index(n) == Some(super::host::NUM_TYPE) {
            let t = self.name("a numeric type after num_type =")?;
            self.no_assign()?;
            return match t.as_str() {
                "none" => Ok(Pipe::assign(super::host::NUM_TYPE, Pipe::Num(NONE))),
                t if super::host::NUM_TYPES.contains(&t) => Ok(Pipe::assign(super::host::NUM_TYPE, Pipe::Name(t.into()))),
                t => Err(format!("num_type takes a numeric type, not {t}; known: {}", super::host::NUM_TYPES.join(" "))),
            };
        }
        let number_var = var_index(n).is_some();
        let group_var = self.groups.iter().any(|g| g == n);
        if let (Some(Tok::Open), Some(e)) = (self.peek(), self.old_form(1)) {
            return Err(e.into());
        }
        let rhs = match self.number_ahead(number_var) {
            true => self.or().map(Rhs::Num),
            false => self.rhs_group(number_var, true),
        }?;
        self.no_assign()?;
        match rhs {
            Rhs::Num(e) if number_var => self.assign_number(n, e),
            Rhs::Num(e) if group_var => Err(format!("{n} is a group variable, so it cannot hold a number: {} gives a number", show_expr(&e, 1))),
            Rhs::Num(e) if self.fn_var(n).is_some() => Err(format!("{n} is a function variable, so it cannot hold a number: {} gives a number; write {n}:TYPE = ... for a function", show_expr(&e, 1))),
            Rhs::Num(e) => self.bind_num(n, e),
            Rhs::Group(p) if number_var => Err(format!("{n} is a variable that holds a number, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) if self.locals.iter().any(|l| l == n) => Err(format!("{n} is a number variable, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) if self.fn_var(n).is_some() => Err(format!("{n} is a function variable, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) => self.bind(n, p),
        }
    }

    /// Whether the right side of an assignment reads as an expression: it starts, maybe after
    /// `(`, with a number, `!`, a call of a function that gives a number, or a name that gives
    /// a number (for a name that is also a step or an untyped parameter, where `number_var`,
    /// but a step where a `|` follows it inside parentheses), or a name that names nothing,
    /// unless written alone (`t = u` binds a group variable).
    fn number_ahead(&self, number_var: bool) -> bool {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        let Some(Tok::Name(n)) = self.peek_at(k) else { return true };
        let after = self.peek_at(k + 1);
        if after == Some(&Tok::Assign) {
            return false;
        }
        let number_fn = get(n).is_some_and(|s| s.is_number()) || self.number_def(n);
        if k > 0 && matches!(after, Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not)) {
            return match self.param(n) {
                Some(i) => self.params[i].ty.as_ref().is_some_and(Ty::is_expr),
                None => number_fn || self.number_fn_name(n),
            };
        }
        if self.locals.iter().any(|l| l == n) {
            return true;
        }
        match self.param(n) {
            Some(i) => return self.params[i].ty.as_ref().map_or(number_var, Ty::is_expr),

            None if number_fn || self.number_fn_name(n) => return true,
            None if self.fn_var(n).is_some() => return false,
            None => {}
        }
        if self.defs.contains_key(n) || self.group_value(n) {
            false
        } else if var_index(n).is_some() {
            resolve(n).is_none() || number_var && !(k > 0 && after == Some(&Tok::Bar))
        } else if ["none", "true", "def", "extern"].contains(&n.as_str()) || MACROS.contains(&n.as_str()) {
            true
        } else if !self.unknown(n) {
            false
        } else {
            k > 0 || !matches!(after, None | Some(Tok::Bar | Tok::Close))
        }
    }

    /// Whether a call form ahead starts with this `(`, as `stage` reads it: `on`, `off`, a
    /// function with parameters or arguments, a parameter called on a group.
    fn form_ahead(&self) -> bool {
        let args = matches!(self.peek_at(2), Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not | Tok::Str(_)));
        match self.peek_at(1) {
            Some(Tok::Name(_)) if self.peek_at(2) == Some(&Tok::Assign) => false,
            Some(Tok::Name(n)) => {
                n == "on"
                    || n == "off"
                    || self.defs.get(n).is_some_and(|d| !d.params.is_empty() || d.run && args)
                    || self.param(n).is_some_and(|i| self.params[i].ty != Some(Ty::Group)) && args
                    || get(n).is_some_and(|s| !s.params.is_empty() || args)
            }
            _ => false,
        }
    }

    /// The right side of an assignment that does not start as an expression: a pipeline in
    /// parentheses, which gives a number where it ends in one (`(a | size) > 3`), or one step
    /// (`top`: as `bound_step` reads it).
    fn rhs_group(&mut self, number_var: bool, top: bool) -> Result<Rhs, String> {
        if self.peek() != Some(&Tok::Open) || self.form_ahead() {
            return Ok(Rhs::Group(if top { self.bound_step()? } else { self.stage()? }));
        }
        if let Some(e) = self.old_form(1) {
            return Err(e.into());
        }
        self.at += 1;
        let inner = match self.peek() {
            Some(Tok::Open) if !self.form_ahead() => match self.rhs_group(number_var, false)? {
                Rhs::Num(e) => {
                    let e = self.expr_from(e)?;
                    if self.peek() == Some(&Tok::Bar) {
                        self.at += 1;
                        return Err(format!("{} gives num; {}", show_expr(&e, 1), self.takes_ahead()));
                    }
                    Rhs::Num(e)
                }
                Rhs::Group(p) => self.pipe_rhs(vec![p])?,
            },
            _ => self.pipe_rhs(Vec::new())?,
        };
        self.expect(Tok::Close, ")")?;
        Ok(match inner {
            Rhs::Num(e) => Rhs::Num(self.expr_from(e)?),
            g => g,
        })
    }

    /// A pipeline after its `first` stages, as the number it ends in or its candidates.
    fn pipe_rhs(&mut self, first: Vec<Pipe>) -> Result<Rhs, String> {
        let (stages, tail) = self.stages_after(first)?;
        let p = seq_of(stages);
        Ok(match tail {
            Some(e) => Rhs::Num(number_seq(p, e)),
            None => Rhs::Group(p),
        })
    }

    /// The expression that starts with the atom `e` read already.
    fn expr_from(&mut self, e: Pipe) -> Result<Pipe, String> {
        self.pending = Some(e);
        let r = self.or();
        self.pending = None;
        r
    }

    /// `n = e` for the variable `n` that holds a number.
    fn assign_number(&mut self, n: &str, e: Pipe) -> Result<Pipe, String> {
        let i = assignable(n)?;
        if let Pipe::Num(k) = e {
            if is_switch(i) && k == NONE {
                return Err(format!("{n} is a switch: assign it 0 (off) or 1 (on)"));
            }
        }
        Ok(Pipe::assign(i, e))
    }

    /// Whether a group variable alone is ahead, up to `|`, `)` or the end: a name that is no
    /// variable, function or definition, or a parameter used as a group variable.
    fn group_var_ahead(&self) -> bool {
        let Some(Tok::Name(n)) = self.peek() else { return false };
        if !matches!(self.peek_at(1), None | Some(Tok::Bar | Tok::Close)) {
            return false;
        }
        match self.param(n) {
            Some(i) => self.params[i].ty == Some(Ty::Group),
            None => !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || ["none", "true", "def", "extern"].contains(&n.as_str())),
        }
    }

    /// The right side of `n = p` read as a group: a group variable alone, or one step.
    fn bound_step(&mut self) -> Result<Pipe, String> {
        let p = match self.group_var_ahead() {
            true => {
                let u = self.name("a group variable")?;
                self.group_name(&u)?;
                group(u)
            }
            false => self.stage()?,
        };
        self.no_assign()?;
        Ok(p)
    }

    /// `n = p`: the candidates of the step `p` bound to the group variable `n`.
    fn bind(&mut self, n: &str, p: Pipe) -> Result<Pipe, String> {
        if self.fn_var(n).is_some() {
            return Err(format!("{n} is a function variable, so it cannot be bound to a group"));
        }
        if self.locals.iter().any(|l| l == n) {
            return Err(format!("{n} is a number variable, so it cannot be bound to a group"));
        }
        if self.defs.contains_key(n) {
            return Err(format!("{n} is defined by let or def @inline and cannot be assigned"));
        } else if known_name(n) || resolve(n).is_some() || ["none", "def", "extern"].contains(&n) {
            return Err(assignable(n).err().unwrap_or_else(|| format!("{n} cannot be assigned")));
        }
        self.groups.push(n.to_string());
        Ok(Pipe::Bind(Slot::Local(n.to_string(), Holds::Group), Arc::new(p)))
    }

    /// `n` written where a group variable is: an error for a variable that holds a number.
    pub(crate) fn group_name(&mut self, n: &str) -> Result<(), String> {
        if self.param(n).is_some() {
            return self.use_param(n, Ty::Group);
        }
        if self.fn_var(n).is_some() {
            return Err(format!("{n} is a function variable, so it cannot name a group variable"));
        }
        if self.locals.iter().any(|l| l == n) {
            return Err(format!("{n} is a number variable, so it cannot name a group variable"));
        }
        match var_index(n) {
            Some(_) => Err(format!("{n} is a variable that holds a number, so it cannot name a group variable")),
            None => Ok(()),
        }
    }

    /// An error where a comparison was meant and `=` written.
    fn no_assign(&self) -> Result<(), String> {
        match self.peek() {
            Some(Tok::Assign) => Err("an assignment is a step; compare with ==".into()),
            _ => Ok(()),
        }
    }

    pub(crate) fn end(&self) -> Result<(), String> {
        match self.peek() {
            None => Ok(()),
            t => Err(format!("unexpected {} after the pipeline", show_tok(t))),
        }
    }

    pub(crate) fn at_close(&self) -> bool {
        matches!(self.peek(), Some(Tok::Close) | None)
    }

    /// Stages up to the closing parenthesis, at least one (`missing` the error otherwise).
    fn stages(&mut self, form: &str, missing: &dyn Fn() -> String) -> Result<Vec<Pipe>, String> {
        let mut out = Vec::new();
        while !self.at_close() {
            self.no_bar(form)?;
            out.push(self.stage()?);
        }
        if out.is_empty() {
            return Err(missing());
        }
        Ok(out)
    }

    fn no_bar(&self, form: &str) -> Result<(), String> {
        match self.peek() {
            Some(Tok::Bar) => Err(format!("group a pipeline argument of {form} in parentheses: ({form} ... (a | b))")),
            _ => Ok(()),
        }
    }

    /// An expression argument of a form: a number, a name, `!` and an argument, or a
    /// parenthesized expression.
    fn arg(&mut self) -> Result<Pipe, String> {
        let e = self.arg_of()?;
        self.no_assign()?;
        Ok(e)
    }

    fn arg_of(&mut self) -> Result<Pipe, String> {
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(op("!", vec![self.arg_of()?]));
        }
        self.atom()
    }

    /// The arguments of a call of the group function `s` after its name, as its parameters
    /// read them: an expression argument (`arg`), a name, one stage per pipeline, or the
    /// whole pipeline up to `)` when one pipeline is the last and only one (`(fix 3 a | b)`).
    fn call(&mut self, s: &'static Sig) -> Result<Pipe, String> {
        let args = self.args(s, false)?;
        let input = self.group_input(true)?;
        let p = construct(&s.name, args).ok_or_else(|| unimplemented(s))?;
        Ok(match input {
            Some(i) => explicit(i, p),
            None => p,
        })
    }

    /// The arguments of a call of `s` after its name, as `call` reads them; `sig` adds the
    /// signature to an error in an expression argument.
    pub(crate) fn args(&mut self, s: &Sig, sig: bool) -> Result<Vec<Arg>, String> {
        let f = s.name.as_str();
        let arity = || format!("{f} takes {}: {s}", s.arity());
        let pipes = s.params.iter().filter(|p| p.ty.is_step()).count();
        let mut args = Vec::new();
        for (i, p) in s.params.iter().enumerate() {
            let whole = pipes == 1 && i + 1 == s.params.len() && p.rep == Rep::One;
            let named = matches!(self.peek(), Some(Tok::Name(_)));
            let alone = !matches!(self.peek_at(1), Some(Tok::Bar));
            let whose = || format!("{f} takes {p}: {s}");
            if matches!(p.ty, Ty::Fn(..)) && !p.ty.is_pipe() && p.rep == Rep::One && alone
                && let Some(q) = self.function_name(&p.ty, &whose)?
            {
                args.push(if p.ty.is_step() { Arg::Pipe(q) } else { Arg::Num(q) });
                continue;
            }
            if p.ty.is_step() && !p.ty.is_pipe() && !self.at_close() {
                let q = if whole { self.pipe()? } else {
                    self.no_bar(f)?;
                    self.stage()?
                };
                let have = self.stage_ty(&q);
                if !have.fits(&p.ty) {
                    return Err(format!("{}; {} is {have}", whose(), stage(&q)));
                }
                args.push(Arg::Pipe(q));
                continue;
            }
            args.push(match (&p.ty, p.rep) {
                (Ty::Text, _) => match self.next() {
                    Some(Tok::Str(t)) => Arg::Num(Pipe::Text(t)),
                    x => return Err(format!("{}; found {}", whose(), show_tok(x.as_ref()))),
                },
                (Ty::Any, _) => {
                    let mut xs = Vec::new();
                    while !self.at_close() {
                        xs.push(self.any_arg()?);
                    }
                    if xs.is_empty() {
                        return Err(arity());
                    }
                    Arg::Pipes(xs)
                }
                (_, Rep::Opt) if self.at_close() => Arg::Absent,
                (Ty::Name | Ty::Group, Rep::Opt) if !named => Arg::Absent,
                (_, Rep::One) if self.at_close() => return Err(arity()),
                (t, _) if t.is_expr() => Arg::Num(self.arg().map_err(|e| if sig { format!("{e}; {f} takes {}: {s}", s.arity()) } else { e })?),
                (t, _) if t.is_step() && matches!(self.peek(), Some(Tok::Num(_))) => return Err(arity()),
                (Ty::Group, _) => {
                    let n = self.name(&format!("a group variable after {f}"))?;
                    if f == "save" {
                        if self.param(&n).is_some() {
                            return Err(format!("parameter {n} cannot be assigned"));
                        }
                        self.groups.push(n.clone());
                    }
                    self.group_name(&n)?;
                    Arg::Name(n)
                }
                (Ty::Term, _) => match self.peek().cloned() {
                    Some(Tok::Name(n)) if self.param(&n).is_some() && matches!(self.peek_at(1), Some(Tok::Close | Tok::Name(_) | Tok::Open | Tok::Num(_))) => {
                        self.at += 1;
                        self.use_param(&n, Ty::Term)?;
                        Arg::Pipe(group(n))
                    }
                    _ => {
                        self.no_bar(f)?;
                        Arg::Pipe(self.stage()?)
                    }
                },
                (Ty::Name, _) => {
                    let n = self.name(&format!("a name after {f}"))?;
                    self.use_param(&n, Ty::Name)?;
                    Arg::Name(n)
                }
                (t, Rep::Many) if t.is_step() => Arg::Pipes(self.stages(f, &arity)?),
                (t, _) if t.is_step() && whole => Arg::Pipe(self.pipe()?),
                (t, _) if t.is_step() => {
                    self.no_bar(f)?;
                    Arg::Pipe(self.stage()?)
                }
                _ => unreachable!("{s}"),
            });
        }
        if !self.at_close() && !(s.input.is_some() && self.input_ahead(!s.params.is_empty())) {
            if pipes > 0 {
                self.no_bar(f)?;
            }
            return Err(arity());
        }
        Ok(args)
    }

    /// The function `n` names written as a value, without arguments: a function variable, or a
    /// built-in or defined function that gives candidates; `None` for another name.
    fn function_value(&mut self, n: &str) -> Option<Pipe> {
        if self.fn_var(n).is_some() {
            return Some(self.fn_read(n.to_string()));
        }
        if let Some(b) = super::builtins::builtin(n).filter(|b| !b.sig.is_number()) {
            return Some(Pipe::App(Fun::Builtin(b), Vec::new().into()));
        }
        let d = self.defs.get(n).filter(|d| d.def.as_ref().is_none_or(|d| d.value.is_none()))?;
        // A `let` or an `@inline` function written out where it is used has no `Def`: one stands
        // for it here, which only shows.
        let def = d.def.clone().unwrap_or_else(|| {
            let body = Arc::new(d.pipe.clone());
            Arc::new(Def { name: n.into(), params: d.params.clone(), body, inline: false, flat: d.flat, input: None, step: true, steps: false, value: None, implicit: None, timed: false, slot: None })
        });
        self.used.push(n.to_string());
        Some(Call::bare(&def))
    }

    /// An argument of type `any`: a string literal, a group value, a function value, an
    /// expression, or else a name.
    fn any_arg(&mut self) -> Result<Pipe, String> {
        let Some(Tok::Str(_) | Tok::Name(_)) = self.peek() else { return self.arg() };
        let n = match self.next() {
            Some(Tok::Str(t)) => return Ok(Pipe::Text(t)),
            Some(Tok::Name(n)) => n,
            _ => unreachable!(),
        };
        if self.group_value(&n) {
            self.use_param(&n, Ty::Group)?;
            return Ok(group(n));
        }
        if self.param(&n).is_none() && !self.locals.contains(&n) && n != "none" {
            if let Some(f) = self.function_value(&n) {
                return Ok(f);
            }
            if self.unknown(&n) {
                return Ok(Pipe::Name(n));
            }
        }
        self.at -= 1;
        self.arg()
    }

    /// The arguments of a call of the number function `s` after its name: names, and
    /// expressions up to `)`.
    fn number_call(&mut self, s: &'static Sig) -> Result<Pipe, String> {
        let f = s.name.as_str();
        let mut args = Vec::new();
        for p in &s.params {
            args.push(match &p.ty {
                _ if self.at_close() && p.rep == Rep::Opt => Arg::Absent,
                _ if self.at_close() => return Err(format!("{f} takes {}: {s}", s.arity())),
                t if matches!(t, Ty::Fn(..)) && self.peek_at(1) == Some(&Tok::Close) && matches!(self.peek(), Some(Tok::Name(n)) if self.param(n).is_some() || self.fn_var(n).is_some()) => {
                    let whose = || format!("{f} takes {p}: {s}");
                    match self.function_name(t, &whose)? {
                        Some(q) => Arg::Num(q),
                        None => Arg::Num(self.or()?),
                    }
                }
                t if t.is_expr() => Arg::Num(self.or()?),
                t if t.is_step() => {
                    self.no_bar(f)?;
                    Arg::Pipe(self.stage()?)
                }
                Ty::MaybeTerm => match self.group_input(true)? {
                    Some(x) => {
                        self.input_fits(s, p, &x)?;
                        Arg::Pipe(x)
                    }
                    None => return Err(format!("{f} takes {p}, as in (main r): {s}")),
                },
                _ if p.rep == Rep::Opt && !matches!(self.peek(), Some(Tok::Name(_))) => Arg::Absent,
                _ => {
                    let n = self.name("a group variable")?;
                    self.group_name(&n)?;
                    Arg::Name(n)
                }
            });
        }
        let e = construct(f, args).ok_or_else(|| unimplemented(s))?;
        if !self.at_close() {
            let input = s.input.as_ref().expect("a number function has an input");
            let named = match self.peek().cloned() {
                // A name for a term is read as a group variable, for the type error.
                Some(Tok::Name(g)) if input.ty != Ty::Group && self.peek_at(1) == Some(&Tok::Close) && !self.group_value(&g) && self.param(&g).is_none() && !self.defs.get(&g).is_some_and(|d| d.input.is_some()) => {
                    self.at += 1;
                    self.group_name(&g)?;
                    Some(group(g))
                }
                _ => None,
            };
            if let Some(g) = named.map_or_else(|| self.group_input(!s.params.is_empty() || input.ty != Ty::Group), |g| Ok(Some(g)))? {
                self.input_fits(s, input, &g)?;
                let Pipe::App(fun, args) = e else { unreachable!("a number function is applied") };
                return Ok(Pipe::App(fun, args.iter().cloned().chain([g]).collect()));
            }
            return Err(format!("{f} takes {}: {s}", s.arity()));
        }
        Ok(e)
    }

    /// An error where `x`, written for the parameter `p` of `s`, has another type: a group
    /// where a term is taken (never converted), or term? where a group is.
    fn input_fits(&self, s: &Sig, p: &Param, x: &Pipe) -> Result<(), String> {
        let shown = match x {
            Pipe::Var(Slot::Local(n, Holds::Group)) => n.clone(),
            x if x.picks() => show_expr(x, 7),
            x => format!("({})", show(x)),
        };
        match (&p.ty, x.picks()) {
            (Ty::Term | Ty::MaybeTerm, false) => Err(format!("{} takes {p}; {shown} is a group — write (main {shown})", s.name)),
            (Ty::Group, true) => Err(format!("{} takes {p}; {shown} is term?, not a group", s.name)),
            _ => Ok(()),
        }
    }

    pub(crate) fn or(&mut self) -> Result<Pipe, String> {
        let mut es = vec![self.and()?];
        while self.peek() == Some(&Tok::Or) {
            self.at += 1;
            es.push(self.and()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { op("||", es) })
    }

    fn and(&mut self) -> Result<Pipe, String> {
        let mut es = vec![self.not()?];
        while self.peek() == Some(&Tok::And) {
            self.at += 1;
            es.push(self.not()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { op("&&", es) })
    }

    fn not(&mut self) -> Result<Pipe, String> {
        if self.pending.is_none() && self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(op("!", vec![self.not()?]));
        }
        let a = self.sum()?;
        self.no_assign()?;
        let Some(&Tok::Cmp(cmp)) = self.peek() else { return Ok(a) };
        self.at += 1;
        Ok(op(cmp, vec![a, self.sum()?]))
    }

    fn sum(&mut self) -> Result<Pipe, String> {
        let mut a = self.product()?;
        while let Some(Tok::Arith(o @ ('+' | '-'))) = self.peek().cloned() {
            self.at += 1;
            a = op(&o.to_string(), vec![a, self.product()?]);
        }
        Ok(a)
    }

    fn product(&mut self) -> Result<Pipe, String> {
        let mut a = self.atom()?;
        while let Some(Tok::Arith(o @ ('*' | '/'))) = self.peek().cloned() {
            self.at += 1;
            a = op(&o.to_string(), vec![a, self.atom()?]);
        }
        Ok(a)
    }

    /// Whether, after the name of a function that gives a number and has no parameters, its
    /// input or the `)` is ahead: `(f)`, `(f t)`, `(f (a | b))`, not `(f < 3)`.
    fn number_input_ahead(&self) -> bool {
        match (self.peek_at(1), self.peek_at(2)) {
            (Some(Tok::Close | Tok::Open), _) => true,
            (Some(Tok::Name(g)), Some(Tok::Close)) => self.input_name(g, false) || self.input_def(g),
            _ => false,
        }
    }

    /// Whether a `|` is ahead before the `)` that closes the parentheses just opened.
    fn bar_inside(&self) -> bool {
        let mut depth = 0;
        for t in &self.toks[self.at..] {
            match t {
                Tok::Open => depth += 1,
                Tok::Close if depth == 0 => return false,
                Tok::Close => depth -= 1,
                Tok::Bar if depth == 0 => return true,
                _ => {}
            }
        }
        false
    }

    /// A pipeline that ends with a step that gives a number, in parentheses (`(lowbits |
    /// size)`), after the `(`.
    fn number_pipe(&mut self) -> Result<Pipe, String> {
        let (stages, tail) = self.stages_of_pipe()?;
        let p = seq_of(stages);
        let Some(e) = tail else { return Err(format!("({}) gives a group, not a number: end it with a step that gives a number, as in (a | size)", show(&p))) };
        Ok(number_seq(p, e))
    }

    /// A number, a name, a call such as `(size (main R))` or `(any C)`, `( expr )` or a
    /// pipeline that ends in a number in parentheses.
    fn atom(&mut self) -> Result<Pipe, String> {
        if let Some(e) = self.pending.take() {
            return Ok(e);
        }
        match self.next() {
            Some(Tok::Num(n)) => Ok(Pipe::Num(n)),
            Some(Tok::Name(n)) => {
                self.no_assign()?;
                if let Some(i) = self.param(&n) {
                    self.use_param(&n, Ty::Num)?;
                    return Ok(param_var(i, n));
                }
                if self.locals.iter().any(|l| *l == n) {
                    return Ok(Pipe::Var(Slot::Local(n, Holds::Num)));
                }
                if let Some(t) = self.fn_var(&n) {
                    return match t {
                        _ if !self.number_fn_name(&n) => Err(format!("{n} holds {t}, which gives a group, not a number")),
                        _ => Ok(Pipe::Var(Slot::Local(n, Holds::Fn(t)))),
                    };
                }
                if self.number_def(&n) && self.defs[&n].params.is_empty() {
                    self.used.push(n.clone());
                    let def = self.defs[&n].def.clone().unwrap();
                    return Ok(Call::bare(&def));
                }
                if self.defs.get(&n).is_some_and(|d| d.run) {
                    return Err(format!("{n} gives a group, not a number: {}; an expression reads variables and number functions", self.sig_named(&n)));
                }
                if self.group_value(&n) {
                    return Err(format!("{n} is a group, not a number: read it with (size {n}) or a function of it, ({n} ...)"));
                }
                let e = name_expr(&n)?;
                Ok(e)
            }
            Some(Tok::Open) => {
                // `(pred t)`: a function value applied to a group.
                if let Some(Tok::Name(k)) = self.peek().cloned()
                    && (self.param(&k).is_some_and(|i| self.params[i].ty.is_none()) || self.number_fn_name(&k))
                    && (matches!(self.peek_at(1), Some(Tok::Name(g)) if self.input_name(g, false)) && self.peek_at(2) == Some(&Tok::Close) || self.peek_at(1) == Some(&Tok::Open))
                {
                    self.at += 1;
                    let f = match self.param(&k) {
                        Some(i) => {
                            self.use_param(&k, Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Num)))?;
                            param_var(i, k)
                        }
                        None => self.fn_read(k),
                    };
                    let input = self.group_input(true)?.expect("an input ahead");
                    self.expect(Tok::Close, ")")?;
                    return Ok(number_seq(input, f));
                }
                // `(size)` and `(size + 1)` are parenthesized expressions, `(minimal r)` a call.
                let call = match self.peek() {
                    Some(Tok::Name(k)) => get(k).filter(|s| {
                        let named = matches!(self.peek_at(1), Some(Tok::Name(_))) && self.peek_at(2) == Some(&Tok::Close);
                        let input = matches!(self.peek_at(1), Some(Tok::Name(g)) if self.group_value(g)) && self.peek_at(2) == Some(&Tok::Close) || self.peek_at(1) == Some(&Tok::Open);
                        let term = s.input.as_ref().is_some_and(|i| i.ty != Ty::Group);
                        s.is_number() && ((!s.params.is_empty() || term) && (s.required() || named) || input)
                    }),
                    _ => None,
                };
                let number_def = match self.peek() {
                    Some(Tok::Name(k)) if self.number_def(k) && (!self.defs[k].params.is_empty() || self.number_input_ahead()) => Some(k.clone()),
                    _ => None,
                };
                let e = match (call, number_def) {
                    (Some(s), _) => {
                        self.at += 1;
                        self.number_call(s)?
                    }
                    (_, Some(k)) => {
                        self.at += 1;
                        self.number_def_call(&k)?
                    }
                    _ if self.bar_inside() => self.number_pipe()?,
                    _ => self.or()?,
                };
                self.expect(Tok::Close, ")")?;
                Ok(e)
            }
            x => Err(format!("expected an expression, found {}", show_tok(x.as_ref()))),
        }
    }
}

/// The variable `n` names, where an assignment to it is allowed.
fn assignable(n: &str) -> Result<usize, String> {
    if let Some(i) = var_index(n) {
        return Ok(i);
    }
    let joined = n.replace('-', "_");
    Err(if n.contains('-') && var_index(&joined).is_some() {
        format!("unknown variable {n}: names use _, not -; write {joined}")
    } else if n == "minimal" {
        "minimal is a condition and cannot be assigned; the setting is prove_minimal".into()
    } else if let Some(s) = get(n).filter(|s| s.is_number()) {
        format!("{n} is computed from the group and cannot be assigned: {s}")
    } else if let Some(s) = get(n) {
        format!("{n} is a function and cannot be assigned: {s}")
    } else {
        format!("unknown variable {n}; known: {}", super::vars::var_names().join(" "))
    })
}

/// Whether a source file may define a variable named `n`: it names nothing yet.
pub fn free_name(n: &str) -> bool {
    !(known_name(n) || resolve(n).is_some() || FEATURES.contains(&n) || ["none", "true", "def", "extern"].contains(&n))
}

pub(crate) fn known_name(n: &str) -> bool {
    var_index(n).is_some() || get(n).is_some() || MACROS.contains(&n)
}

/// `p` on the group value `input` instead of the step's input (`(f x g)`, `g | (f x)`).
pub(crate) fn explicit(input: Pipe, p: Pipe) -> Pipe {
    Pipe::Seq(vec![input, p])
}

const NO_IMPORT: &str = "(import \"PATH\") is a top-level item of a program, not a step";

/// The error for a function that gives a text written as a step.
fn text_step(s: &Sig) -> String {
    format!("{} gives a text, not a group: {s}; a text ends a top-level statement, as in (parse \"x + y\") | {}, or is the input of parse", s.name, s.name)
}

/// The error for a number function written as a step.
fn not_a_step(s: &Sig) -> String {
    format!("{} gives a number, not a group: {s}; a step calls a function that gives a group", s.name)
}

/// The step a name written alone is: a function called without arguments.
fn bare(n: &str) -> Result<Pipe, String> {
    if let Some(s) = get(n) {
        return match s {
            _ if s.is_number() => Err(not_a_step(s)),
            _ if s.is_text() => Err(text_step(s)),
            _ if s.kind() == Kind::FromText => Err(format!("{n} takes a text: ({n} \"x + y\"); {s}")),
            _ if s.required() => Err(format!("{n} needs parentheses: ({n} ...); {s}")),
            _ => construct(n, vec![Arg::Absent; s.params.len()]).ok_or_else(|| unimplemented(s)),
        };
    }
    Err(match n {
        _ if n == "extern" => NO_EXTERN.into(),
        _ if MACROS.contains(&n) => format!("{n} needs parentheses: ({n} ...)"),
        _ if var_index(n).is_some() => format!("{n} is a variable, not a step: assign it with {n} = VALUE, or read it in an expression"),
        _ => format!("unknown pass {n}; known: {}", step_names().join(" ")),
    })
}

/// `e` with a note on a word of `s` such as `time-limit` (outside comments), which reads as a
/// subtraction: the first whose name with `_` is known, else the first not made of numbers.
pub(crate) fn hyphen_hint(e: String, s: &str) -> String {
    let code = s.lines().map(|l| l.split('#').next().unwrap_or("")).collect::<Vec<_>>().join("\n");
    let words: Vec<&str> = code.split(|c: char| !name_char(c) && c != '-').filter(|w| w.contains('-') && w.split('-').all(|p| p.starts_with(name_start))).collect();
    let number = |p: &str| FEATURES.contains(&p) || var_index(p).is_some();
    let known = words.iter().find(|w| known_name(&w.replace('-', "_")));
    let Some(w) = known.or_else(|| words.iter().find(|w| !w.split('-').all(number))) else { return e };
    let joined = w.replace('-', "_");
    if e.contains(&joined) {
        return e;
    }
    let write = if known.is_some() { format!("; write {joined}") } else { String::new() };
    format!("{e} ({w} reads as {}: names use _, not -{write})", w.replace('-', " - "))
}

/// The assignment `name = val`, a `--passes` item `name=val`.
pub fn parse_assign(name: &str, val: &str) -> Result<Pipe, String> {
    let go = || {
        assignable(name)?;
        let defs = super::source::prelude();
        let mut p = Parser::new(lex(val)?, &defs);
        let a = p.assign(name)?;
        p.end()?;
        Ok(a)
    };
    go().map_err(|e| hyphen_hint(e, val))
}

/// The top-level statement `s` of a program: its steps, each with what it gives; `top` the
/// local variables the statements before bound, to which it adds its own.
/// `toks`: `s` lexed, or `None` to lex it here.
pub(crate) fn parse_statement(s: &str, toks: Option<Vec<Tok>>, defs: &Defs, top: &mut TopNames, used: &mut Vec<String>) -> Result<Vec<Top>, String> {
    let go = || {
        let mut p = Parser::new(toks.map_or_else(|| lex(s), Ok)?, defs);
        p.groups = top.groups.clone();
        p.locals = top.locals.clone();
        p.fns = top.fns.clone();
        let tops = p.statement()?;
        Ok((tops, p))
    };
    let (tops, p) = go().map_err(|e: String| hyphen_hint(e, s))?;
    used.extend(p.used);
    *top = TopNames { groups: p.groups, locals: p.locals, fns: p.fns };
    Ok(tops)
}

/// Parses `s` in the pipeline language.
pub fn parse(s: &str) -> Result<Pipe, String> {
    parse_with(s, &super::source::prelude(), &mut Vec::new())
}

/// Parses `s`, where the names of `defs` stand for their pipelines; the names expanded are
/// added to `used`.
pub fn parse_with(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Pipe, String> {
    parse_on(s, defs, used, super::flow::Flow::Group)
}

/// `parse_with` for a pipeline whose input is `input`: a group, or one term.
pub(crate) fn parse_on(s: &str, defs: &Defs, used: &mut Vec<String>, input: super::flow::Flow) -> Result<Pipe, String> {
    let go = || {
        let mut p = Parser::new(lex(s)?, defs);
        let pipe = p.pipe()?;
        p.end()?;
        super::flow::step(&mut super::infer::Infer::none(), &pipe, input)?;
        Ok((pipe, p.used))
    };
    let (pipe, names) = go().map_err(|e| hyphen_hint(e, s))?;
    used.extend(names);
    Ok(pipe)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::ast::{Expanded, op_of, pretty};
    use crate::lang::builtins::{Operator, all, sample};
    use crate::lang::defs::{Named, parse_definition};
    use crate::lang::lexer::is_old_syntax;
    use crate::passes::Passes;

    /// `s` parsed with the names `default.pipe` defines (`rewrite`, `prepass_steps`, ...), as a
    /// pipeline on one term, where a function of a term reads it.
    fn parse(s: &str) -> Result<Pipe, String> {
        parse_on(s, &crate::passes::DEFAULT.1, &mut Vec::new(), crate::lang::flow::Flow::One)
    }

    #[test]
    fn defaults_read_back() {
        let d = Passes::default();
        for (name, p) in [("pipeline", &d.pipeline()), ("prepass", &d.prepass()), ("polish", &d.polish()), ("rewrite", &d.rewrite()), ("simba", &d.simba())] {
            for s in [show(p), pretty(p)] {
                assert_eq!(Passes::parse(&format!("{name}={s}")).unwrap(), d, "{s}");
            }
        }
    }

    #[test]
    fn number_pipelines_and_explicit_inputs() {
        let cond = |s: &str| match parse(&format!("(if {s} id)")).unwrap() {
            Pipe::App(_, args) => args[0].clone(),
            p => panic!("{p:?}"),
        };
        let main = parse("main").unwrap();
        let lowbits_size = Pipe::Seq(vec![Pipe::app("lowbits", vec![]), main.clone(), Pipe::app("size", vec![])]);
        assert_eq!(cond("((lowbits | main | size) > 3)"), op(">", vec![lowbits_size.clone(), Pipe::Num(3)]), "a pipeline that ends in a number is a sequence");
        let Pipe::Seq(main_g) = parse("(save g) | (main g)").unwrap() else { panic!() };
        let Pipe::Drop(main_g, false) = &main_g[1] else { panic!("{main_g:?}") };
        assert_eq!(parse("(save g) | (if (mixed (main g)) id)").unwrap(), Pipe::Seq(vec![Pipe::app("save", vec![Pipe::Name("g".into())]), Pipe::app("if", vec![Pipe::app("mixed", vec![(**main_g).clone()]), Pipe::id(), Pipe::id()])]), "the input written follows the arguments");
        assert_eq!(cond("(minimal (lowbits))"), Pipe::app("minimal", vec![Pipe::app("lowbits", vec![])]));
        assert_eq!(cond("(size main)"), Pipe::app("size", vec![main]), "main alone where a term is wanted is main of the input");
        for s in ["(if ((lowbits | main | size) > 3) id)", "(save g) | (if (mixed (main g)) id)", "(save g) | (if (((main g) | mixed) + (minimal g) + (size (index 1 g))) id)", "(if (rewrite | minimal) id)", "(save g) | (if (same (main g) main) id)", "(if (size main) id)", "main | (prepass id)"] {
            assert_eq!(show(&parse(s).unwrap()), s, "{s}");
        }
    }

    #[test]
    fn forms_and_conditions() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        same("lowbits | rewrite | tfunc", "(seq lowbits rewrite tfunc)");
        same("(if (mixed main) rewrite)", "(if (mixed main) rewrite id)");
        same("(if (!minimal || (tiny main)) (rewrite | tfunc))", "(if (!minimal || ((tiny main))) (seq rewrite tfunc) id)");
        same("(filter (mul >= 4 && vars < 3))", "(filter ((mul >= 4) && (vars < 3)))");
        assert_eq!(parse("(off lowbits relate)").unwrap(), Expanded::switches(false, &["lowbits", "relate"]));
        same("(fix restarts (prepass prepass_steps) | egglog)", "(fix restarts ((prepass prepass_steps) | egglog))");
        same("# comment
(best 2 rewrite (scope unshift)) # more", "(best 2 rewrite (scope unshift))");
        let p = parse("(filter (size > (size (main f)) * 3/4 || (same (main r))))").unwrap();
        let Pipe::App(_, f) = &p else { panic!("{p:?}") };
        let Some((Operator::Or, cs)) = op_of(&f[0]) else { panic!("{p:?}") };
        let main = |r: &str| {
            let Pipe::App(_, a) = parse(&format!("(filter (size (main {r})))")).unwrap() else { panic!() };
            let Pipe::App(_, m) = &a[0] else { panic!() };
            m[0].clone()
        };
        assert_eq!(cs[1], Pipe::app("same", vec![main("r")]));
        let three_quarters = op("/", vec![op("*", vec![Pipe::app("size", vec![main("f")]), Pipe::Num(3)]), Pipe::Num(4)]);
        assert_eq!(cs[0], op(">", vec![Pipe::app("size", vec![]), three_quarters]));
        for ok in [
            "(if !(minimal && (tiny main)) id)",
            "(filter (any (mul >= 2)))",
            "(filter (all !tiny && size * 2 + 1 <= (size (main t)) - vars))",
            "(fix (restarts - 1) (prepass prepass_steps))",
            "(best (keep + 1) id)",
            "(if ((size main) < split_size) id)",
            "(wins (2 * 4) id)",
            "(filter !(same (main r)))",
            "(if (mul main) id)",
            "(filter (mul + tiny))",
            "(fix (mixed main) id)",
            "(if (((mul main) >= 4) + 1) id)",
            "(best ((size main) > 3) id)",
            "(if (none > (size main)) id)",
            "(fix (time_limit / 2 - ((mul main) < 1)) id)",
            "main | (if mixed id)",
            "main | (fix size id)",
        ] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
        }
        assert_eq!(show(&parse("(if !((mul main) < 1 || (tiny main)) id)").unwrap()), "(if !((mul main) < 1 || (tiny main)) id)");
        assert_eq!(show(&parse("(fix (2 * (keep + 1)) id)").unwrap()), "(fix (2 * (keep + 1)) id)");
        assert!(is_old_syntax("seq(a,b)") && !is_old_syntax("(seq a b)"));
    }

    #[test]
    fn numbers_and_hyphens() {
        let p = parse("main | split_runs = size-mul").unwrap();
        let Pipe::Seq(steps) = &p else { panic!() };
        assert_eq!(steps[1], Pipe::assign(var_index("split_runs").unwrap(), op("-", vec![Pipe::app("size", vec![]), Pipe::app("mul", vec![])])));
        assert_eq!(parse("main | (if (restarts-1 > size-mul) id)").unwrap(), parse("main | (if (restarts - 1 > size - mul) id)").unwrap());
        assert_eq!(parse("(if 1 none id)").unwrap(), Pipe::app("if", vec![Pipe::Num(1), resolve("none").unwrap(), Pipe::id()]));
        for ok in ["(if 1 none rewrite)", "(filter !0)", "(if (any 1) none)", "(if (1 && (mixed main)) id)"] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
        }
        assert_eq!(show(&parse("(if 1 none rewrite)").unwrap()), "(if 1 none rewrite)");
        assert!(parse_assign("time-limit", "5").unwrap_err().contains("write time_limit"));
    }

    #[test]
    fn assignments() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        let at = |n: &str| var_index(n).unwrap();
        let assign = |n: &str, v: Pipe| Pipe::assign(at(n), v);
        assert_eq!(parse("split_runs = 4").unwrap(), assign("split_runs", Pipe::Num(4)));
        same("split_runs=4 | rewrite", "split_runs = 4 | rewrite");
        same("(split_runs=4)", "split_runs   =   4");
        let p = parse("split_runs = vars * 2 + 1 | (split_bits rewrite)").unwrap();
        let rhs = op("+", vec![op("*", vec![Pipe::app("vars", vec![]), Pipe::Num(2)]), Pipe::Num(1)]);
        assert_eq!(p, Pipe::Seq(vec![assign("split_runs", rhs), parse("(split_bits rewrite)").unwrap()]));
        assert_eq!(parse("rewrites = none").unwrap(), assign("rewrites", Pipe::Num(NONE)));
        assert_eq!(parse("relate = 0").unwrap(), assign("relate", Pipe::Num(0)));
        assert_eq!(parse("cut = 1").unwrap(), assign("cut", Pipe::Num(1)));
        assert_eq!(parse("split_runs = none + 1").unwrap(), assign("split_runs", op("+", vec![Pipe::Num(NONE), Pipe::Num(1)])));
        assert_eq!(parse("split_runs = mixed").unwrap(), assign("split_runs", Pipe::app("mixed", vec![])));
        same("(if mixed split_runs = 3)", "(if mixed (split_runs = 3))");
        same("(union split_runs = 3 rewrite)", "(union (split_runs = 3) rewrite)");
        same("semi_leaves = split_runs - 1 | rewrite", "semi_leaves = (split_runs - 1) | rewrite");
        for ok in [
            "split_runs = 4 | rewrite",
            "split_runs = vars * 2 | (split_bits rewrite)",
            "rewrites = none | relate = 0 | cut = 1 | time_limit = (size (main t)) * 10 | rewrite",
            "(if mixed semi_leaves = 2 (time_limit = none | rewrite))",
            "(best 1 (bit_split_budget = cand_bit_splits | rewrite) (time_limit = time_limit / 2 | rewrite))",
            "semi_shapes = 0 | rewrite",
            "keep = 1 | restarts = restarts - 1 | iter_limit = 3 | match_limit = 8 | prove_minimal = 0 | rewrite",
            "(if (rerun_input && printed && !relate) id)",
            "split_runs = relate + cut | rewrite",
        ] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
            assert_eq!(parse(&pretty(&p)).unwrap(), p, "{ok}: {}", pretty(&p));
        }
        assert_eq!(show(&parse("split_runs=vars*2|rewrite").unwrap()), "split_runs = vars * 2 | rewrite");
    }

    #[test]
    fn every_builtin_parses_to_its_application() {
        for s in all().iter().filter(|s| !s.is_text()) {
            let call = sample(s);
            let p = match s.is_number() {
                true => {
                    let Pipe::App(_, args) = parse(&format!("(filter {call})")).unwrap_or_else(|e| panic!("{call}: {e}")) else { panic!("{call}") };
                    args[0].clone()
                }
                false => parse(&call).unwrap_or_else(|e| panic!("{call}: {e}")),
            };
            match &p {
                Pipe::App(Fun::Builtin(b) | Fun::Op(_, b), _) => assert_eq!(b.name, s.name, "{}", s.decl()),
                Pipe::Seq(_) => assert_eq!(s.name, "seq"),
                Pipe::Expanded(m) => assert_eq!(m.head, s.name),
                p => panic!("{}: {p:?}", s.decl()),
            }
        }
        for s in all().iter().filter(|s| s.is_text()) {
            let tops = parse_statement(&format!("(parse \"x\") | {}", s.name), None, &Defs::new(), &mut TopNames::default(), &mut Vec::new()).unwrap();
            assert!(matches!(&tops.last().unwrap().pipe, Pipe::App(Fun::Builtin(b), _) if b.name == s.name), "{}", s.decl());
        }
    }

    #[test]
    fn calls_follow_signatures() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        let id = Pipe::id;
        same("(egglog)", "egglog");
        assert_eq!(parse("(egglog later)").unwrap(), Pipe::app("egglog", vec![Pipe::Name("later".into())]));
        same("(fix 3 lowbits | rewrite)", "(fix 3 (lowbits | rewrite))");
        same("(tag t lowbits | rewrite)", "(tag t (lowbits | rewrite))");
        same("(if (size) id)", "(if size id)");
        same("(relate = 0 | rewrite)", "relate = 0 | rewrite");
        same("(rewrite | unshift)", "rewrite | unshift");
        assert_eq!(parse("(if (size + 1) id)").unwrap(), Pipe::app("if", vec![op("+", vec![Pipe::app("size", vec![]), Pipe::Num(1)]), id(), id()]));
        same("(filter (any mul > 1 && tiny))", "(filter (any (mul > 1 && tiny)))");
        assert_eq!(parse("(if lowbits id)").unwrap(), Pipe::app("if", vec![Pipe::global(var_index("lowbits").unwrap()), id(), id()]), "a switch in an expression");
        for (bad, msg) in [
            ("mixed", "mixed gives a number, not a group: (mixed t:term?) num"),
            ("(any 1)", "any gives a number"),
            ("(size (main t))", "size gives a number"),
            ("split_runs", "split_runs is a variable, not a step"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn a_slash_between_names_divides() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        same("split_runs = split_runs/2 | rewrite", "split_runs = split_runs / 2 | rewrite");
        same("(if (size/2 > vars/3) id)", "(if (size / 2 > vars / 3) id)");
        assert!(lex("semi_shapes").unwrap() == [Tok::Name("semi_shapes".into())] && lex("a/b").unwrap().len() == 3, "names have no /");
    }

    #[test]
    fn function_type_annotations() {
        let def = |s: &str| parse_definition(s, &Defs::new(), &mut Vec::new());
        assert_eq!(def("(def (f k:num) (if (size <= k) lowbits))").unwrap().params[0].ty, Ty::Num);
    }

    #[test]
    fn group_assignments() {
        let bind = |n: &str, p: &str| Pipe::Bind(Slot::Local(n.into(), Holds::Group), Arc::new(parse(p).unwrap()));
        assert_eq!(parse("t = (lowbits | unshift)").unwrap(), bind("t", "lowbits | unshift"));
        assert_eq!(parse("t = rewrite | unshift").unwrap(), Pipe::Seq(vec![bind("t", "rewrite"), parse("unshift").unwrap()]));
        assert_eq!(parse("t = u | rewrite").unwrap(), Pipe::Seq(vec![Pipe::Bind(Slot::Local("t".into(), Holds::Group), Arc::new(group("u".into()))), parse("rewrite").unwrap()]), "t = u binds u's group");
        assert_eq!(show(&parse("(save u) | t = (u | unshift)").unwrap()), "(save u) | t = (u | unshift)");
        assert_eq!(parse("t = unshift").unwrap(), bind("t", "unshift"), "unshift after a group variable is the pass");
        assert_eq!(parse("t = (relate = 0 | rewrite)").unwrap(), bind("t", "relate = 0 | rewrite"));
        assert_eq!(parse("t = (best 1 id rewrite)").unwrap(), bind("t", "(best 1 id rewrite)"));
        assert!(matches!(parse("keep = keep + 1").unwrap(), Pipe::Bind(Slot::Global(_), _)), "a variable that holds a number takes an expression");
        assert!(matches!(parse("relate = (size > 3)").unwrap(), Pipe::Bind(Slot::Global(_), _)));
        for s in ["t = (lowbits | unshift) | (t | rewrite)", "t = rewrite | unshift", "(if mixed t = rewrite) | u = (v = t) | (filter (same (main u)))", "(seq t = (x = u))", "t = u | rewrite"] {
            assert_eq!(show(&parse(s).unwrap()), s, "{s}");
            assert_eq!(parse(&show(&parse(s).unwrap())).unwrap(), parse(s).unwrap(), "{s}");
        }
        let lets = |item: &str| {
            let d = parse_definition(item, &Defs::new(), &mut Vec::new()).unwrap();
            let mut defs = Defs::new();
            defs.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: Vec::new(), def: None, input: None });
            defs
        };
        assert_eq!(parse_with("t = g", &lets("(let g lowbits | unshift)"), &mut Vec::new()).unwrap(), bind("t", "lowbits | unshift"));
        let d = parse_definition("(def (f p:pipe g:group) g | p)", &Defs::new(), &mut Vec::new()).unwrap();
        assert_eq!((d.input.as_deref(), def_sig(&d.name, &d.params).to_string().as_str()), (Some("g"), "(f p:pipe g:group) group"), "a last group parameter the body starts with is its input");
        assert!(parse_assign("t", "rewrite").unwrap_err().contains("unknown variable t"), "a --passes item NAME=VALUE is to a variable that holds a number");
    }

    #[test]
    fn nested_assignments_parse_once() {
        let (mut group, mut number) = ("rewrite".to_string(), "keep = 1".to_string());
        for i in 0..24 {
            group = format!("t{i} = ({group} | unshift)");
            number = format!("keep = (relate = 0 | ({number}) | size) + 1");
        }
        let start = std::time::Instant::now();
        for s in [&group, &number] {
            let p = parse(s).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{s}");
        }
        assert!(matches!(parse(&number).unwrap(), Pipe::Bind(Slot::Global(_), _)));
        assert!(matches!(parse(&group).unwrap(), Pipe::Bind(Slot::Local(_, Holds::Group), _)));
        assert!(start.elapsed() < std::time::Duration::from_secs(2), "{:?}", start.elapsed());
        for (s, msg) in [("keep = ((lowbits | size) + 1)", ""), ("t = ((lowbits | unshift) | tfunc)", ""), ("t = ((lowbits | size) | tfunc)", "gives num; tfunc takes t:term"), ("t = (u)", "unknown name u in an expression"), ("t = (time-limit 3)", "write time_limit = N")] {
            match parse(s) {
                Ok(_) => assert!(msg.is_empty(), "{s}"),
                Err(e) => assert!(!msg.is_empty() && e.contains(msg), "{s}: {e}"),
            }
        }
    }

    #[test]
    fn operators_are_applications_of_builtins() {
        let p = parse("(filter (size + 1 > 2 && !mixed || vars == 3))").unwrap();
        let Pipe::App(_, f) = &p else { panic!("{p:?}") };
        let Some((Operator::Or, ors)) = op_of(&f[0]) else { panic!("{p:?}") };
        let Some((Operator::And, ands)) = op_of(&ors[0]) else { panic!("{p:?}") };
        assert!(matches!(op_of(&ands[1]), Some((Operator::Not, [_]))));
        let Pipe::App(Fun::Op(_, gt), _) = &ands[0] else { panic!("{p:?}") };
        assert_eq!(gt.sig.to_string(), "(> a:num b:num) num");
        assert_eq!(gt.sig.kind(), Kind::Op);
        assert_eq!(ands[0], op(">", vec![op("+", vec![Pipe::app("size", vec![]), Pipe::Num(1)]), Pipe::Num(2)]));
        assert_eq!(show(&p), "(filter (size + 1 > 2 && !mixed || vars == 3))", "printed infix as written");
        assert!(get("&&").unwrap().params[1].ty == Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Num)), "&& and || declare their later operands as functions of the input");
        assert!(parse("(+ 1 2)").is_err() && resolve("+").is_none(), "an operator is written infix only");
    }

    #[test]
    fn every_variable_binds_with_one_node() {
        let p = parse("keep = 2 | n = (size * 2) | t = rewrite | f:term->num = (size <= n) | (filter f) | (fix n t)").unwrap();
        let Pipe::Seq(steps) = &p else { panic!("{p:?}") };
        let slots: Vec<&Slot> = steps[..4].iter().map(|s| if let Pipe::Bind(x, _) = s { x } else { panic!("{s:?}") }).collect();
        assert_eq!(slots[0], &Slot::Global(var_index("keep").unwrap()));
        assert_eq!(slots[1], &Slot::Local("n".into(), Holds::Num));
        assert_eq!(slots[2], &Slot::Local("t".into(), Holds::Group));
        assert_eq!(slots[3], &Slot::Local("f".into(), Holds::Fn(Ty::parse("term->num").unwrap())));
        let Pipe::App(_, filter) = &steps[4] else { panic!() };
        assert_eq!(filter[0], Pipe::Var(Slot::Local("f".into(), Holds::Fn(Ty::parse("term->num").unwrap()))), "a read has the slot its binding has");
        assert_eq!(show(&p), "keep = 2 | n = size * 2 | t = rewrite | f:term->num = size <= n | (filter f) | (fix n t)");
    }
}
