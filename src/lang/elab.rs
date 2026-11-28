//! Elaboration: the syntax tree (`syntax`) of a pipeline, a statement, an assignment or a
//! definition made into `ast::Pipe`. Names are resolved by what they name, and each position
//! is read by what it takes (`docs/lang/evaluation.md`): a number, a group, a tuple, a text or
//! a function value.

use super::ast::{Fun, Holds, Pipe, Slot, gives_tuple, piped, show, show_expr, stage, starts_with_value, value_ty};
use super::builtins::{MACROS, get, number_names, resolve, step_names};
use super::defs::{Call, Def, Defs, Subst, def_sig, instance, intern, sig_of};
use super::host::FEATURES;
use super::infer::ParamUse;
use super::lexer::{NO_EXTERN, Tok, lex, name_char, name_start, show_tok};
use super::macros::smallest;
use super::reader::NO_ASSIGN;
use super::run::{Gives, Top};
use super::syntax::{Lhs, Node, Pipeline, Stage, Syn};
use super::types::{Kind, Param, Rep, Sig, Ty};
use super::vars::{NONE, is_switch, var_index};
use std::sync::Arc;

const NO_WITH: &str = "(with KEY=VALUE ... p) is no longer read: write (KEY = VALUE | ... | p), as in (rewrites = 8 | semi_leaves = 2 | rewrite); with's bit_splits=N is bit_split_budget = N";
const NO_TIME_LIMIT: &str = "(time-limit N) is no longer read: write time_limit = N, or time_limit = none for no limit";
const NO_TRUE: &str = "true is no longer a condition: write 1, or (any 1) for true only on a group that is not empty";
const NO_IMPORT: &str = "(import \"PATH\") is a top-level item of a program, not a step";

/// An argument of a call, as its parameter's type reads it.
#[derive(Clone)]
pub(crate) enum Arg {
    Num(Pipe),
    Name(String),
    Pipe(Pipe),
    Pipes(Vec<Pipe>),
    Absent,
}

/// The stages of a pipeline: the items of the first one and the stages after it; none where
/// `first` is empty.
#[derive(Clone, Copy)]
pub(crate) struct Stages<'s> {
    first: &'s [Syn<'s>],
    rest: &'s [Stage<'s>],
}

impl<'s> Stages<'s> {
    pub(crate) fn of(p: &'s Pipeline<'s>) -> Stages<'s> {
        Stages { first: &p.stages[0].items, rest: &p.stages[1..] }
    }

    pub(crate) fn len(&self) -> usize {
        if self.first.is_empty() { 0 } else { 1 + self.rest.len() }
    }

    pub(crate) fn get(&self, i: usize) -> Option<&'s [Syn<'s>]> {
        match i {
            0 => Some(self.first).filter(|f| !f.is_empty()),
            i => self.rest.get(i - 1).map(|s| &s.items[..]),
        }
    }

    pub(crate) fn at(&self, i: usize) -> &'s [Syn<'s>] {
        self.get(i).expect("a stage")
    }

    /// The stages from the one at `i` on.
    pub(crate) fn from(&self, i: usize) -> Stages<'s> {
        match i {
            0 => *self,
            i if i > self.rest.len() => Stages { first: &[], rest: &[] },
            i => Stages { first: &self.rest[i - 1].items, rest: &self.rest[i..] },
        }
    }
}

/// The arguments of a call being read: the items after its name, and the stages after them in
/// the same parentheses, which only the last pipeline parameter reads.
pub(crate) struct Items<'s> {
    items: &'s [Syn<'s>],
    k: usize,
    end: usize,
    rest: &'s [Stage<'s>],
}

impl<'s> Items<'s> {
    /// The arguments of the call `x`, `(NAME ...)`.
    pub(crate) fn of(x: &'s Syn<'s>) -> Items<'s> {
        let (s, rest) = x.head_stage().expect("a call in parentheses");
        Items { items: &s.items, k: 1, end: s.end, rest }
    }

    pub(crate) fn peek(&self) -> Option<&'s Syn<'s>> {
        self.items.get(self.k)
    }

    pub(crate) fn after(&self) -> Option<&'s Syn<'s>> {
        self.items.get(self.k + 1)
    }

    pub(crate) fn next(&mut self) -> Option<&'s Syn<'s>> {
        let x = self.items.get(self.k);
        self.k += 1;
        x
    }

    pub(crate) fn at_close(&self) -> bool {
        self.k >= self.items.len() && self.rest.is_empty()
    }

    pub(crate) fn at_bar(&self) -> bool {
        self.k >= self.items.len() && !self.rest.is_empty()
    }

    /// The token the next item starts at, or that ends the items.
    pub(crate) fn tok(&self) -> usize {
        self.peek().map_or(self.end, |x| x.at)
    }

    /// Whether the next item is the last one before a `|`.
    pub(crate) fn before_bar(&self) -> bool {
        self.k + 1 == self.items.len() && !self.rest.is_empty()
    }

    /// Whether the next item is the last one before the `)`.
    pub(crate) fn before_close(&self) -> bool {
        self.k + 1 == self.items.len() && self.rest.is_empty()
    }
}

/// The application of the built-in function `f` to the arguments read by its parameters:
/// for `seq` a sequence, for `smallest` the macro expanded, for `if` without its second
/// branch `id` there; `None` when no Rust code implements `f`.
pub(crate) fn construct(f: &str, args: Vec<Arg>) -> Option<Pipe> {
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
        let vars = super::vars::var_names();
        Err(super::warn::unknown(format!("unknown name {n} in an expression"), n, number_names().chain(vars)))
    }
}

/// The type of the value `e` gives: a text or a number.
fn expr_ty(e: &Pipe) -> Ty {
    match e {
        Pipe::Text(_) => Ty::Text,
        Pipe::App(Fun::Builtin(b), _) if b.sig.is_text() => Ty::Text,
        _ => Ty::Num,
    }
}

/// The right side of an assignment, by the type of what it gives.
pub(crate) enum Rhs {
    Num(Pipe),
    Group(Pipe),
}

pub(crate) fn seq_of(mut stages: Vec<Pipe>) -> Pipe {
    if stages.len() == 1 { stages.pop().unwrap() } else { Pipe::Seq(stages) }
}

/// Whether the stage `p` gives a number or a text: a pipeline in parentheses that ends in one.
fn gives_value(p: &Pipe) -> bool {
    matches!(p, Pipe::Seq(_)) && super::eval::step_kind(p) == super::eval::StepKind::Value && !gives_tuple(p)
}

/// The pipeline `p | e` that gives the number `e` gives, `p` a sequence written out: `p` and
/// its steps are one scope alike, and it shows the same.
pub(crate) fn number_seq(p: Pipe, e: Pipe) -> Pipe {
    let mut ps = match p {
        Pipe::Seq(ps) if ps.is_empty() => return e,
        Pipe::Seq(ps) if ps.len() > 1 => ps,
        p => vec![p],
    };
    ps.push(e);
    Pipe::Seq(ps)
}

/// The leftmost operand of the expression `x` and the token after it, where `x` applies an
/// operator.
fn leftmost<'s>(x: &'s Syn<'s>) -> Option<(&'s Syn<'s>, usize)> {
    fn first<'s>(x: &'s Syn<'s>) -> &'s Syn<'s> {
        match &x.node {
            Node::Op(_, a, _) => first(a),
            Node::And(es) | Node::Or(es) => first(&es[0]),
            _ => x,
        }
    }
    match &x.node {
        Node::Op(..) | Node::And(_) | Node::Or(_) => {
            let a = first(x);
            Some((a, a.end))
        }
        _ => None,
    }
}

/// Where an expression argument (a number, a name, `!` and an argument, or one in
/// parentheses) ends before the end of `x`: the token of the operator after it.
fn earg_cut(x: &Syn) -> Option<usize> {
    match &x.node {
        Node::Not(e) => earg_cut(e),
        _ => leftmost(x).map(|(_, at)| at),
    }
}

pub(crate) struct Elab<'a> {
    pub(crate) toks: &'a [Tok],
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
    /// The local variables that hold a tuple bound so far in the text, and their types.
    pub(crate) tuples: Vec<(String, Ty)>,
    /// The parameters without a type written alone in a position of a tuple, whose type the
    /// tuple's takes once the parameter's other uses give it.
    pub(crate) holes: Vec<String>,
    /// Reading a top-level statement, whose last step may give a text.
    pub(crate) text_tail: bool,
    /// The step read has an input: not at the top level of a program before a step gives a
    /// value. A function that gives a number written alone is applied to it only then.
    pub(crate) input: bool,
    /// Reading the top level of a statement, outside parentheses.
    pub(crate) top: bool,
}

/// The local variables the top-level statements of a program bound so far, which the later
/// ones read.
#[derive(Clone, Default)]
pub(crate) struct TopNames {
    groups: Vec<String>,
    locals: Vec<String>,
    fns: Vec<(String, Ty)>,
    /// A statement gave a value, which the later ones take as their input.
    pub(crate) value: bool,
    tuples: Vec<(String, Ty)>,
}

impl<'a> Elab<'a> {
    pub(crate) fn new(toks: &'a [Tok], defs: &'a Defs) -> Elab<'a> {
        Elab { toks, defs, used: Vec::new(), params: Vec::new(), groups: Vec::new(), fns: Vec::new(), locals: Vec::new(), tuples: Vec::new(), holes: Vec::new(), text_tail: false, input: true, top: false }
    }

    pub(crate) fn tok(&self, i: usize) -> String {
        show_tok(self.toks.get(i))
    }

    /// The error for items left after a step: past the end of a top-level statement, or
    /// before the `)`.
    fn leftover(&self, at: usize) -> String {
        match self.top {
            true => format!("unexpected {} after the pipeline", self.tok(at)),
            false => format!("expected ), found {}", self.tok(at)),
        }
    }

    fn one_item(&self, s: &[Syn]) -> Result<(), String> {
        match s.get(1) {
            Some(x) => Err(self.leftover(x.at)),
            None => Ok(()),
        }
    }

    /// An error where items are left before the `)` of a call.
    pub(crate) fn close(&self, c: &Items) -> Result<(), String> {
        match c.peek() {
            Some(x) => Err(format!("expected ), found {}", self.tok(x.at))),
            None if !c.rest.is_empty() => Err(format!("expected ), found {}", self.tok(c.end))),
            None => Ok(()),
        }
    }

    /// `f` read inside parentheses.
    pub(crate) fn inside<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let top = std::mem::replace(&mut self.top, false);
        let r = f(self);
        self.top = top;
        r
    }

    /// Whether `n` is a group value: a group parameter, or a group variable bound before in
    /// the text that names nothing else.
    pub(crate) fn group_value(&self, n: &str) -> bool {
        match self.param(n) {
            Some(i) => matches!(self.params[i].ty, Some(Ty::Group | Ty::Term)),
            None => self.groups.iter().any(|g| g == n) && !self.defs.contains_key(n) && !known_name(n) && resolve(n).is_none(),
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

    /// An explicit input next in a call: a group value's name, a step in parentheses (run on
    /// the step's input unless it starts with a value), or with `loose` a name that names
    /// nothing else, read as a group variable (the checks find it unbound); `None` (nothing
    /// read) otherwise.
    fn group_input(&mut self, c: &mut Items) -> Result<Option<Pipe>, String> {
        self.group_input_of(c, true)
    }

    fn group_input_of(&mut self, c: &mut Items, loose: bool) -> Result<Option<Pipe>, String> {
        let Some(x) = c.peek() else { return Ok(None) };
        match &x.node {
            Node::Name(n) if self.input_def(n) => {
                c.k += 1;
                self.used.push(n.to_string());
                self.call_of(n, Vec::new(), None).map(Some)
            }
            Node::Name(n) if self.input_name(n, loose) => {
                c.k += 1;
                self.use_param(n, Ty::Group)?;
                Ok(Some(group(n.to_string())))
            }
            Node::Paren(_) | Node::Tuple(_) => {
                c.k += 1;
                self.stage(x).map(Some)
            }
            _ => Ok(None),
        }
    }

    /// Whether an explicit input is next in `c`, as `group_input` reads it.
    fn input_next(&self, c: &Items, loose: bool) -> bool {
        match c.peek().map(|x| &x.node) {
            Some(Node::Name(n)) => self.input_name(n, loose) || self.input_def(n),
            Some(Node::Paren(_) | Node::Tuple(_)) => true,
            _ => false,
        }
    }

    /// Whether `n` names no variable, function, definition or word of the language.
    pub(crate) fn unknown(&self, n: &str) -> bool {
        !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || ["none", "true", "def", "extern"].contains(&n))
    }

    /// The type of the function variable `n` bound before in the text.
    pub(crate) fn fn_var(&self, n: &str) -> Option<Ty> {
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

    /// Whether `n` is a function defined whose body is an expression.
    fn number_def(&self, n: &str) -> bool {
        self.defs.get(n).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_some())
    }

    /// The function the next item, a name alone, stands for where a function of type `want` is wanted:
    /// a parameter not typed otherwise, which gets that type unless annotated, or a function
    /// variable; `None` (nothing read) for another name. `whose` names the parameter the
    /// argument is for.
    fn function_name(&mut self, c: &mut Items, want: &Ty, whose: &dyn Fn() -> String) -> Result<Option<Pipe>, String> {
        let Some(n) = c.peek().and_then(Syn::name) else { return Ok(None) };
        if let Some(i) = self.param(n) {
            if self.params[i].ty.as_ref().is_some_and(|t| !matches!(t, Ty::Fn(..))) {
                return Ok(None);
            }
            c.k += 1;
            self.use_param(n, want.clone())?;
            return Ok(Some(param_var(i, n.into())));
        }
        let Some(t) = self.fn_var(n) else { return Ok(None) };
        c.k += 1;
        if !t.fits(want) {
            return Err(format!("{}; {n} is {t}", whose()));
        }
        Ok(Some(Pipe::Var(Slot::Local(n.into(), Holds::Fn(t)))))
    }

    /// The function variable `n` read.
    pub(crate) fn fn_read(&self, n: String) -> Pipe {
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

    /// The signature of the function `n` defined.
    pub(crate) fn sig_named(&self, n: &str) -> Sig {
        let d = &self.defs[n];
        let mut sig = d.def.as_ref().map_or_else(|| def_sig(n, &d.params), |d| sig_of(d));
        if d.input.is_some() && d.pipe.picks() {
            sig.result = Ty::MaybeTerm;
        }
        sig
    }

    /// The signature of the function `n` names when it lacks at most its input written alone:
    /// a built-in, a `def` (one that gives a number without parameters) or a `let`; `None` for
    /// another name.
    pub(crate) fn bare_fn(&self, n: &str) -> Option<Sig> {
        if self.param(n).is_some() || self.locals.iter().any(|l| l == n) || self.fn_var(n).is_some() {
            return None;
        }
        if let Some(s) = get(n) {
            return (!s.is_op() && !s.required()).then(|| s.clone());
        }
        if !self.defs.contains_key(n) {
            return None;
        }
        let s = self.sig_named(n);
        (!s.required() && (!self.number_def(n) || self.defs[n].params.is_empty())).then_some(s)
    }

    /// The function `n` names written as a value, without arguments: a function variable, or a
    /// built-in or defined function that gives candidates; `None` for another name.
    fn function_value(&mut self, n: &str) -> Option<Pipe> {
        if self.fn_var(n).is_some() {
            return Some(self.fn_read(n.to_string()));
        }
        if let Some(b) = super::builtins::builtin(n).filter(|b| !b.sig.is_op()) {
            return Some(Pipe::FnValue(Arc::new(Pipe::App(Fun::Builtin(b), Vec::new().into()))));
        }
        let d = self.defs.get(n)?;
        // A `let` or an `@inline` function written out where it is used has no `Def`: one stands
        // for it here, which only shows.
        let def = d.def.clone().unwrap_or_else(|| {
            let body = Arc::new(d.pipe.clone());
            Arc::new(Def { name: n.into(), params: d.params.clone(), body, inline: false, flat: d.flat, input: None, step: true, steps: false, value: None, implicit: None, tuple: None, timed: false, slot: None })
        });
        self.used.push(n.to_string());
        Some(Pipe::FnValue(Arc::new(Call::bare(&def))))
    }

    /// An error where `n` cannot be a new local variable: a parameter, or the name of a
    /// variable of `VARS`, a function, a definition or a word of the language.
    pub(crate) fn local_name(&self, n: &str) -> Result<(), String> {
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

    /// What kind of local variable `n` is bound as so far in the text.
    pub(crate) fn local_kind(&self, n: &str) -> Option<&'static str> {
        if self.groups.iter().any(|g| g == n) {
            Some("group")
        } else if self.locals.iter().any(|l| l == n) {
            Some("number")
        } else if self.fn_var(n).is_some() {
            Some("function")
        } else if self.tuples.iter().any(|(t, _)| t == n) {
            Some("tuple")
        } else {
            None
        }
    }

    /// `n = f`: the function value `f` of type `ty` bound to the local variable `n`.
    fn bind_fn(&mut self, n: &str, f: Pipe, ty: Ty) -> Result<Pipe, String> {
        if self.groups.iter().any(|g| g == n) {
            return Err(format!("{n} is a group variable, so it cannot hold a function value"));
        }
        if self.locals.iter().any(|l| l == n) {
            return Err(format!("{n} is a number variable, so it cannot hold a function value"));
        }
        if self.tuples.iter().any(|(t, _)| t == n) {
            return Err(format!("{n} is a tuple variable, so it cannot hold a function value"));
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
        if self.tuples.iter().any(|(t, _)| t == n) {
            return Err(format!("{n} is a tuple variable, so it cannot name a group variable"));
        }
        if self.locals.iter().any(|l| l == n) {
            return Err(format!("{n} is a number variable, so it cannot name a group variable"));
        }
        match var_index(n) {
            Some(_) => Err(format!("{n} is a variable that holds a number, so it cannot name a group variable")),
            None => Ok(()),
        }
    }

    /// The call of the function `n` defined with `args` read by its parameters, and for one
    /// put in place that starts from its input, that input when written (`(main r)`), else the
    /// step's (`main`).
    pub(crate) fn call_of(&self, n: &str, args: Vec<Arg>, input: Option<Pipe>) -> Result<Pipe, String> {
        let d = &self.defs[n];
        let args: Vec<Pipe> = args
            .into_iter()
            .zip(&d.params)
            .map(|(a, p)| match a {
                Arg::Name(s) if p.ty == Ty::Group => group(s),
                Arg::Name(s) => Pipe::Name(s),
                Arg::Pipe(p) | Arg::Num(p) => p,
                _ => unreachable!("a parameter of a def is a pipeline, an expression, a group or a name"),
            })
            .collect();
        let open = |s: &str| self.param(s).is_some();
        match &d.def {
            Some(def) => Ok(Pipe::App(Fun::Def(Arc::new(Call { body: instance(def, &args, &open)?, def: def.clone() })), args.into())),
            None => {
                let body = Subst::new(&d.params, &args, true, true, &open).pipe(&d.pipe)?;
                if d.input.is_none() {
                    return Ok(body);
                }
                let Pipe::Seq(mut ps) = body else { unreachable!("a body that starts from its input is a sequence") };
                ps.remove(0);
                let rest = seq_of(ps);
                let steps = vec![match &input {
                    Some(i) => explicit(i.clone(), rest),
                    None => rest,
                }];
                Ok(Pipe::Expanded(Box::new(super::ast::Expanded { head: intern(n), args: args.into_iter().chain(input).collect(), steps, scoped: false, timed: false })))
            }
        }
    }

    /// A pipeline that gives a group.
    pub(crate) fn pipe(&mut self, ss: Stages) -> Result<Pipe, String> {
        let (stages, tail) = self.stages(ss, Vec::new())?;
        let p = seq_of(stages);
        match tail {
            Some(e) if matches!(&p, Pipe::Seq(ps) if ps.is_empty()) => Err(match &e {
                Pipe::Var(Slot::Param(_, n)) => self.step_param(n).err().unwrap_or_else(|| not_group(&e)),
                Pipe::Var(Slot::Global(i)) => bare(super::vars::var(*i).name).err().unwrap_or_else(|| not_group(&e)),
                Pipe::Var(Slot::Local(n, Holds::Num)) => bare(n).err().unwrap_or_else(|| not_group(&e)),
                e => not_group(e),
            }),
            Some(e) => Err(format!("{} | {} gives a number, not a group: a pipeline that ends in a number goes where a number does, as in x = (a | size)", show(&p), show_expr(&e, 1))),
            None if gives_tuple(&p) => Err(format!("{} gives {}, not a group: a tuple goes where one is taken, as in t = ... or ... | (index 0)", show(&p), value_ty(&p).unwrap())),
            None => Ok(p),
        }
    }

    /// A pipeline in parentheses, which gives what its last step gives: a group, a tuple, or a
    /// number or a text.
    fn paren_pipe(&mut self, pl: &Pipeline) -> Result<Pipe, String> {
        let (stages, tail) = self.inside(|e| e.stages(Stages::of(pl), Vec::new()))?;
        let p = seq_of(stages);
        Ok(match tail {
            Some(e) => number_seq(p, e),
            None => p,
        })
    }

    /// The input the step `x` takes, for an error after a step that gives no group: its
    /// input parameter, or `a group`.
    pub(crate) fn takes(&self, x: &Syn) -> String {
        let mut x = x;
        loop {
            x = match &x.node {
                Node::Paren(p) => &p.stages[0].items[0],
                _ => break,
            };
        }
        let input = match &x.node {
            Node::Name(n) if self.param(n).is_none() => match get(n) {
                Some(s) => s.input.as_ref().map(|i| i.to_string()),
                None => self.defs.get(*n).map(|_| self.sig_named(n)).and_then(|s| s.input.map(|i| i.to_string())),
            },
            _ => None,
        };
        format!("{} takes {}", self.tok(x.at), input.unwrap_or_else(|| "a group".into()))
    }

    /// The stages of a pipeline whose first `stages` are elaborated already, and the
    /// expression of a last step that gives a number (`a | size`).
    pub(crate) fn stages(&mut self, ss: Stages, stages: Vec<Pipe>) -> Result<(Vec<Pipe>, Option<Pipe>), String> {
        let outer = self.input;
        self.input |= stages.iter().any(starts_with_value);
        let r = self.stages_on(ss, stages);
        self.input = outer;
        r
    }

    fn stages_on(&mut self, ss: Stages, mut stages: Vec<Pipe>) -> Result<(Vec<Pipe>, Option<Pipe>), String> {
        let mut i = 0;
        while i < ss.len() {
            let s = ss.at(i);
            let x = &s[0];
            let first = stages.is_empty();
            if let Some(e) = old_form(x) {
                return Err(e.into());
            }
            let mut indexed = None;
            let value = match &x.node {
                Node::Str(t) => Some(Pipe::Text(t.to_string())),
                _ if !first && self.text_tail && self.text_fn(x) => Some(self.text_value(x)?),
                _ if let Some((a, at)) = self.step_cut(x, &|e, n| !e.number_step_name(n)) => {
                    self.stage(a)?;
                    return Err(self.leftover(at));
                }
                _ => match self.tuple_index(x)? {
                    Some((p, Ty::Num | Ty::Text)) => Some(p),
                    Some((p, t)) => {
                        indexed = Some(self.index_step(p, t)?);
                        None
                    }
                    None if self.is_number_step(x) => Some(self.expr(x)?),
                    None => None,
                },
            };
            if let Some(e) = value {
                self.one_item(s)?;
                let (steps, last) = self.then_applied(e, ss, &mut i, first)?;
                stages.extend(steps);
                if last.is_some() {
                    return Ok((stages, last));
                }
                self.input = true;
                i += 1;
                continue;
            }
            let flat = match &x.node {
                Node::Name(n) => self.defs.get(*n).is_some_and(|d| d.flat && d.params.is_empty()),
                Node::Paren(_) => x.head_name().is_some_and(|n| self.defs.get(n).is_some_and(|d| d.flat && !d.params.is_empty())),
                _ => false,
            };
            let p = match indexed {
                Some(p) => p,
                None => self.stage(x)?,
            };
            self.one_item(s)?;
            self.input |= starts_with_value(&p);
            let more = i + 1 < ss.len();
            if gives_value(&p) && !more {
                return Ok((stages, Some(p)));
            }
            if (gives_tuple(&p) || gives_value(&p)) && more {
                let (steps, last) = self.then_applied(p, ss, &mut i, false)?;
                stages.extend(steps);
                if last.is_some() {
                    return Ok((stages, last));
                }
                self.input = true;
                i += 1;
                continue;
            }
            match p {
                Pipe::Seq(ps) if flat => stages.extend(ps),
                p => stages.push(p),
            }
            i += 1;
        }
        Ok((stages, None))
    }

    /// `(index i t)` of a tuple elaborated, where a step is: an error unless it gives a group,
    /// a tuple or a function that gives candidates.
    pub(crate) fn index_step(&self, p: Pipe, t: Ty) -> Result<Pipe, String> {
        match t {
            Ty::Group | Ty::Tuple(_) => Ok(p),
            t if t.is_step() => Ok(p),
            t => Err(format!("{} gives {t}, not a group", show(&p))),
        }
    }

    /// The function after the `|` whose input takes a value of type `ty` (a number or a text):
    /// its name and signature.
    fn taker(&self, x: &Syn, ty: &Ty) -> Option<(String, Sig)> {
        let n = match &x.node {
            Node::Name(n) => *n,
            Node::Paren(_) => x.head_name()?,
            _ => return None,
        };
        if self.param(n).is_some() || self.fn_var(n).is_some() || self.locals.iter().any(|l| l == n) {
            return None;
        }
        let s = match get(n) {
            Some(s) => s.clone(),
            None if self.defs.contains_key(n) => self.sig_named(n),
            None => return None,
        };
        (s.input.as_ref()?.ty == *ty).then(|| (n.to_string(), s))
    }

    /// The value `e` of the step at `i` of `ss` and the functions after each `|` whose input
    /// takes the value the step before gives, as steps (`i` the last of them); the number or
    /// text that ends the pipeline, or `None` where the last step gives a group (a `|` may
    /// follow it) or a tuple. A `|` before a function that takes another type is an error.
    fn then_applied(&mut self, mut e: Pipe, ss: Stages, i: &mut usize, first: bool) -> Result<(Vec<Pipe>, Option<Pipe>), String> {
        let (mut steps, mut after) = (Vec::new(), Vec::new());
        let mut ty = value_ty(&e).unwrap_or_else(|| expr_ty(&e));
        while let Some(n) = ss.get(*i + 1) {
            let x = &n[0];
            if ty.positions().is_some() && !self.no_value(x) {
                *i += 1;
                let (f, gives) = self.tuple_taker(&e, &ty, x)?;
                self.one_item(n)?;
                steps.push(std::mem::replace(&mut e, f));
                steps.append(&mut after);
                if !matches!(gives, Ty::Num | Ty::Text | Ty::Tuple(_)) && !gives.is_function() {
                    steps.push(e);
                    return Ok((steps, None));
                }
                ty = gives;
            } else if let Some((name, s)) = self.taker(x, &ty) {
                *i += 1;
                let f = self.taking(x, &name, &s)?;
                self.one_item(n)?;
                steps.push(std::mem::replace(&mut e, f));
                steps.append(&mut after);
                if !matches!(s.result, Ty::Num | Ty::Text) {
                    steps.push(e);
                    return Ok((steps, None));
                }
                ty = s.result.clone();
            } else if self.no_value(x) {
                *i += 1;
                after.push(self.stage(x)?);
                self.one_item(n)?;
            } else {
                break;
            }
        }
        let more = *i + 1 < ss.len();
        if !more && !matches!(ty, Ty::Num | Ty::Text) {
            steps.push(e);
            steps.append(&mut after);
            return Ok((steps, None));
        }
        if !more {
            return Ok(match after.pop() {
                Some(last) => {
                    steps.push(e);
                    steps.append(&mut after);
                    (steps, Some(last))
                }
                None => (steps, Some(e)),
            });
        }
        if first && steps.is_empty() && after.is_empty() && ty == Ty::Num && named_number(&e) {
            return Err(not_group(&e));
        }
        let given = match ty {
            Ty::Text => format!("{} gives text", show(&e)),
            Ty::Num => format!("{} gives num", show_expr(&e, 1)),
            t => format!("{} gives {t}", stage(&e)),
        };
        Err(format!("{given}; {}", self.takes(&ss.at(*i + 1)[0])))
    }

    /// Whether the step `x` gives no value: an assignment, a switch, or a call of `print` or
    /// `assert`.
    fn no_value(&self, x: &Syn) -> bool {
        match &x.node {
            Node::Assign(Lhs::Name(n) | Lhs::Typed(n, _), _) => self.param(n).is_none(),
            Node::Paren(_) => x.head_name().is_some_and(|n| n == "on" || n == "off" || get(n).is_some_and(|s| s.kind() == Kind::Effect)),
            _ => false,
        }
    }

    /// The call of the function `n` (signature `s`) the step `x` is, `NAME` or `(NAME
    /// args...)`, without its input, which the value of the step before gives.
    fn taking(&mut self, x: &Syn, n: &str, s: &Sig) -> Result<Pipe, String> {
        let reading = Sig { input: None, ..s.clone() };
        let args = match &x.node {
            Node::Paren(_) => {
                let mut c = Items::of(x);
                let a = self.inside(|e| e.args(&reading, true, &mut c))?;
                self.close(&c)?;
                a
            }
            _ if s.required() => return Err(format!("{n} takes {}: {s}", s.arity())),
            _ => vec![Arg::Absent; s.params.len()],
        };
        if super::builtins::builtin(n).is_some() {
            return construct(n, args).ok_or_else(|| unimplemented(get(n).unwrap()));
        }
        self.used.push(n.to_string());
        self.call_of(n, args, None)
    }

    /// One step.
    pub(crate) fn stage(&mut self, x: &Syn) -> Result<Pipe, String> {
        match &x.node {
            Node::Assign(Lhs::Name(n), rhs) => return self.assign(n, rhs),
            Node::Assign(Lhs::Typed(n, t), rhs) => return self.typed_bind(n, t, rhs),
            Node::Assign(Lhs::Names(ns), rhs) => return self.unpack(ns, rhs),
            _ => {}
        }
        if let Some(e) = old_form(x) {
            return Err(e.into());
        }
        let p = self.stage_of(x)?;
        self.note_bound(&p);
        Ok(p)
    }

    /// The step the next item of `c` is.
    fn stage_next(&mut self, c: &mut Items) -> Result<Pipe, String> {
        match c.next() {
            Some(x) => self.stage(x),
            None => Err(format!("expected a pass or (, found {}", self.tok(c.end))),
        }
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

    fn stage_of(&mut self, x: &Syn) -> Result<Pipe, String> {
        if x.tuple().is_some() || x.name().is_some_and(|n| self.tuple_var(n).is_some()) {
            return Ok(self.tuple_term(x)?.0);
        }
        if let Some((p, t)) = self.tuple_index(x)? {
            return self.index_step(p, t);
        }
        match &x.node {
            Node::Name(n) => self.name_step(n),
            Node::Paren(_) => self.inside(|e| e.paren_step(x)),
            _ => Err(format!("expected a pass or (, found {}", self.tok(x.at))),
        }
    }

    fn name_step(&mut self, n: &str) -> Result<Pipe, String> {
        if self.group_value(n) {
            self.use_param(n, Ty::Group)?;
            return Ok(group(n.into()));
        }
        if self.param(n).is_none()
            && let Some(t) = self.fn_var(n)
        {
            return match t {
                t if t.is_step() => Ok(Pipe::Var(Slot::Local(n.into(), Holds::Fn(t)))),
                t => Err(format!("{n} gives a number, not a group: it holds {t}; a step calls a function that gives a group")),
            };
        }
        if let Some(i) = self.param(n) {
            self.step_param(n)?;
            return Ok(param_var(i, n.into()));
        }
        if self.defs.get(n).is_some_and(|d| d.input.is_some() && d.params.is_empty()) {
            self.used.push(n.into());
            return self.call_of(n, Vec::new(), None);
        }
        if let Some(d) = self.defs.get(n) {
            if !d.params.is_empty() {
                return Err(format!("{n} needs parentheses: ({n} ...); {}", self.sig_named(n)));
            }
            if self.number_def(n) {
                return Err(format!("{n} gives a number, not a group: {}; a step calls a function that gives a group", self.sig_named(n)));
            }
            if d.def.as_ref().is_some_and(|d| d.inline && d.input.is_some()) {
                let p = self.call_of(n, Vec::new(), None)?;
                self.used.push(n.into());
                return Ok(p);
            }
            let p = d.pipe.clone();
            self.used.push(n.into());
            return Ok(p);
        }
        bare(n)
    }

    /// A step in parentheses: a call, or a pipeline.
    fn paren_step(&mut self, x: &Syn) -> Result<Pipe, String> {
        let (st, _) = x.head_stage().expect("no tuple");
        let head = &st.items[0];
        let args_follow = st.items.get(1).is_some_and(|a| !matches!(a.node, Node::Str(_)));
        let mut c = Items::of(x);
        let n = match &head.node {
            Node::Assign(Lhs::Name(_), _) => return self.pipe(Stages::of(x.paren().unwrap())),
            Node::Name(n) => *n,
            _ => return self.paren_pipe(x.paren().unwrap()),
        };
        let p = match () {
            _ if n == "on" || n == "off" => self.switches(n, &mut c)?,
            _ if self.defs.get(n).is_some_and(|d| !d.params.is_empty() || (d.run || d.input.is_some()) && args_follow) => self.def_call(n, &mut c)?,
            _ if self.param(n).is_none() && self.fn_var(n).is_some_and(|t| t.is_step()) && args_follow => {
                let Some(input) = self.group_input(&mut c)? else { return Err(format!("{n} takes a group value: ({n} g)")) };
                Pipe::Seq(vec![input, self.fn_read(n.into())])
            }
            _ if self.param(n).is_some_and(|i| self.params[i].ty != Some(Ty::Group)) && args_follow => {
                let Some(input) = self.group_input(&mut c)? else { return Err(format!("parameter {n} takes a group value: ({n} g)")) };
                self.step_param(n)?;
                Pipe::Seq(vec![input, param_var(self.param(n).unwrap(), n.into())])
            }
            _ if n == "import" => return Err(NO_IMPORT.into()),
            _ => match get(n) {
                Some(s) if s.is_number() && x.paren().is_some_and(|p| p.stages.len() == 1) => return Err(not_a_step(s)),
                Some(s) if s.is_text() && x.paren().is_some_and(|p| p.stages.len() == 1) => return Err(text_step(s)),
                Some(s) if s.is_number() || s.is_text() => return self.paren_pipe(x.paren().unwrap()),
                Some(s) if s.kind() == Kind::FromText => {
                    let t = match c.next() {
                        Some(t) => self.text_value(t)?,
                        None => return Err(format!("expected a text, as in \"x + y\" or (show (main t)), found {}", self.tok(c.end))),
                    };
                    Pipe::App(Fun::Builtin(super::builtins::builtin(n).unwrap()), vec![t].into())
                }
                Some(s) if !s.params.is_empty() => self.call(s, &mut c)?,
                Some(s) if args_follow => {
                    let Some(input) = self.group_input_of(&mut c, false)? else { return Err(format!("{n} takes {}: {s}", s.arity())) };
                    explicit(input, construct(n, Vec::new()).ok_or_else(|| unimplemented(s))?)
                }
                _ => return self.paren_pipe(x.paren().unwrap()),
            },
        };
        self.close(&c)?;
        Ok(p)
    }

    /// Whether `x` is a function that gives a text, alone or called in parentheses.
    pub(crate) fn text_fn(&self, x: &Syn) -> bool {
        let n = match &x.node {
            Node::Name(n) => *n,
            Node::Paren(_) => match x.head_name() {
                Some(n) => n,
                None => return false,
            },
            _ => return false,
        };
        self.param(n).is_none() && get(n).is_some_and(Sig::is_text)
    }

    /// A text: a string literal, or a function that gives one, alone (on the step's input) or
    /// with its input written (`(show (main t))`).
    pub(crate) fn text_value(&mut self, x: &Syn) -> Result<Pipe, String> {
        if let Node::Str(t) = &x.node {
            return Ok(Pipe::Text(t.to_string()));
        }
        if !self.text_fn(x) {
            return Err(format!("expected a text, as in \"x + y\" or (show (main t)), found {}", self.tok(x.at)));
        }
        let n = match &x.node {
            Node::Name(n) => *n,
            _ => x.head_name().unwrap(),
        };
        let s = get(n).unwrap();
        let f = Fun::Builtin(super::builtins::builtin(n).unwrap());
        if x.name().is_some() {
            return Ok(Pipe::App(f, Vec::new().into()));
        }
        let mut c = Items::of(x);
        let input = self.inside(|e| e.group_input(&mut c))?;
        self.close(&c)?;
        match input {
            Some(i) => {
                self.input_fits(s, s.input.as_ref().unwrap(), &i)?;
                Ok(Pipe::App(f, vec![i].into()))
            }
            None => Ok(Pipe::App(f, Vec::new().into())),
        }
    }

    /// A top-level statement: its steps, each with what it gives.
    fn statement(&mut self, pl: &Pipeline) -> Result<Vec<Top>, String> {
        let ss = Stages::of(pl);
        let x = &ss.at(0)[0];
        if let Node::Name(n) = &x.node
            && ss.len() > 1
            && ss.at(0).len() == 1
            && !self.input
            && let Some(s) = self.bare_fn(n).filter(|s| matches!(s.result, Ty::Num | Ty::Text) && s.input.is_some())
        {
            let input = if s.input.as_ref().is_some_and(|i| i.ty == Ty::Group) { Ty::Group } else { Ty::Term };
            let f = Ty::Fn(Box::new(input), Box::new(s.result.clone()));
            return Err(format!("{n} is a function value here, {f}, since the top level of the program starts with no input; {}", self.takes(&ss.at(1)[0])));
        }
        let fn_alone = matches!((&x.node, ss.len(), ss.at(0).len()), (Node::Name(n), 1, 1) if self.fn_var(n).is_some());
        let lead = match &x.node {
            Node::Str(t) => Some(Pipe::Text(t.to_string())),
            _ if self.text_fn(x) && ss.at(0).len() == 1 => Some(self.text_value(x)?),
            Node::Assign(..) => None,
            _ if let Some(e) = old_form(x) => return Err(e.into()),
            _ if let Some((a, at)) = self.step_cut(x, &|e, n| !e.rhs_name(n, false, true)) => {
                self.stage(a)?;
                return Err(self.leftover(at));
            }
            _ if fn_alone => None,
            _ => match self.tuple_index(x)? {
                Some((p, Ty::Num)) => Some(p),
                Some((p, t)) => {
                    let p = self.index_step(p, t)?;
                    self.one_item(ss.at(0))?;
                    let (stages, tail) = self.stages(ss.from(1), vec![p])?;
                    return Ok(stages.into_iter().chain(tail).map(Top::step).collect());
                }
                None if self.rhs_number(x, false) => Some(self.expr(x)?),
                None => None,
            },
        };
        let mut first = Vec::new();
        if let Some(e) = lead {
            self.one_item(ss.at(0))?;
            let mut i = 0;
            let (steps, last) = self.then_applied(e, ss, &mut i, true)?;
            if let Some(e) = last {
                let mut out: Vec<Top> = steps.into_iter().map(Top::step).collect();
                out.push(Top::step(e));
                return Ok(out);
            }
            first = steps;
            if i + 1 >= ss.len() {
                return Ok(first.into_iter().map(Top::step).collect());
            }
            self.text_tail = true;
            let r = self.stages(ss.from(i + 1), first);
            self.text_tail = false;
            let (stages, tail) = r?;
            return Ok(stages.into_iter().chain(tail).map(Top::step).collect());
        }
        if fn_alone {
            let n = x.name().unwrap().to_string();
            return Ok(vec![Top { pipe: self.fn_read(n), gives: Gives::Fn }]);
        }
        self.text_tail = true;
        let r = self.stages(ss, first);
        self.text_tail = false;
        let (stages, tail) = r?;
        Ok(stages.into_iter().chain(tail).map(Top::step).collect())
    }

    /// `x` where it applies an operator and its leftmost operand is a name that `step` says
    /// is a step: that operand, and the token of the operator after it.
    fn step_cut<'s>(&self, x: &'s Syn<'s>, step: &dyn Fn(&Self, &str) -> bool) -> Option<(&'s Syn<'s>, usize)> {
        let (a, at) = leftmost(x)?;
        let n = a.name()?;
        step(self, n).then_some((a, at))
    }

    /// Whether the step `x` gives a number and is no expression whose leftmost operand is a
    /// step.
    pub(crate) fn number_item(&self, x: &Syn) -> bool {
        self.step_cut(x, &|e, n| !e.number_step_name(n)).is_none() && self.is_number_step(x)
    }

    /// The expression argument the next item of `c` is.
    pub(crate) fn earg_of(&mut self, c: &mut Items) -> Result<Pipe, String> {
        match c.next() {
            Some(x) if let Some(at) = earg_cut(x) => Err(format!("expected ), found {}", self.tok(at))),
            Some(x) => self.earg(x),
            None => Err(format!("expected an expression, found {}", self.tok(c.end))),
        }
    }

    /// Whether the step `x` gives a number: a number, `!`, an operator, a variable that holds
    /// a number, a function that gives one (applied to the step's input), or such a call or
    /// expression in parentheses.
    fn is_number_step(&self, x: &Syn) -> bool {
        match &x.node {
            Node::Num(_) | Node::Not(_) | Node::Op(..) | Node::And(_) | Node::Or(_) => true,
            Node::Name(n) => self.number_step_name(n),
            Node::Paren(_) => match x.single() {
                Some(y) => self.is_number_step(y),
                None if self.is_call(x) => x.head_name().is_some_and(|n| self.number_step_name(n)),
                None => false,
            },
            _ => false,
        }
    }

    /// Whether the name `n` written as a step gives a number.
    fn number_step_name(&self, n: &str) -> bool {
        if let Some(i) = self.param(n) {
            return self.number_fn_name(n) || self.params[i].ty == Some(Ty::Num);
        }
        if self.fn_var(n).is_some() {
            return self.number_fn_name(n);
        }
        if self.locals.iter().any(|l| l == n) {
            return true;
        }
        get(n).is_some_and(|s| s.is_number()) || self.number_def(n) || var_index(n).is_some() && get(n).is_none() && !self.defs.contains_key(n) && !self.group_value(n)
    }

    /// Whether the parentheses `x` are a call: their first item names a function, and
    /// arguments follow it or it takes some.
    fn is_call(&self, x: &Syn) -> bool {
        let Some((st, _)) = x.head_stage() else { return false };
        let Some(n) = st.items[0].name() else { return false };
        let named = self.param(n).is_some() || self.fn_var(n).is_some() || get(n).is_some_and(|s| !s.is_op()) || self.defs.contains_key(n);
        named && (st.items.len() > 1 || get(n).is_some_and(|s| !s.params.is_empty()) || self.defs.get(n).is_some_and(|d| !d.params.is_empty()))
    }

    /// Whether the right side `x` of an assignment gives a number, `number_var` where the left
    /// side is a variable that holds one: an expression, a name that gives a number (for a
    /// name that is also a step or an untyped parameter, where `number_var`), a call of a
    /// function that gives one, or a name or expression in parentheses that does.
    pub(crate) fn rhs_number(&self, x: &Syn, number_var: bool) -> bool {
        match &x.node {
            Node::Num(_) | Node::Not(_) | Node::Op(..) | Node::And(_) | Node::Or(_) => true,
            Node::Name(n) => self.rhs_name(n, number_var, false),
            Node::Paren(_) => match x.single().map(|y| (y, &y.node)) {
                Some((_, Node::Name(n))) => self.rhs_name(n, number_var, true),
                Some((_, Node::Assign(..) | Node::Str(_))) => false,
                Some((y, Node::Paren(_) | Node::Tuple(_))) => self.rhs_number(y, number_var),
                Some(_) => true,
                None if self.is_call(x) => {
                    let n = x.head_name().unwrap();
                    match self.param(n) {
                        Some(i) => self.params[i].ty.as_ref().is_some_and(Ty::is_expr),
                        None => get(n).is_some_and(|s| s.is_number()) || self.number_def(n) || self.number_fn_name(n),
                    }
                }
                None => false,
            },
            _ => false,
        }
    }

    /// Whether the name `n` alone on the right side of an assignment gives a number;
    /// `parens`: written in parentheses, where a name that names nothing is an expression.
    fn rhs_name(&self, n: &str, number_var: bool, parens: bool) -> bool {
        if self.locals.iter().any(|l| l == n) {
            return true;
        }
        if let Some(i) = self.param(n) {
            return self.params[i].ty.as_ref().map_or(number_var, Ty::is_expr);
        }
        if get(n).is_some_and(|s| s.is_number()) || self.number_def(n) || self.number_fn_name(n) {
            return true;
        }
        if self.fn_var(n).is_some() || self.tuple_term_name(n) {
            return false;
        }
        if self.defs.contains_key(n) || self.group_value(n) {
            false
        } else if var_index(n).is_some() {
            resolve(n).is_none() || number_var
        } else if ["none", "true", "def", "extern"].contains(&n) || MACROS.contains(&n) {
            true
        } else if !self.unknown(n) {
            false
        } else {
            parens
        }
    }

    /// The right side of `n = ...`, read once and taken by the type of what it gives: a number
    /// for a variable that holds a number, candidates for a group variable. Where a name fits
    /// both (`relate`, a parameter `r`), `n` decides.
    fn assign(&mut self, n: &str, rhs: &Syn) -> Result<Pipe, String> {
        if let Some(d) = self.defs.get(n).filter(|d| d.run) {
            return Err(format!("{n} is a function and cannot be assigned: {}", def_sig(n, &d.params)));
        }
        if self.param(n).is_some() {
            return Err(format!("parameter {n} cannot be assigned"));
        }
        if var_index(n) == Some(super::host::NUM_TYPE) {
            let Some(t) = rhs.name() else { return Err(format!("expected a numeric type after num_type =, found {}", self.tok(rhs.at))) };
            return match t {
                "none" => Ok(Pipe::assign(super::host::NUM_TYPE, Pipe::Num(NONE))),
                t if super::host::NUM_TYPES.contains(&t) => Ok(Pipe::assign(super::host::NUM_TYPE, Pipe::Name(t.into()))),
                t => Err(format!("num_type takes a numeric type, not {t}; known: {}", super::host::NUM_TYPES.join(" "))),
            };
        }
        let number_var = var_index(n).is_some();
        let group_var = self.groups.iter().any(|g| g == n);
        if rhs.paren().is_some()
            && let Some(e) = old_form(rhs)
        {
            return Err(e.into());
        }
        if let Some((a, at)) = self.step_cut(rhs, &|e, m| !e.rhs_name(m, number_var, true)) {
            self.stage(a)?;
            return Err(self.leftover(at));
        }
        let tuple_var = self.tuples.iter().any(|(t, _)| t == n);
        let rhs = match self.tuple_index(rhs)? {
            Some((p, Ty::Num)) => Rhs::Num(p),
            Some((p, t @ Ty::Tuple(_))) => return self.bind_tuple(n, p, t),
            Some((p, t)) => Rhs::Group(self.index_step(p, t)?),
            None if let Some((e, ty)) = self.tuple_rhs(rhs)? => return self.bind_tuple(n, e, ty),
            None if self.rhs_number(rhs, number_var) => Rhs::Num(self.expr(rhs)?),
            None => self.rhs_step(rhs)?,
        };
        match rhs {
            Rhs::Num(e) if number_var => self.assign_number(n, e),
            Rhs::Num(e) if group_var => Err(format!("{n} is a group variable, so it cannot hold a number: {} gives a number", show_expr(&e, 1))),
            Rhs::Num(e) if self.fn_var(n).is_some() => Err(format!("{n} is a function variable, so it cannot hold a number: {} gives a number; write {n}:TYPE = ... for a function", show_expr(&e, 1))),
            Rhs::Num(e) if tuple_var => Err(format!("{n} is a tuple variable, so it cannot hold a number: {} gives a number", show_expr(&e, 1))),
            Rhs::Group(p) if gives_tuple(&p) => {
                let ty = value_ty(&p).unwrap();
                self.bind_tuple(n, p, ty)
            }
            Rhs::Num(e) => self.bind_num(n, e),
            Rhs::Group(p) if number_var => Err(format!("{n} is a variable that holds a number, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) if self.locals.iter().any(|l| l == n) => Err(format!("{n} is a number variable, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) if self.fn_var(n).is_some() => Err(format!("{n} is a function variable, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) if tuple_var => Err(format!("{n} is a tuple variable, so it cannot be bound to a group: {} gives a group", stage(&p))),
            Rhs::Group(p) => self.bind(n, p),
        }
    }

    /// The right side of an assignment that is no expression: a pipeline in parentheses,
    /// which gives a number where it ends in one (`(a | size)`), a group variable alone, or
    /// one step.
    pub(crate) fn rhs_step(&mut self, x: &Syn) -> Result<Rhs, String> {
        if let Some(pl) = x.paren().filter(|_| !self.is_call(x) && !matches!(x.head_name(), Some("on" | "off"))) {
            let (stages, tail) = self.inside(|e| e.stages(Stages::of(pl), Vec::new()))?;
            let p = seq_of(stages);
            return Ok(match tail {
                Some(e) => Rhs::Num(number_seq(p, e)),
                None => Rhs::Group(p),
            });
        }
        if let Node::Name(u) = &x.node
            && self.group_var_alone(u)
        {
            self.group_name(u)?;
            return Ok(Rhs::Group(group(u.to_string())));
        }
        Ok(Rhs::Group(self.stage(x)?))
    }

    /// Whether the name `n` alone on the right side of an assignment is a group variable: a
    /// name that is no variable, function or definition, or a parameter used as a group
    /// variable.
    fn group_var_alone(&self, n: &str) -> bool {
        match self.param(n) {
            Some(i) => self.params[i].ty == Some(Ty::Group),
            None => !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || ["none", "true", "def", "extern"].contains(&n)),
        }
    }

    /// `n = e` for the variable `n` that holds a number.
    fn assign_number(&mut self, n: &str, e: Pipe) -> Result<Pipe, String> {
        let i = assignable(n)?;
        if let Pipe::Num(k) = e
            && is_switch(i)
            && k == NONE
        {
            return Err(format!("{n} is a switch: assign it 0 (off) or 1 (on)"));
        }
        Ok(Pipe::assign(i, e))
    }

    /// `n:t = f`: the variable `n` bound to the function `f` of that type.
    fn typed_bind(&mut self, n: &str, t: &str, rhs: &Syn) -> Result<Pipe, String> {
        let ty = Ty::parse(t).ok().filter(Ty::is_function).ok_or_else(|| format!("{n}:{t} = ...: a function variable takes a function type, as in term->num or term->term"))?;
        let outer = std::mem::replace(&mut self.input, true);
        let f = self.fn_rhs(n, &ty, rhs);
        self.input = outer;
        let f = f?;
        self.bind_fn(n, f, ty)
    }

    /// The right side `x` of `n:t = ...`, a function of type `ty`.
    pub(crate) fn fn_rhs(&mut self, n: &str, ty: &Ty, x: &Syn) -> Result<Pipe, String> {
        Ok(match ty.is_step() {
            true => {
                let q = self.stage(x)?;
                if let Pipe::Var(Slot::Param(i, m)) = &q
                    && self.params[*i].ty.is_none()
                {
                    self.use_param(&m.clone(), ty.clone())?;
                }
                let have = self.stage_ty(&q);
                if !have.fits(ty) {
                    return Err(format!("{n} holds {ty}; {} is {have}", stage(&q)));
                }
                q
            }
            false => self.expr(x)?,
        })
    }

    fn no_bar(&self, form: &str, c: &Items) -> Result<(), String> {
        match c.at_bar() {
            true => Err(format!("group a pipeline argument of {form} in parentheses: ({form} ... (a | b))")),
            false => Ok(()),
        }
    }

    /// The last pipeline parameter of a call, read to `)`: the next item, and the stages after
    /// it where it ends its stage.
    fn whole(&mut self, c: &mut Items) -> Result<Pipe, String> {
        let Some(x) = c.peek() else { return Err(format!("expected a pass or (, found {}", self.tok(c.end))) };
        let mut ss = Stages { first: std::slice::from_ref(x), rest: &[] };
        if c.k + 1 == c.items.len() {
            ss.rest = std::mem::take(&mut c.rest);
        }
        c.k += 1;
        self.pipe(ss)
    }

    /// The arguments of a call of the group function `s` after its name, as its parameters
    /// read them.
    fn call(&mut self, s: &'static Sig, c: &mut Items) -> Result<Pipe, String> {
        let args = self.args(s, false, c)?;
        let input = self.group_input(c)?;
        let p = construct(&s.name, args).ok_or_else(|| unimplemented(s))?;
        Ok(match input {
            Some(i) => explicit(i, p),
            None => p,
        })
    }

    /// The arguments of a call of `s` after its name: an expression argument (a number, a
    /// name, `!` and an argument, or one in parentheses), a name, one step per pipeline, or the
    /// whole pipeline up to `)` when one pipeline is the last and only one (`(fix 3 a | b)`);
    /// `sig` adds the signature to an error in an expression argument.
    pub(crate) fn args(&mut self, s: &Sig, sig: bool, c: &mut Items) -> Result<Vec<Arg>, String> {
        let outer = self.input;
        let r = self.args_on(s, sig, outer, c);
        self.input = outer;
        r
    }

    fn args_on(&mut self, s: &Sig, sig: bool, input: bool, c: &mut Items) -> Result<Vec<Arg>, String> {
        let f = s.name.as_str();
        let arity = || format!("{f} takes {}: {s}", s.arity());
        let pipes = s.params.iter().filter(|p| p.ty.is_step()).count();
        let mut args = Vec::new();
        for (i, p) in s.params.iter().enumerate() {
            self.input = input || matches!(p.ty, Ty::Fn(..));
            let whole = pipes == 1 && i + 1 == s.params.len() && p.rep == Rep::One;
            let named = c.peek().is_some_and(|x| matches!(self.toks.get(x.at), Some(Tok::Name(_))));
            let alone = !c.before_bar();
            let whose = || format!("{f} takes {p}: {s}");
            if matches!(p.ty, Ty::Fn(..)) && !p.ty.is_pipe() && p.rep == Rep::One && alone
                && let Some(q) = self.function_name(c, &p.ty, &whose)?
            {
                args.push(if p.ty.is_step() { Arg::Pipe(q) } else { Arg::Num(q) });
                continue;
            }
            if p.ty.is_step() && !p.ty.is_pipe() && !c.at_close() {
                let q = if whole {
                    self.whole(c)?
                } else {
                    self.no_bar(f, c)?;
                    self.stage_next(c)?
                };
                let have = self.stage_ty(&q);
                if !have.fits(&p.ty) {
                    return Err(format!("{}; {} is {have}", whose(), stage(&q)));
                }
                args.push(Arg::Pipe(q));
                continue;
            }
            args.push(match (&p.ty, p.rep) {
                (Ty::Text, _) => match c.peek() {
                    Some(Syn { node: Node::Str(t), .. }) => {
                        c.k += 1;
                        Arg::Num(Pipe::Text(t.to_string()))
                    }
                    _ => return Err(format!("{}; found {}", whose(), self.tok(c.tok()))),
                },
                (Ty::Any, _) => {
                    let mut xs = Vec::new();
                    while !c.at_close() {
                        xs.push(self.any_arg(c)?);
                    }
                    if xs.is_empty() {
                        return Err(arity());
                    }
                    Arg::Pipes(xs)
                }
                (_, Rep::Opt) if c.at_close() => Arg::Absent,
                (Ty::Name | Ty::Group, Rep::Opt) if !named => Arg::Absent,
                (_, Rep::One) if c.at_close() => return Err(arity()),
                (t @ Ty::Tuple(_), _) => Arg::Num(self.tuple_arg(c, t, &whose)?),
                (t, _) if t.is_expr() => {
                    if let Some(x) = c.peek()
                        && let Some(at) = earg_cut(x)
                    {
                        return Err(self.cut_arg(s, i, at));
                    }
                    let e = match c.next() {
                        Some(x) => self.earg(x),
                        None => Err(format!("expected an expression, found {}", self.tok(c.end))),
                    };
                    Arg::Num(e.map_err(|e| if sig { format!("{e}; {f} takes {}: {s}", s.arity()) } else { e })?)
                }
                (t, _) if t.is_step() && matches!(c.peek().map(|x| &x.node), Some(Node::Num(_))) => return Err(arity()),
                (Ty::Group, _) => {
                    let n = self.name_item(c, &format!("a group variable after {f}"))?;
                    if f == "save" {
                        if self.param(&n).is_some() {
                            return Err(format!("parameter {n} cannot be assigned"));
                        }
                        self.groups.push(n.clone());
                    }
                    self.group_name(&n)?;
                    Arg::Name(n)
                }
                (Ty::Term, _) => match c.peek() {
                    Some(Syn { node: Node::Name(n), .. }) if self.param(n).is_some() && !c.before_bar() && c.after().is_none_or(|a| matches!(self.toks.get(a.at), Some(Tok::Name(_) | Tok::Open | Tok::Num(_)))) => {
                        c.k += 1;
                        self.use_param(n, Ty::Term)?;
                        Arg::Pipe(group(n.to_string()))
                    }
                    _ => {
                        self.no_bar(f, c)?;
                        Arg::Pipe(self.stage_next(c)?)
                    }
                },
                (Ty::Name, _) => {
                    let n = self.name_item(c, &format!("a name after {f}"))?;
                    self.use_param(&n, Ty::Name)?;
                    Arg::Name(n)
                }
                (t, Rep::Many) if t.is_step() => {
                    let mut out = Vec::new();
                    while !c.at_close() {
                        self.no_bar(f, c)?;
                        out.push(self.stage_next(c)?);
                    }
                    if out.is_empty() {
                        return Err(arity());
                    }
                    Arg::Pipes(out)
                }
                (t, _) if t.is_step() && whole => Arg::Pipe(self.whole(c)?),
                (t, _) if t.is_step() => {
                    self.no_bar(f, c)?;
                    Arg::Pipe(self.stage_next(c)?)
                }
                _ => unreachable!("{s}"),
            });
        }
        if !c.at_close() && !(s.input.is_some() && self.input_next(c, !s.params.is_empty())) {
            if pipes > 0 {
                self.no_bar(f, c)?;
            }
            return Err(arity());
        }
        Ok(args)
    }

    /// The error for an expression argument for parameter `i` of `s` that goes on past an
    /// argument with the operator at token `at`: what the parameter after it reads there.
    fn cut_arg(&self, s: &Sig, i: usize, at: usize) -> String {
        let op = self.tok(at);
        match s.params.get(i + 1) {
            Some(q) if q.ty.is_expr() => format!("expected an expression, found {op}"),
            Some(q) if q.ty == Ty::Text => format!("{} takes {q}: {s}; found {op}", s.name),
            Some(q) if q.ty == Ty::Group => format!("expected a group variable after {}, found {op}", s.name),
            Some(q) if q.ty == Ty::Name => format!("expected a name after {}, found {op}", s.name),
            Some(_) => format!("expected a pass or (, found {op}"),
            None => format!("{} takes {}: {s}", s.name, s.arity()),
        }
    }

    /// The name the next item of `c` is; `what` names what is expected otherwise.
    pub(crate) fn name_item(&self, c: &mut Items, what: &str) -> Result<String, String> {
        match c.peek() {
            Some(Syn { node: Node::Name(n), .. }) => {
                c.k += 1;
                Ok(n.to_string())
            }
            _ => Err(format!("expected {what}, found {}", self.tok(c.tok()))),
        }
    }

    /// An argument of type `any`: a string literal, a group value, a function value, an
    /// expression, or else a name. A function written alone that lacks at most its input is
    /// applied where it can be (the step has an input, or the function takes none), else it is
    /// a function value.
    fn any_arg(&mut self, c: &mut Items) -> Result<Pipe, String> {
        let Some(x) = c.next() else { return Err(format!("expected an expression, found {}", self.tok(c.end))) };
        if let Some((p, _)) = self.tuple_index(x)? {
            return Ok(p);
        }
        if self.tuple_term_known(x) {
            return Ok(self.tuple_term(x)?.0);
        }
        if x.paren().is_some() && !self.rhs_number(x, true) {
            let p = self.stage(x)?;
            return Ok(p);
        }
        let n = match &x.node {
            Node::Str(t) => return Ok(Pipe::Text(t.to_string())),
            Node::Name(n) => *n,
            _ => {
                if let Some(at) = earg_cut(x) {
                    return Err(format!("expected an expression, found {}", self.tok(at)));
                }
                return self.earg(x);
            }
        };
        if self.group_value(n) {
            self.use_param(n, Ty::Group)?;
            return Ok(group(n.into()));
        }
        if self.param(n).is_none() && !self.locals.iter().any(|l| l == n) && n != "none" {
            if let Some(s) = self.bare_fn(n).filter(|s| self.input || s.input.is_none()) {
                if s.result == Ty::Text {
                    return Ok(Pipe::App(Fun::Builtin(super::builtins::builtin(n).expect("a function that gives a text is built in")), Vec::new().into()));
                }
                return if s.result == Ty::Num { self.earg(x) } else { self.stage(x) };
            }
            if let Some(f) = self.function_value(n) {
                return Ok(f);
            }
            if self.unknown(n) {
                return Ok(Pipe::Name(n.into()));
            }
        }
        self.earg(x)
    }

    /// The arguments of a call of the number function `s` after its name: names, and
    /// expressions up to `)`.
    fn number_call(&mut self, s: &'static Sig, c: &mut Items) -> Result<Pipe, String> {
        let outer = self.input;
        let r = self.number_call_on(s, outer, c);
        self.input = outer;
        r
    }

    fn number_call_on(&mut self, s: &'static Sig, input: bool, c: &mut Items) -> Result<Pipe, String> {
        let f = s.name.as_str();
        let mut args = Vec::new();
        for p in &s.params {
            self.input = input || matches!(p.ty, Ty::Fn(..));
            args.push(match &p.ty {
                _ if c.at_close() && p.rep == Rep::Opt => Arg::Absent,
                _ if c.at_close() => return Err(format!("{f} takes {}: {s}", s.arity())),
                t if matches!(t, Ty::Fn(..)) && c.before_close() && c.peek().and_then(Syn::name).is_some_and(|n| self.param(n).is_some() || self.fn_var(n).is_some()) => {
                    let whose = || format!("{f} takes {p}: {s}");
                    match self.function_name(c, t, &whose)? {
                        Some(q) => Arg::Num(q),
                        None => Arg::Num(self.expr_next(c)?),
                    }
                }
                t if t.is_expr() => Arg::Num(self.expr_next(c)?),
                t if t.is_step() => {
                    self.no_bar(f, c)?;
                    Arg::Pipe(self.stage_next(c)?)
                }
                Ty::MaybeTerm => match self.group_input(c)? {
                    Some(x) => {
                        self.input_fits(s, p, &x)?;
                        Arg::Pipe(x)
                    }
                    None => return Err(format!("{f} takes {p}, as in (main r): {s}")),
                },
                _ if p.rep == Rep::Opt && c.peek().and_then(Syn::name).is_none() => Arg::Absent,
                _ => {
                    let n = self.name_item(c, "a group variable")?;
                    self.group_name(&n)?;
                    Arg::Name(n)
                }
            });
        }
        self.input = input;
        let e = construct(f, args).ok_or_else(|| unimplemented(s))?;
        if !c.at_close() {
            let input = s.input.as_ref().expect("a number function has an input");
            let named = match c.peek() {
                // A name for a term is read as a group variable, for the type error.
                Some(Syn { node: Node::Name(g), .. }) if input.ty != Ty::Group && c.before_close() && !self.group_value(g) && self.param(g).is_none() && !self.defs.get(*g).is_some_and(|d| d.input.is_some()) => {
                    c.k += 1;
                    self.group_name(g)?;
                    Some(group(g.to_string()))
                }
                _ => None,
            };
            let loose = !s.params.is_empty() || input.ty != Ty::Group;
            if let Some(g) = named.map_or_else(|| self.group_input_of(c, loose), |g| Ok(Some(g)))? {
                self.input_fits(s, input, &g)?;
                let Pipe::App(fun, args) = e else { unreachable!("a number function is applied") };
                return Ok(Pipe::App(fun, args.iter().cloned().chain([g]).collect()));
            }
            return Err(format!("{f} takes {}: {s}", s.arity()));
        }
        Ok(e)
    }

    fn expr_next(&mut self, c: &mut Items) -> Result<Pipe, String> {
        match c.next() {
            Some(x) => self.expr(x),
            None => Err(format!("expected an expression, found {}", self.tok(c.end))),
        }
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

    /// An expression argument of a form: a number, a name, `!` and an argument, or a
    /// parenthesized expression.
    fn earg(&mut self, x: &Syn) -> Result<Pipe, String> {
        match &x.node {
            Node::Not(e) => Ok(op("!", vec![self.earg(e)?])),
            Node::Assign(..) => Err(NO_ASSIGN.into()),
            _ => self.atom(x),
        }
    }

    /// The expression `x`.
    pub(crate) fn expr(&mut self, x: &Syn) -> Result<Pipe, String> {
        Ok(match &x.node {
            Node::Or(es) => op("||", es.iter().map(|e| self.expr(e)).collect::<Result<_, _>>()?),
            Node::And(es) => op("&&", es.iter().map(|e| self.expr(e)).collect::<Result<_, _>>()?),
            Node::Not(e) => op("!", vec![self.expr(e)?]),
            Node::Op(o, a, b) => {
                let a = self.expr(a)?;
                op(o, vec![a, self.expr(b)?])
            }
            Node::Assign(..) => return Err(NO_ASSIGN.into()),
            _ => return self.atom(x),
        })
    }

    /// A number, a name, a call such as `(size (main R))` or `(any C)`, `( expr )` or a
    /// pipeline that ends in a number in parentheses.
    fn atom(&mut self, x: &Syn) -> Result<Pipe, String> {
        if x.tuple().is_some() {
            let (p, t) = self.tuple_literal(x, None)?;
            return Err(format!("{} gives {t}, not a number: read a position with (index i ...)", show(&p)));
        }
        if let Some((p, t)) = self.tuple_index(x)? {
            return match t {
                Ty::Num => Ok(p),
                t => Err(format!("{} gives {t}, not a number", show(&p))),
            };
        }
        match &x.node {
            Node::Num(n) => Ok(Pipe::Num(*n)),
            Node::Name(n) => self.name_atom(n),
            Node::Paren(_) => self.inside(|e| e.paren_atom(x)),
            _ => Err(format!("expected an expression, found {}", self.tok(x.at))),
        }
    }

    fn name_atom(&mut self, n: &str) -> Result<Pipe, String> {
        if let Some(i) = self.param(n) {
            self.use_param(n, Ty::Num)?;
            return Ok(param_var(i, n.into()));
        }
        if self.locals.iter().any(|l| l == n) {
            return Ok(Pipe::Var(Slot::Local(n.into(), Holds::Num)));
        }
        if let Some(t) = self.fn_var(n) {
            return match t {
                _ if !self.number_fn_name(n) => Err(format!("{n} holds {t}, which gives a group, not a number")),
                _ => Ok(Pipe::Var(Slot::Local(n.into(), Holds::Fn(t)))),
            };
        }
        if !self.input
            && let Some(s) = self.bare_fn(n).filter(|s| s.result == Ty::Num && s.input.is_some())
        {
            return Err(super::flow::no_input(n, &s));
        }
        if self.number_def(n) && self.defs[n].params.is_empty() {
            self.used.push(n.into());
            let def = self.defs[n].def.clone().unwrap();
            return Ok(Call::bare(&def));
        }
        if self.number_def(n) {
            return Err(format!("{n} needs parentheses: ({n} ...); {}", self.sig_named(n)));
        }
        if self.defs.get(n).is_some_and(|d| d.run) {
            return Err(format!("{n} gives a group, not a number: {}; an expression reads variables and number functions", self.sig_named(n)));
        }
        if self.group_value(n) {
            return Err(format!("{n} is a group, not a number: read it with (size {n}) or a function of it, ({n} ...)"));
        }
        if let Some(t) = self.tuple_var(n) {
            return Err(format!("{n} holds {t}, not a number: read a position with (index i {n})"));
        }
        name_expr(n)
    }

    /// Parentheses in an expression: a function value applied to a group, a call of a number
    /// function, a pipeline that ends in a number, or an expression.
    fn paren_atom(&mut self, x: &Syn) -> Result<Pipe, String> {
        let pl = x.paren().expect("no tuple");
        let (st, rest) = (&pl.stages[0], &pl.stages[1..]);
        let head = &st.items[0];
        if let Some(k) = head.name() {
            // `(pred t)`: a function value applied to a group.
            if (self.param(k).is_some_and(|i| self.params[i].ty.is_none()) || self.number_fn_name(k))
                && st.items.len() == 2
                && rest.is_empty()
                && match &st.items[1].node {
                    Node::Name(g) => self.input_name(g, false),
                    Node::Paren(_) | Node::Tuple(_) => true,
                    _ => false,
                }
            {
                let f = match self.param(k) {
                    Some(i) => {
                        self.use_param(k, Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Num)))?;
                        param_var(i, k.into())
                    }
                    None => self.fn_read(k.into()),
                };
                let mut c = Items::of(x);
                let input = self.group_input(&mut c)?.expect("an input written");
                return Ok(number_seq(input, f));
            }
            if let Some(s) = get(k).filter(|s| s.is_number() && (st.items.len() > 1 || !s.params.is_empty())) {
                let mut c = Items::of(x);
                let e = self.number_call(s, &mut c)?;
                self.close(&c)?;
                return Ok(e);
            }
            if self.number_def(k) && (st.items.len() > 1 || !self.defs[k].params.is_empty()) {
                let mut c = Items::of(x);
                let e = self.number_def_call(k, &mut c)?;
                self.close(&c)?;
                return Ok(e);
            }
            if st.items.len() > 1 && rest.is_empty() && self.is_call(x) && !self.number_step_name(k) {
                return Err(match self.defs.get(k) {
                    Some(_) if self.param(k).is_none() => format!("{k} gives a group, not a number: {}; an expression reads variables and number functions", self.sig_named(k)),
                    _ => self.name_atom(k).err().unwrap_or_else(|| format!("expected ), found {}", self.tok(st.items[1].at))),
                });
            }
        }
        if !rest.is_empty() {
            return self.number_pipe(pl);
        }
        let e = self.expr(head)?;
        if let Some(y) = st.items.get(1) {
            return Err(format!("expected ), found {}", self.tok(y.at)));
        }
        Ok(e)
    }

    /// A pipeline that ends with a step that gives a number, in parentheses (`(lowbits |
    /// size)`).
    fn number_pipe(&mut self, pl: &Pipeline) -> Result<Pipe, String> {
        let (stages, tail) = self.stages(Stages::of(pl), Vec::new())?;
        let p = seq_of(stages);
        let Some(e) = tail else { return Err(format!("({}) gives a group, not a number: end it with a step that gives a number, as in (a | size)", show(&p))) };
        Ok(number_seq(p, e))
    }

    /// A call of the function `n` defined with parameters, after its name: a call of a
    /// `def` with the name arguments in place in its body, or an `@inline` body with all
    /// arguments in place.
    pub(crate) fn def_call(&mut self, n: &str, c: &mut Items) -> Result<Pipe, String> {
        let defs = self.defs;
        let d = &defs[n];
        let sig = self.sig_named(n);
        // `(main NAME)` reads NAME as a group variable, also one nothing binds, for the checks to
        // report.
        if let (Some(_), true, Some(Syn { node: Node::Name(g), .. })) = (&d.input, d.params.is_empty(), c.peek())
            && c.before_close()
            && !self.defs.contains_key(*g)
        {
            c.k += 1;
            self.group_name(g)?;
            self.used.push(n.to_string());
            return self.call_of(n, Vec::new(), Some(group(g.to_string())));
        }
        let takes_input = d.input.is_some() || d.def.as_ref().is_some_and(|d| d.input.is_some());
        if d.params.is_empty() && !self.input_next(c, takes_input) {
            return Err(format!("{n} takes {}: {sig}", sig.arity()));
        }
        let reading = def_sig(n, &d.params);
        let args = match d.params.is_empty() && takes_input {
            true => Vec::new(),
            false => self.args(&reading, true, c).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()).replace(&format!("{n} takes {}", reading.arity()), &format!("{n} takes {}", sig.arity())))?,
        };
        let input = self.group_input_of(c, !d.params.is_empty() || takes_input)?;
        self.used.push(n.to_string());
        if d.input.is_some() {
            return self.call_of(n, args, input);
        }
        let call = self.call_of(n, args, None)?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        match input {
            _ if d.def.as_ref().is_some_and(|d| d.value.is_some()) => Err(format!("{n} gives a number, not a group: {sig}; a step calls a function that gives a group")),
            Some(i) if step => Ok(explicit(i, call)),
            Some(_) => Err(format!("{n} takes {}: {sig}", sig.arity())),
            None => Ok(call),
        }
    }

    /// The arguments of a call of the function `n` defined whose body is an expression, after
    /// its name, and its input when written.
    fn number_def_call(&mut self, n: &str, c: &mut Items) -> Result<Pipe, String> {
        let defs = self.defs;
        let d = &defs[n];
        let sig = self.sig_named(n);
        let reading = def_sig(n, &d.params);
        let args = self.args(&reading, true, c).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()).replace(&format!("{n} takes {}", reading.arity()), &format!("{n} takes {}", sig.arity())))?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        let input = match step {
            true => self.group_input_of(c, !d.params.is_empty())?,
            false => None,
        };
        self.used.push(n.to_string());
        let Pipe::App(f, args) = self.call_of(n, args, None)? else { unreachable!("a function whose body is an expression is a def") };
        Ok(Pipe::App(f, args.iter().cloned().chain(input).collect()))
    }
}

/// Whether the number `e` is a function applied to the step's input: a built-in, a `def` or
/// a function variable, maybe the first operand of an operator.
fn named_number(e: &Pipe) -> bool {
    match e {
        Pipe::App(Fun::Builtin(b), _) => b.sig.is_number(),
        Pipe::App(Fun::Def(c), _) => c.def.value.is_some(),
        Pipe::Var(Slot::Local(_, Holds::Fn(_))) => true,
        _ => false,
    }
}

/// The error for the number `e` where a pipeline that gives a group is taken.
fn not_group(e: &Pipe) -> String {
    match e {
        Pipe::App(Fun::Builtin(b), _) if b.sig.is_number() => not_a_step(b.sig),
        Pipe::App(Fun::Builtin(b), _) if b.sig.is_text() => text_step(b.sig),
        Pipe::App(Fun::Def(c), _) if c.def.value.is_some() => format!("{} gives a number, not a group: {}; a step calls a function that gives a group", c.def.name, sig_of(&c.def)),
        Pipe::Var(Slot::Local(n, Holds::Fn(t))) => format!("{n} gives a number, not a group: it holds {t}; a step calls a function that gives a group"),
        Pipe::App(Fun::Op(..), args) if args.first().is_some_and(named_number) => not_group(&args[0]),
        Pipe::Num(n) => format!("expected a pass or (, found {}", show_expr(&Pipe::Num(*n), 7)),
        e => format!("{} gives a number, not a group: a pipeline that ends in a number goes where a number does, as in x = (a | size)", piped(e).unwrap_or_else(|| show_expr(e, 1))),
    }
}

/// The error for a form no longer read: the item `x`, or the first one in parentheses.
fn old_form(x: &Syn) -> Option<&'static str> {
    let y = match x.head_stage() {
        Some((s, _)) => &s.items[0],
        None => x,
    };
    match &y.node {
        Node::Name("with") => Some(NO_WITH),
        Node::Op("-", a, b) if a.name() == Some("time") && b.name() == Some("limit") => Some(NO_TIME_LIMIT),
        _ => None,
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
        super::warn::unknown(format!("unknown variable {n}"), n, super::vars::var_names())
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
        _ => super::warn::unknown(format!("unknown pass {n}"), n, step_names()),
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
    parse_assign_on(name, val, &super::source::prelude(), &TopNames { value: true, ..Default::default() })
}

/// Whether `n` can name a local variable of a statement: it names no variable, function,
/// definition or word of the language.
pub(crate) fn can_be_local(n: &str, defs: &Defs) -> bool {
    !(defs.contains_key(n) || known_name(n) || resolve(n).is_some() || ["none", "def", "extern"].contains(&n))
}

/// `parse_assign` as a top-level item of a program: the names of `defs` and the local
/// variables of the statements before (`top`) are known, and the step has an input only
/// where one of them gave a value.
pub(crate) fn parse_assign_on(name: &str, val: &str, defs: &Defs, top: &TopNames) -> Result<Pipe, String> {
    let go = || {
        assignable(name)?;
        let toks = lex(val)?;
        let rhs = super::reader::value(&toks)?;
        let mut p = Elab::new(&toks, defs);
        p.groups = top.groups.clone();
        p.locals = top.locals.clone();
        p.fns = top.fns.clone();
        p.input = top.value;
        p.top = true;
        p.assign(name, &rhs)
    };
    go().map_err(|e| hyphen_hint(e, val))
}

/// The top-level statement `s` of a program: its steps, each with what it gives; `top` the
/// local variables the statements before bound, to which it adds its own.
/// `toks`: `s` lexed, or `None` to lex it here.
pub(crate) fn parse_statement(s: &str, toks: Option<&[Tok]>, defs: &Defs, top: &mut TopNames, used: &mut Vec<String>) -> Result<Vec<Top>, String> {
    let lexed;
    let toks = match toks {
        Some(t) => t,
        None => {
            lexed = lex(s).map_err(|e| hyphen_hint(e, s))?;
            &lexed
        }
    };
    let go = || {
        let pl = super::reader::statement(toks)?;
        let mut p = Elab::new(toks, defs);
        p.groups = top.groups.clone();
        p.locals = top.locals.clone();
        p.fns = top.fns.clone();
        p.input = top.value;
        p.tuples = top.tuples.clone();
        p.top = true;
        let tops = p.statement(&pl)?;
        Ok((tops, p.used, p.groups, p.locals, p.fns, p.tuples))
    };
    let (tops, names, groups, locals, fns, tuples) = go().map_err(|e: String| hyphen_hint(e, s))?;
    used.extend(names);
    let value = top.value || tops.iter().any(|t| matches!(t.gives, Gives::Group) && starts_with_value(&t.pipe));
    *top = TopNames { groups, locals, fns, value, tuples };
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
        let toks = lex(s)?;
        let pl = super::reader::statement(&toks)?;
        let mut p = Elab::new(&toks, defs);
        p.top = true;
        let pipe = p.pipe(Stages::of(&pl))?;
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
    use crate::lang::lexer::lex;
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
        let main_g = &main_g[1];
        assert_eq!(parse("(save g) | (if (mixed (main g)) id)").unwrap(), Pipe::Seq(vec![Pipe::app("save", vec![Pipe::Name("g".into())]), Pipe::app("if", vec![Pipe::app("mixed", vec![main_g.clone()]), Pipe::id(), Pipe::id()])]), "the input written follows the arguments");
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
