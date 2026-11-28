//! The tree of the pipeline language, steps and expressions alike, and how it is printed
//! back as source.

use super::builtins::Operator;
use super::defs::Call;
use super::lexer::quoted;
use super::types::{Param, Rep, Ty};
use super::vars::{NONE, var};
use std::fmt;

/// A term of the pipeline language (`crate::lang`): a step, which maps a list of
/// equivalent candidate terms (the first is the main one) to another, so any step can follow
/// any other (`lowbits | rewrite | (fix 3 egglog)`), or an expression, evaluated on the
/// candidates to a number or `NONE` (true when not 0). Every function, built-in (the
/// operators too) or defined, is applied by an `App`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pipe {
    /// A number; `NONE` is `none`.
    Num(u64),
    /// A name argument: a stats or origin name, an egglog label, a note register, or the group
    /// variable a built-in binds or reads (`(save t)`, `(load t)`).
    Name(String),
    /// A string literal (`text`), its escapes read.
    Text(String),
    /// A read of a variable or parameter.
    Var(Slot),
    /// A function applied to its arguments in the order of its parameters. For a built-in,
    /// an optional one not written is left out, except the second branch of `if`, which is
    /// `id`; for a function that gives a number, the input written follows the arguments
    /// (`(minimal g)`, `(size (main g))`; `builtins::Builtin::input_at`). Written without the
    /// arguments it is a function value (`print`).
    App(Fun, std::sync::Arc<[Pipe]>),
    /// Each in turn on the candidates of the one before (`a | b`), as a scope. Where the last
    /// gives a number (`(lowbits | size)`), so does the sequence: the last on what the others
    /// give, those as a scope that ends before it.
    Seq(Vec<Pipe>),
    /// `NAME = VALUE`, the input passing on unchanged. A global binds in the enclosing scope
    /// to the number the right side gives (a switch is on for any value but 0, `time_limit`
    /// takes milliseconds from now), a local number variable likewise in the run's table, a
    /// group variable to the candidates the right side gives as a scope of its own, a
    /// function variable to the right side as a closure over the values of the variables it
    /// reads (`crate::lang::eval::Closure`).
    Bind(Slot, std::sync::Arc<Pipe>),
    /// A macro call as written and what it expands to, which is what runs.
    Expanded(Box<Expanded>),
}

/// A variable or parameter, resolved when parsed.
#[derive(Clone, Debug, PartialEq)]
pub enum Slot {
    /// A global variable, by its position in `VARS`, looked up along the calls; `time_limit`
    /// reads as the milliseconds left, `keep` as at least 1.
    Global(usize),
    /// A local variable of the run, looked up in the text. A group variable read gives its
    /// candidates whatever the input; a function variable is applied to the input.
    Local(String, Holds),
    /// A parameter of the function whose body this is, by its position, and its name: a
    /// pipeline argument runs where the call is written, a numeric one gives the value it had
    /// at the call.
    Param(usize, String),
}

/// What a local variable holds.
#[derive(Clone, Debug, PartialEq)]
pub enum Holds {
    Num,
    Group,
    Fn(super::types::Ty),
}

/// The function an `App` applies: a built-in, an operator (a built-in too, its `Impl` held
/// in the node so that evaluating it reads nothing else) or a `def`.
#[derive(Clone, Debug, PartialEq)]
pub enum Fun {
    Builtin(&'static super::builtins::Builtin),
    Op(super::builtins::Operator, &'static super::builtins::Builtin),
    Def(std::sync::Arc<Call>),
}

impl Fun {
    /// The type of the parameter argument `i` of `args` is for; `None` for the input written
    /// after the arguments of a function that gives a number, or as the only one (`parse`).
    pub fn param_ty(&self, args: &[Pipe], i: usize) -> Option<&super::types::Ty> {
        match self {
            Fun::Builtin(b) if b.input_at(args) == Some(i) => None,
            Fun::Builtin(b) | Fun::Op(_, b) => b.sig.params.get(i).or(b.sig.params.last()).map(|p| &p.ty),
            Fun::Def(c) => c.def.params.get(i).map(|p| &p.ty),
        }
    }
}

/// A macro call (`(smallest p)`, `(off NAME ...)`, `(on NAME ...)`) as written, `head` and
/// `args`, which `--show-passes`, errors, checks and warnings read, and its expansion, which
/// runs.
#[derive(Clone, Debug)]
pub struct Expanded {
    pub head: &'static str,
    pub args: Vec<Pipe>,
    pub steps: Vec<Pipe>,
    /// The steps are a scope; otherwise they run in the enclosing one, as the call would.
    pub scoped: bool,
    /// The macro's declaration is `@timed`: past the time limit the call is skipped whole.
    pub timed: bool,
}

impl PartialEq for Expanded {
    fn eq(&self, o: &Expanded) -> bool {
        self.head == o.head && self.args == o.args
    }
}

impl Pipe {
    /// The built-in function `name` applied to `args`; `name` must be declared.
    pub fn app(name: &str, args: Vec<Pipe>) -> Pipe {
        let b = super::builtins::builtin(name).unwrap_or_else(|| panic!("no built-in {name}"));
        match b.imp {
            super::builtins::Impl::Operator(o) => Pipe::App(Fun::Op(o, b), args.into()),
            _ => Pipe::App(Fun::Builtin(b), args.into()),
        }
    }

    /// The step `id`.
    pub fn id() -> Pipe {
        Pipe::app("id", Vec::new())
    }

    /// Whether this is the step `id`.
    pub fn is_id(&self) -> bool {
        matches!(self, Pipe::App(Fun::Builtin(b), _) if b.name == "id")
    }

    /// The `Def` this calls, and the arguments.
    pub fn call(&self) -> Option<(&std::sync::Arc<Call>, &[Pipe])> {
        match self {
            Pipe::App(Fun::Def(c), args) => Some((c, args)),
            _ => None,
        }
    }

    /// Whether this is a function written as a value, without arguments, that gives
    /// candidates, or a function variable: `print` writes its signature.
    pub fn is_function_value(&self) -> bool {
        match self {
            Pipe::Var(Slot::Local(_, Holds::Fn(_))) => true,
            Pipe::App(Fun::Builtin(b), _) => !b.sig.is_number(),
            Pipe::App(Fun::Def(c), _) => c.def.value.is_none(),
            _ => false,
        }
    }

    /// Whether this gives a term? (`(main r)`, `(index i r)`): steps whose last picks one
    /// candidate of a group.
    pub fn picks(&self) -> bool {
        matches!(self, Pipe::Seq(ps) if matches!(ps.last(), Some(Pipe::App(Fun::Builtin(b), _)) if b.sig.kind() == super::types::Kind::Pick))
    }

    /// The global variable at `i`, read.
    pub fn global(i: usize) -> Pipe {
        Pipe::Var(Slot::Global(i))
    }

    /// `x = e` for the global variable at `i`.
    pub fn assign(i: usize, e: Pipe) -> Pipe {
        Pipe::Bind(Slot::Global(i), std::sync::Arc::new(e))
    }
}

impl fmt::Display for Pipe {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show(self))
    }
}

impl Pipe {
    /// `f` on each pipeline directly inside `self`, also inside its expressions: the
    /// pipeline arguments, the steps of a sequence and the inputs written of calls, the
    /// pipeline arguments of a call (not the body it calls).
    pub fn each<'p>(&'p self, f: &mut dyn FnMut(&'p Pipe)) {
        match self {
            Pipe::App(fun, args) => {
                for (i, a) in args.iter().enumerate() {
                    match fun.param_ty(args, i) {
                        Some(t) if !t.is_step() => a.each_in_expr(f),
                        _ => f(a),
                    }
                }
            }
            Pipe::Seq(ps) => ps.iter().for_each(f),
            Pipe::Expanded(m) => m.args.iter().filter(|a| !matches!(a, Pipe::Name(_))).for_each(f),
            Pipe::Bind(Slot::Local(_, Holds::Group), p) => f(p),
            Pipe::Bind(Slot::Local(_, Holds::Fn(t)), p) if t.is_step() => f(p),
            Pipe::Bind(_, e) => e.each_in_expr(f),
            Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::Var(_) => {}
        }
    }

    /// `each` for the expression `self`, where a sequence gives a number: its steps before the
    /// last are pipelines, the last an expression.
    fn each_in_expr<'p>(&'p self, f: &mut dyn FnMut(&'p Pipe)) {
        match self {
            Pipe::Seq(ps) => {
                let (e, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
                steps.iter().for_each(&mut *f);
                e.each_in_expr(f);
            }
            e => e.each(f),
        }
    }
}

/// The operator `p` applies, and its operands.
pub(crate) fn op_of(p: &Pipe) -> Option<(Operator, &[Pipe])> {
    match p {
        Pipe::App(Fun::Op(o, _), args) => Some((*o, args)),
        _ => None,
    }
}

/// Whether `p` gives its candidates whatever its input: it starts with a group value.
pub fn starts_with_value(p: &Pipe) -> bool {
    match p {
        Pipe::Var(Slot::Local(_, Holds::Group)) => true,
        Pipe::Seq(ps) => ps.first().is_some_and(starts_with_value),
        Pipe::App(Fun::Def(c), _) => !c.def.step,
        Pipe::App(Fun::Builtin(b), _) => b.sig.kind() == super::types::Kind::FromText,
        _ => false,
    }
}

/// The right side of an assignment.
pub fn show_assigned(e: &Pipe) -> String {
    show_expr(e, 1)
}

/// `e` where an operand of precedence `need` stands: `||` is 1, `&&` 2, `!` 3, a comparison
/// 4, `+ -` 5, `* /` 6, the rest 7.
pub(crate) fn show_expr(e: &Pipe, need: u8) -> String {
    let (s, prec) = match e {
        Pipe::Num(NONE) => ("none".into(), 7),
        Pipe::Num(n) => (n.to_string(), 7),
        _ if op_of(e).is_some() => {
            let (o, args) = op_of(e).unwrap();
            let all = |need: u8, sep: &str| args.iter().map(|c| show_expr(c, need)).collect::<Vec<_>>().join(sep);
            match o {
                Operator::Not => (format!("!{}", show_expr(&args[0], 7)), 3),
                Operator::And => (all(3, " && "), 2),
                Operator::Or => (all(2, " || "), 1),
                Operator::Cmp(op) => (format!("{} {} {}", show_expr(&args[0], 5), op.symbol(), show_expr(&args[1], 5)), 4),
                Operator::Arith(op) => {
                    let prec = if matches!(op, '+' | '-') { 5 } else { 6 };
                    (format!("{} {op} {}", show_expr(&args[0], prec), show_expr(&args[1], prec + 1)), prec)
                }
            }
        }
        Pipe::App(Fun::Builtin(b), args) if b.input_at(args).is_some_and(|k| !matches!(args[k], Pipe::Var(Slot::Local(_, Holds::Group))) && !args[k].picks()) => (format!("({})", piped(e).unwrap()), 7),
        Pipe::App(Fun::Builtin(b), args) if args.is_empty() => (b.name.to_string(), 7),
        Pipe::App(Fun::Builtin(b), args) => (form(b.name, &args.iter().map(|a| if let Pipe::Name(n) = a { n.clone() } else { show_expr(a, 1) }).collect::<Vec<_>>()), 7),
        Pipe::Var(Slot::Global(i)) => (var(*i).name.to_string(), 7),
        Pipe::Var(Slot::Param(_, n)) => (n.clone(), 7),
        Pipe::Seq(ps) => match &ps[..] {
            [Pipe::Var(Slot::Local(r, Holds::Group)), f] if matches!(f, Pipe::App(Fun::Builtin(b), _) if b.sig.input.as_ref().is_some_and(|i| i.ty == Ty::Group)) || matches!(f, Pipe::Var(Slot::Param(..) | Slot::Local(_, Holds::Fn(_)))) => {
                let s = show_expr(f, 7);
                let inner = s.strip_prefix('(').and_then(|s| s.strip_suffix(')')).unwrap_or(&s);
                (format!("({inner} {r})"), 7)
            }
            _ => (format!("({})", piped(e).unwrap()), 7),
        },
        Pipe::App(Fun::Def(_), _) => (show(e), 7),
        p => (show(p), 7),
    };
    if prec < need { format!("({s})") } else { s }
}

/// The expression `e` written as steps and the number of them, `p | e`: a sequence that gives
/// a number, or a number function with its input written other than a group value.
pub(crate) fn piped(e: &Pipe) -> Option<String> {
    match e {
        Pipe::Seq(ps) => {
            let (last, steps) = ps.split_last()?;
            let steps = match steps {
                [p] => show(p),
                ps => show(&Pipe::Seq(ps.to_vec())),
            };
            Some(format!("{steps} | {}", show_expr(last, 1)))
        }
        Pipe::App(f @ Fun::Builtin(b), args) => {
            let k = b.input_at(args).filter(|k| !args[*k].picks())?;
            Some(format!("{} | {}", show(&args[k]), show_expr(&Pipe::App(f.clone(), args[..k].into()), 1)))
        }
        _ => None,
    }
}

/// `e` as an argument of a form.
fn show_arg(e: &Pipe) -> String {
    match op_of(e) {
        Some((Operator::Not, x)) => format!("!{}", show_arg(&x[0])),
        _ => show_expr(e, 7),
    }
}

/// `p` written as a stage: a sequence in parentheses.
pub fn show_stage(p: &Pipe) -> String {
    stage(p)
}

pub(crate) fn stage(p: &Pipe) -> String {
    match p {
        Pipe::Seq(ps) if ps.len() > 1 => format!("({})", show(p)),
        _ => show(p),
    }
}

pub(crate) fn form(head: &str, args: &[String]) -> String {
    format!("({head} {})", args.join(" "))
}

/// The arguments of a step `b` applied to `args` as written: each pipeline (`true`) or other
/// argument (`false`) and, for a pipeline, whether it is written as a stage (one of several
/// pipelines) rather than read up to `)`; an `id` for an optional pipeline left out.
fn app_args<'p>(b: &super::builtins::Builtin, args: &'p [Pipe]) -> Vec<(&'p Pipe, Option<bool>)> {
    let pipes = b.sig.params.iter().filter(|p| p.ty.is_step()).count();
    let last = b.sig.params.len().saturating_sub(1);
    args.iter()
        .enumerate()
        .filter_map(|(i, a)| {
            let p = b.sig.param(i);
            match () {
                _ if !p.ty.is_step() => Some((a, None)),
                _ if p.rep == Rep::Opt && a.is_id() => None,
                _ => Some((a, Some(!(pipes == 1 && i == last && p.rep == Rep::One)))),
            }
        })
        .collect()
}

/// The position of the parameter of `params` that a call reads up to `)`, as a built-in's: the
/// last one when it is the only pipeline parameter (written without parentheses unless it
/// starts with a group value, which would read as the input).
fn read_to_close(params: &[Param]) -> Option<usize> {
    let last = params.len().checked_sub(1)?;
    (params.iter().filter(|p| p.ty.is_step()).count() == 1 && params[last].ty.is_step() && params[last].rep == Rep::One).then_some(last)
}

/// An argument of a step that is not a pipeline.
fn show_fixed(a: &Pipe) -> String {
    match a {
        Pipe::Name(n) => n.clone(),
        a => show_arg(a),
    }
}

/// The argument `a` of a call for the parameter `p`.
fn show_call_arg(a: &Pipe, p: &Param) -> String {
    match (&p.ty, a) {
        (_, Pipe::Name(n)) | (Ty::Group, Pipe::Var(Slot::Local(n, Holds::Group))) => n.clone(),
        (t, a) if t.is_step() => stage(a),
        (_, a) => show_arg(a),
    }
}

/// `p` in the pipeline language, on one line.
pub fn show(p: &Pipe) -> String {
    let stages = |ps: &[Pipe]| ps.iter().map(stage).collect::<Vec<_>>();
    match p {
        Pipe::App(Fun::Builtin(b), args) if b.sig.params.is_empty() && !args.is_empty() => form(b.name, &args.iter().map(|a| if let Pipe::Text(t) = a { quoted(t) } else { show_expr(a, 7) }).collect::<Vec<_>>()),
        Pipe::App(Fun::Builtin(b), args) if !b.sig.is_number() => {
            let shown: Vec<String> = app_args(b, args)
                .into_iter()
                .map(|(a, at)| match at {
                    None => show_fixed(a),
                    Some(true) => stage(a),
                    Some(false) => show(a),
                })
                .collect();
            if shown.is_empty() { b.name.to_string() } else { form(b.name, &shown) }
        }
        Pipe::Seq(ps) if ps.len() > 1 => stages(ps).join(" | "),
        Pipe::Seq(ps) => form("seq", &stages(ps)),
        Pipe::Expanded(m) => form(m.head, &m.args.iter().map(show).collect::<Vec<_>>()),
        Pipe::App(Fun::Def(c), args) => {
            let last = read_to_close(&c.def.params);
            let all: Vec<String> = args.iter().zip(&c.def.params).enumerate().map(|(i, (a, p))| if Some(i) == last && !starts_with_value(a) { show(a) } else { show_call_arg(a, p) }).chain(args.get(c.def.params.len()).map(stage)).collect();
            if all.is_empty() { c.def.name.clone() } else { form(&c.def.name, &all) }
        }
        Pipe::Var(Slot::Param(_, n) | Slot::Local(n, _)) | Pipe::Name(n) => n.clone(),
        Pipe::Text(t) => quoted(t),
        Pipe::Bind(Slot::Local(n, Holds::Num), e) => format!("{n} = {}", show_assigned(e)),
        Pipe::Bind(Slot::Local(n, Holds::Group), q) => format!("{n} = {}", bound(q, show(q))),
        Pipe::Bind(Slot::Local(n, Holds::Fn(t)), q) if t.is_step() => format!("{n}:{t} = {}", stage(q)),
        Pipe::Bind(Slot::Local(n, Holds::Fn(t)), q) => format!("{n}:{t} = {}", show_assigned(q)),
        Pipe::Bind(Slot::Global(i), v) => format!("{} = {}", var(*i).name, show_assigned(v)),
        Pipe::Bind(Slot::Param(..), _) => unreachable!("a parameter is not assigned"),
        e => show_expr(e, 1),
    }
}

/// The right side `q` of a `Bind`, written `s`, as a stage: an assignment in parentheses.
fn bound(q: &Pipe, s: String) -> String {
    match q {
        Pipe::Seq(ps) if ps.len() > 1 => format!("({s})"),
        Pipe::Bind(..) => format!("({s})"),
        _ => s,
    }
}

pub(crate) const WIDTH: usize = 100;

/// `p` in the pipeline language over several lines, each at most about `WIDTH` wide, nested
/// pipelines indented.
pub fn pretty(p: &Pipe) -> String {
    pretty_at(p, 0)
}

pub(crate) fn pretty_at(p: &Pipe, indent: usize) -> String {
    let one = show(p);
    if indent + one.len() <= WIDTH {
        return one;
    }
    let pad = " ".repeat(indent + 2);
    let nested = |head: &str, fixed: Vec<String>, ps: Vec<(&Pipe, bool)>| {
        let mut s = format!("({head}");
        for f in fixed {
            s += &format!(" {f}");
        }
        for (q, as_stage) in ps {
            let body = pretty_at(q, indent + 2);
            let body = if as_stage && matches!(q, Pipe::Seq(ps) if ps.len() > 1) { format!("({body})") } else { body };
            s += &format!("\n{pad}{body}");
        }
        s + ")"
    };
    match p {
        Pipe::Seq(ps) if ps.len() > 1 => {
            let lines: Vec<String> = ps.iter().enumerate().map(|(i, q)| pretty_stage(q, if i == 0 { indent } else { indent + 2 })).collect();
            lines.join(&format!("\n{}| ", " ".repeat(indent)))
        }
        Pipe::Seq(ps) => nested("seq", vec![], many(ps)),
        Pipe::Expanded(m) if m.switch_names().is_none() => nested(m.head, vec![], m.args.iter().map(|a| (a, false)).collect()),
        Pipe::App(Fun::Builtin(b), args) if b.sig.params.iter().any(|q| q.ty.is_step()) => {
            let all = app_args(b, args);
            let fixed = all.iter().filter(|(_, at)| at.is_none()).map(|(a, _)| show_fixed(a)).collect();
            let ps = all.iter().filter_map(|(a, at)| at.map(|s| (*a, s))).collect();
            nested(b.name, fixed, ps)
        }
        Pipe::App(Fun::Def(c), args) if !args.is_empty() && args.len() <= c.def.params.len() => {
            let params = &c.def.params;
            let names = params.iter().take_while(|p| matches!(p.ty, Ty::Name | Ty::Num)).count();
            let last = read_to_close(params);
            let pipes: Vec<(&Pipe, bool)> = args.iter().zip(params).enumerate().skip(names).filter(|(_, (_, p))| p.ty.is_step()).map(|(i, (q, _))| (q, Some(i) != last || starts_with_value(q))).collect();
            if names + pipes.len() < args.len() {
                return one;
            }
            nested(&c.def.name, args[..names].iter().zip(params).map(|(a, p)| show_call_arg(a, p)).collect(), pipes)
        }
        Pipe::Bind(Slot::Local(n, Holds::Group), q) => format!("{n} = {}", bound(q, pretty_at(q, indent + 2))),
        _ => one,
    }
}

fn many(ps: &[Pipe]) -> Vec<(&Pipe, bool)> {
    ps.iter().map(|q| (q, true)).collect()
}

/// A stage of a sequence: a nested sequence in parentheses.
fn pretty_stage(p: &Pipe, indent: usize) -> String {
    let s = pretty_at(p, indent);
    if matches!(p, Pipe::Seq(ps) if ps.len() > 1) { format!("({s})") } else { s }
}
