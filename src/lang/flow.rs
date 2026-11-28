//! What each step of a pipeline gives, a group, one term, a number or a text, checked against
//! what the next takes: a group given to a function whose input is a term runs it on each
//! element only when it gives terms or groups; one that gives a number or a text needs the
//! element written (`(size main)`). The same walk infers the types of a function's parameters
//! (`infer`), where a value whose type is not known yet takes the type of the input it goes to.

use super::ast::{Fun, Holds, Pipe, Slot, show_expr};
use super::builtins::Builtin;
use super::defs::Def;
use super::infer::Infer;
use super::types::{Kind, Param, Ty};

/// Checks the body of `d` on its input: one term where the input is a term, else a group.
pub(crate) fn body(d: &Def) -> Result<(), String> {
    body_of(&d.params, d.input.as_deref(), d.implicit.as_ref(), d.value.as_ref(), &d.body)
}

/// `body` for a function with parameters `params`, the input parameter `input`, the implicit
/// input `implicit`, and the expression `value` or else the steps `steps`.
pub(crate) fn body_of(params: &[Param], input: Option<&str>, implicit: Option<&Ty>, value: Option<&Pipe>, steps: &Pipe) -> Result<(), String> {
    let cx = &mut Infer::of_params(params, input, implicit);
    let input = if implicit == Some(&Ty::Term) { Flow::One } else { Flow::Group };
    match value {
        Some(v) => expr(cx, v, input),
        None => step(cx, steps, input).map(|_| ()),
    }
}

/// What a step gives.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Flow {
    Group,
    /// A term or none (`main`, `(index i r)`).
    One,
    Num,
    Text,
    /// Not known where it is read (a parameter's argument, a function variable).
    Unknown,
    /// A group or a term, the type variable `k` while a function's parameters are inferred.
    Var(usize),
}

/// The input type of `b`, `None` for a function without one.
fn takes(b: &Builtin) -> Option<&Ty> {
    b.sig.input.as_ref().map(|i| &i.ty)
}

/// The input type of a call of the `def` `d`.
fn def_takes(d: &Def) -> Ty {
    if d.implicit == Some(Ty::Term) { Ty::Term } else { Ty::Group }
}

/// What the step `p` gives on `input`, or the error of a function given a group where it takes
/// one term.
pub(crate) fn step(cx: &mut Infer, p: &Pipe, input: Flow) -> Result<Flow, String> {
    Ok(match p {
        Pipe::Seq(ps) => {
            let mut f = input;
            for (i, q) in ps.iter().enumerate() {
                f = match i + 1 == ps.len() && is_expr(q) {
                    true => {
                        expr(cx, q, f)?;
                        Flow::Num
                    }
                    false => step(cx, q, f)?,
                };
            }
            f
        }
        Pipe::App(Fun::Builtin(b), _) if b.sig.is_number() || b.sig.is_text() => {
            expr(cx, p, input)?;
            if b.sig.is_text() { Flow::Text } else { Flow::Num }
        }
        Pipe::App(Fun::Builtin(b), args) => {
            let input = match takes(b) {
                Some(t) => cx.joint(input, t)?,
                None => input,
            };
            builtin_args(cx, b, args, input)?;
            match b.sig.kind() {
                Kind::Each | Kind::Alt if input == Flow::One => Flow::One,
                Kind::Pick => Flow::One,
                Kind::Effect => input,
                // These give their input, or part of it.
                Kind::Group if matches!(b.name, "save" | "label" | "clear" | "note" | "id" | "filter" | "within" | "settle" | "pre_done") => input,
                _ => Flow::Group,
            }
        }
        Pipe::App(Fun::Def(c), _) if c.def.value.is_some() => {
            expr(cx, p, input)?;
            Flow::Num
        }
        Pipe::App(Fun::Def(c), args) => {
            let input = cx.joint(input, &def_takes(&c.def))?;
            def_args(cx, c, args, input)?;
            Flow::Group
        }
        Pipe::App(Fun::Op(..), _) => {
            expr(cx, p, input)?;
            Flow::Num
        }
        Pipe::Expanded(m) if m.switch_names().is_some() => input,
        Pipe::Expanded(m) if m.is_call() => step(cx, &m.steps[0], input)?,
        Pipe::Expanded(m) => {
            step(cx, &m.args[0], input)?;
            Flow::Group
        }
        Pipe::Var(Slot::Local(n, Holds::Group)) => cx.value(n)?.unwrap_or(Flow::Group),
        Pipe::Var(Slot::Param(i, _)) => cx.param_step(*i, input, p)?,
        Pipe::Var(_) => Flow::Unknown,
        Pipe::Bind(Slot::Local(_, Holds::Group), q) => {
            let gives = step(cx, q, input)?;
            cx.result(gives, &Ty::Group)?;
            input
        }
        Pipe::Bind(Slot::Local(_, Holds::Fn(_)), _) => input,
        Pipe::Bind(_, e) => {
            expr(cx, e, input)?;
            input
        }
        Pipe::Drop(q, true) => {
            expr(cx, q, input)?;
            input
        }
        Pipe::Drop(q, false) => {
            step(cx, q, input)?;
            input
        }
        Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::FnValue(_) => input,
    })
}

/// Whether `p`, the last of a sequence, is an expression: the sequence gives a number.
fn is_expr(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => b.sig.is_number(),
        Pipe::App(Fun::Op(..), _) | Pipe::Num(_) => true,
        Pipe::App(Fun::Def(c), _) => c.def.value.is_some(),
        Pipe::Var(Slot::Global(_) | Slot::Local(_, Holds::Num)) => true,
        Pipe::Var(Slot::Local(_, Holds::Fn(t))) => matches!(t, Ty::Fn(_, b) if **b == Ty::Num),
        _ => false,
    }
}

/// Checks the expression `e` evaluated on `input`.
pub(crate) fn expr(cx: &mut Infer, e: &Pipe, input: Flow) -> Result<(), String> {
    match e {
        Pipe::App(Fun::Builtin(b), args) => {
            let at = b.input_at(args).or((b.sig.is_text() && !args.is_empty()).then_some(0));
            let (own, args) = match at {
                Some(k) => (step(cx, &args[k], input)?, &args[..k]),
                None => (input, &args[..]),
            };
            let own = match takes(b) {
                Some(t) => cx.joint(own, t)?,
                None => own,
            };
            if own == Flow::Group && takes(b).is_some_and(|t| matches!(t, Ty::Term | Ty::MaybeTerm)) {
                cx.fail(element(b, args))?;
            }
            builtin_args(cx, b, args, own)
        }
        Pipe::App(Fun::Op(..), args) => args.iter().try_for_each(|a| expr(cx, a, input)),
        Pipe::Seq(ps) => {
            let (last, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
            let mut f = input;
            for q in steps {
                f = step(cx, q, f)?;
            }
            expr(cx, last, f)
        }
        Pipe::App(Fun::Def(c), args) => {
            let own = match args.get(c.def.params.len()) {
                Some(q) => step(cx, q, input)?,
                None => input,
            };
            let own = cx.joint(own, &def_takes(&c.def))?;
            if own == Flow::Group && c.def.implicit == Some(Ty::Term) {
                cx.fail(format!("{} takes one term and its input here is a group: write the element, as in ({} ... main)", c.def.name, c.def.name))?;
            }
            def_args(cx, c, args, input)
        }
        Pipe::Var(Slot::Local(n, Holds::Fn(Ty::Fn(a, _)))) if input == Flow::Group && **a == Ty::Term => cx.fail(format!("{n} takes one term and its input here is a group: write the element, as in ({n} main)")),
        _ => Ok(()),
    }
}

/// The error for `b` with `args` given a group where it takes one term.
fn element(b: &Builtin, args: &[Pipe]) -> String {
    let call = show_expr(&Pipe::App(Fun::Builtin(super::builtins::builtin(b.name).unwrap()), args.into()), 7);
    let with = |x: &str| match call.strip_suffix(')') {
        Some(c) => format!("{c} {x})"),
        None => format!("({call} {x})"),
    };
    let input = b.sig.input.as_ref().unwrap();
    format!("{} takes {input} and gives {}; its input here is a group: write the element, as in {} or {}", b.name, b.sig.result, with("main"), with("(index i r)"))
}

/// Checks the arguments of a call of the built-in `b` whose input is `input`.
fn builtin_args(cx: &mut Infer, b: &Builtin, args: &[Pipe], input: Flow) -> Result<(), String> {
    for (i, a) in args.iter().enumerate() {
        let Some(p) = b.sig.params.get(i).or_else(|| b.sig.params.last().filter(|p| p.rep == super::types::Rep::Many)) else { continue };
        match &p.ty {
            Ty::Any if matches!(a, Pipe::Var(Slot::Local(..)) | Pipe::Name(_) | Pipe::Text(_)) || a.is_function_value() => {}
            Ty::Any | Ty::Num => expr(cx, a, input)?,
            t => arg(cx, t, a, input)?,
        }
    }
    Ok(())
}

/// Checks the arguments of a call of the `def` `c`.
fn def_args(cx: &mut Infer, c: &super::defs::Call, args: &[Pipe], input: Flow) -> Result<(), String> {
    for (a, p) in args.iter().zip(&c.def.params) {
        match &p.ty {
            Ty::Num => expr(cx, a, input)?,
            Ty::Term => {
                if step(cx, a, input)? == Flow::Group {
                    cx.fail(format!("{} takes {}:term; its argument here gives a group: write the element, as in (main r)", c.def.name, p.name))?;
                }
            }
            t => arg(cx, t, a, input)?,
        }
    }
    Ok(())
}

/// Checks an argument for a parameter of type `t`, a function or a group or a name, in a call
/// whose input is `input`: a function of a group is given that input, one of one term a term,
/// and what a function giving terms or groups gives goes where its result is.
fn arg(cx: &mut Infer, t: &Ty, a: &Pipe, input: Flow) -> Result<(), String> {
    let given = |i: &Ty| if *i == Ty::Group && input == Flow::One { Flow::One } else { from(i) };
    if let Pipe::Var(Slot::Param(i, _)) = a
        && t.is_step()
    {
        cx.param_arg(*i, t)?;
    }
    match t {
        Ty::Fn(i, r) if **r == Ty::Num => expr(cx, a, given(i)),
        Ty::Fn(i, r) => {
            let gives = step(cx, a, given(i))?;
            cx.result(gives, r)
        }
        _ => Ok(()),
    }
}

fn from(t: &Ty) -> Flow {
    if *t == Ty::Group { Flow::Group } else { Flow::One }
}
