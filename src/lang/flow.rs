//! What each step of a pipeline gives, a group, one term, a number or a text, checked against
//! what the next takes: a group given to a function whose input is a term runs it on each
//! element only when it gives terms or groups; one that gives a number or a text needs the
//! element written (`(size main)`). The same walk infers the types of a function's parameters
//! (`infer`), where a value whose type is not known yet takes the type of the input it goes to.

use super::ast::{Fun, Holds, Pipe, Slot, show_expr, value_ty};
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
    Tuple,
    /// Not known where it is read (a parameter's argument, a function variable).
    Unknown,
    /// No input: the top level of a program before a step gives a value.
    None,
    /// A group or a term, the type variable `k` while a function's parameters are inferred.
    Var(usize),
}

/// The error for the function `n` with signature `s`, called where the step has no input.
pub(crate) fn no_input(n: &str, s: &super::types::Sig) -> String {
    let element = s.input.as_ref().is_some_and(|i| i.ty != Ty::Group) && (s.is_number() || s.is_text());
    let (call, from) = match element {
        false => (format!("({n} t)"), format!("t | {n}")),
        true => (format!("({n} (main t))"), format!("t | main | {n}")),
    };
    format!("{n} has no input here: the top level of the program starts with none; write its input, as in {call}, or start from a value, as in {from}; {s}")
}

/// The error for a call of `f` on `input` where it has none (`no_input`), or where it is a
/// number or a text and `f` takes candidates.
fn needs(input: Flow, f: &Fun) -> Result<(), String> {
    let given = match input {
        Flow::None => "",
        Flow::Num => "a number",
        Flow::Text => "a text",
        Flow::Tuple => "a tuple",
        _ => return Ok(()),
    };
    let (n, s) = match f {
        Fun::Builtin(b) => (b.name.to_string(), b.sig.clone()),
        Fun::Def(c) => (c.def.name.clone(), super::defs::sig_of(&c.def)),
        Fun::Op(..) => return Ok(()),
    };
    match &s.input {
        _ if given.is_empty() => Err(no_input(&n, &s)),
        Some(i) if matches!(i.ty, Ty::Group | Ty::Term | Ty::MaybeTerm) => Err(format!("{n} takes {i}; its input here is {given}: {s}")),
        _ => Ok(()),
    }
}

/// Whether the call of `c` with `args` lacks only its last parameter, a tuple, which the step
/// before gives.
fn takes_tuple(c: &super::defs::Call, args: &[Pipe]) -> bool {
    args.len() + 1 == c.def.params.len() && c.def.params.last().is_some_and(|p| p.ty.positions().is_some())
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
        Pipe::App(f @ Fun::Builtin(b), args) => {
            let input = match takes(b) {
                Some(t) if b.sig.kind() == Kind::FromText => cx.joint(Flow::Text, t)?,
                Some(t) => {
                    needs(input, f)?;
                    cx.joint(input, t)?
                }
                None => input,
            };
            builtin_args(cx, b, args, input)?;
            match b.sig.kind() {
                Kind::Each | Kind::Alt if input == Flow::One => Flow::One,
                Kind::Pick => Flow::One,
                Kind::Tuple => Flow::Tuple,
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
        Pipe::App(f @ Fun::Def(c), args) if c.def.tuple.is_some() => {
            let input = match takes_tuple(c, args) {
                true => input,
                false => {
                    if c.def.step {
                        needs(input, f)?;
                    }
                    cx.joint(input, &def_takes(&c.def))?
                }
            };
            def_args(cx, c, args, input)?;
            Flow::Tuple
        }
        Pipe::Tuple(ps) => {
            positions(cx, ps, input)?;
            Flow::Tuple
        }
        Pipe::Index(t, _) => {
            step(cx, t, input)?;
            match value_ty(p) {
                Some(Ty::Group) => Flow::Group,
                Some(Ty::Num) => Flow::Num,
                Some(Ty::Text) => Flow::Text,
                Some(Ty::Tuple(_)) => Flow::Tuple,
                _ => Flow::Unknown,
            }
        }
        Pipe::Unpack(_, e) | Pipe::Bind(Slot::Local(_, Holds::Tuple(_)), e) => {
            step(cx, e, input)?;
            input
        }
        Pipe::Var(Slot::Local(_, Holds::Tuple(_))) => Flow::Tuple,
        Pipe::App(f @ Fun::Def(c), args) => {
            let input = match takes_tuple(c, args) {
                true => input,
                false => {
                    if c.def.step {
                        needs(input, f)?;
                    }
                    cx.joint(input, &def_takes(&c.def))?
                }
            };
            def_args(cx, c, args, input)?;
            Flow::Group
        }
        Pipe::App(Fun::Op(..), _) => {
            expr(cx, p, input)?;
            Flow::Num
        }
        Pipe::Expanded(m) if m.switch_names().is_some() => input,
        Pipe::Expanded(m) if m.is_call() => match step(cx, &m.steps[0], input) {
            // The function written out is the one without an input, not a step of its body.
            Err(e) if input == Flow::None && e.contains(" has no input here") => {
                let n = m.head;
                return Err(format!("{n} has no input here: the top level of the program starts with none; write its input, as in ({n} t), or start from a value, as in t | {n}"));
            }
            r => r?,
        },
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
        Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::FnValue(_) => input,
    })
}

/// Whether `p`, an argument of `print`, is a step that gives a group or a term: a function
/// written alone and applied.
pub(crate) fn is_group_step(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => !b.sig.is_number() && !b.sig.is_text(),
        Pipe::App(Fun::Def(c), _) => c.def.value.is_none(),
        Pipe::Expanded(_) => true,
        Pipe::Seq(ps) => ps.last().is_some_and(|q| !is_expr(q)),
        _ => false,
    }
}

/// Whether `p`, the last of a sequence, is an expression: the sequence gives a number.
pub(crate) fn is_expr(p: &Pipe) -> bool {
    match p {
        Pipe::App(Fun::Builtin(b), _) => b.sig.is_number(),
        Pipe::App(Fun::Op(..), _) | Pipe::Num(_) => true,
        Pipe::App(Fun::Def(c), _) => c.def.value.is_some(),
        Pipe::Index(..) => value_ty(p) == Some(Ty::Num),
        Pipe::Var(Slot::Global(_) | Slot::Local(_, Holds::Num)) => true,
        Pipe::Var(Slot::Local(_, Holds::Fn(t))) => matches!(t, Ty::Fn(_, b) if **b == Ty::Num),
        _ => false,
    }
}

/// Checks the expression `e` evaluated on `input`.
pub(crate) fn expr(cx: &mut Infer, e: &Pipe, input: Flow) -> Result<(), String> {
    match e {
        Pipe::App(f @ Fun::Builtin(b), args) => {
            let at = b.input_at(args).or((b.sig.is_text() && !args.is_empty()).then_some(0));
            let (own, args) = match at {
                Some(k) => (step(cx, &args[k], input)?, &args[..k]),
                None => (input, &args[..]),
            };
            let own = match takes(b) {
                Some(t) => {
                    needs(own, f)?;
                    cx.joint(own, t)?
                }
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
        Pipe::App(f @ Fun::Def(c), args) => {
            let own = match args.get(c.def.params.len()) {
                Some(q) => step(cx, q, input)?,
                None => input,
            };
            if takes_tuple(c, args) {
                return def_args(cx, c, args, input);
            }
            if c.def.step || c.def.implicit.is_some() {
                needs(own, f)?;
            }
            let own = cx.joint(own, &def_takes(&c.def))?;
            if own == Flow::Group && c.def.implicit == Some(Ty::Term) {
                cx.fail(format!("{} takes one term and its input here is a group: write the element, as in ({} ... main)", c.def.name, c.def.name))?;
            }
            def_args(cx, c, args, input)
        }
        Pipe::Var(Slot::Local(n, Holds::Fn(t))) if input == Flow::None => Err(format!("{n} has no input here: the top level of the program starts with none; it holds {t}")),
        Pipe::Var(Slot::Local(n, Holds::Fn(Ty::Fn(a, _)))) if input == Flow::Group && **a == Ty::Term => cx.fail(format!("{n} takes one term and its input here is a group: write the element, as in ({n} main)")),
        Pipe::Index(t, _) => step(cx, t, input).map(|_| ()),
        Pipe::Tuple(ps) => positions(cx, ps, input),
        _ => Ok(()),
    }
}

/// Checks the positions of a tuple evaluated on `input`: expressions, and steps whose groups
/// the positions hold.
fn positions(cx: &mut Infer, ps: &[(Pipe, Ty)], input: Flow) -> Result<(), String> {
    for (q, t) in ps {
        match t {
            Ty::Num | Ty::Text => expr(cx, q, input)?,
            Ty::Group => {
                let gives = step(cx, q, input)?;
                cx.result(gives, &Ty::Group)?;
            }
            Ty::Tuple(_) => {
                step(cx, q, input)?;
            }
            _ => {}
        }
    }
    Ok(())
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
            Ty::Any if is_group_step(a) => {
                step(cx, a, input)?;
            }
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
        Ty::Tuple(_) => step(cx, a, input).map(|_| ()),
        _ => Ok(()),
    }
}

fn from(t: &Ty) -> Flow {
    if *t == Ty::Group { Flow::Group } else { Flow::One }
}
