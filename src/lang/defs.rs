//! Definitions: `(let NAME p)` and `(def ...)`, the functions they define, the types of their
//! parameters inferred from the body, and their calls with the arguments put in place.

use super::ast::{Expanded, Fun, Holds, Pipe, Slot, WIDTH, piped, pretty_at, show, show_expr, starts_with_value};
use super::builtins::{MACROS, get, resolve};
use super::host::{self, INNER, defined_builtin};
use super::lexer::{Tok, lex};
use super::macros::smallest;
use super::parser::{Arg, Parser, explicit, group, hyphen_hint, not_pipe, number_seq, seq_of};
use super::types::{Param, Rep, Sig, Ty};
use super::vars::var_index;
use std::sync::Arc;

/// A function `(def (NAME PARAM ...) body)` defined in `--passes` or `default.pipe`.
#[derive(Debug, PartialEq)]
pub struct Def {
    pub name: String,
    /// The parameters, their types inferred from the body: `pipe`, `num`, `group` or `name`.
    pub params: Vec<super::types::Param>,
    /// The body, name parameters written as their names.
    pub body: std::sync::Arc<Pipe>,
    /// `(def @inline ...)` with a numeric parameter: a call has its own arguments but no run
    /// of its own (other `@inline` functions are expanded where they are called).
    pub inline: bool,
    /// The body of an `inline` one is written `a | b`, which joins the caller's sequence.
    pub flat: bool,
    /// `@pipe`: the input parameter, bound to the candidates `|` gives; `None` in the form
    /// without it, whose body runs on the input as it is.
    pub input: Option<String>,
    /// Written as a step: `@pipe`, or the form without an input parameter.
    pub step: bool,
    /// The body when it gives a number: a call gives a number (`body` is then a `filter` of
    /// it, for the checks).
    pub value: Option<Pipe>,
    /// `value` runs steps (`lowbits | size`), so a call is a run of its own.
    pub steps: bool,
    /// The input `value` reads where it is not written, so that a call takes it implicitly
    /// (`(def (under k) size <= k)`).
    pub implicit: Option<super::types::Ty>,
}

impl Def {
    /// Whether a parameter is a name, which a call puts in place in its own copy of the body;
    /// a group parameter too in an `inline` one, which shares the caller's group variables.
    pub fn has_names(&self) -> bool {
        self.params.iter().any(|p| p.ty == super::types::Ty::Name || p.ty == super::types::Ty::Group && self.inline) || self.inline && self.input.is_some()
    }

    /// The group variables bound when the body starts: the group parameters and the input.
    pub fn bound(&self) -> Vec<String> {
        let groups = self.params.iter().filter(|p| p.ty == super::types::Ty::Group).map(|p| p.name.clone());
        groups.chain(self.input.clone()).collect()
    }
}

/// The `Def` an `App` calls, and its body with the name arguments in place of the name
/// parameters. The `App`'s arguments are one per parameter, as its type reads it: a name as
/// `Pipe::Name`, a group variable of the caller (passed by value) as its read, a pipeline,
/// or an expression evaluated once at the call on the caller's candidates.
#[derive(Debug)]
pub struct Call {
    pub def: std::sync::Arc<Def>,
    pub body: std::sync::Arc<Pipe>,
}

/// The body is made from the function and the arguments (an `@inline` one with an input
/// binds it under a name of its own for each call); the `App` compares the arguments.
impl PartialEq for Call {
    fn eq(&self, o: &Call) -> bool {
        self.def == o.def
    }
}

impl Call {
    /// The call of `def` without arguments.
    pub fn bare(def: &std::sync::Arc<Def>) -> Pipe {
        Pipe::App(Fun::Def(std::sync::Arc::new(Call { def: def.clone(), body: def.body.clone() })), Vec::new().into())
    }
}

/// What a name `(let NAME p)` or `(def ...)` defined stands for.
#[derive(Clone)]
pub struct Named {
    /// The pipeline expanded where it is used: `p`, or the call of a `def`.
    pub pipe: Pipe,
    /// Written as a sequence without parentheses, which joins the sequence it is used in
    /// (`(let g a | b)`; `(let g (a | b))` stays one nested stage).
    pub flat: bool,
    /// Defined by `(def (NAME ...) p)`: a function called as a run of its own.
    pub run: bool,
    /// The parameters, their types inferred from the body.
    pub params: Vec<Param>,
    /// The function `(def (NAME ...) p)` defines.
    pub def: Option<Arc<Def>>,
}

/// The names `let` and `def` defined.
pub type Defs = std::collections::HashMap<String, Named>;

/// How a definition item defines its name.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DefKind {
    /// `(let NAME p)`, the same as `Inline`.
    Let,
    /// `(def @inline (NAME) p)`: expanded where it is used.
    Inline,
    /// `(def (NAME) p)`: a call is a run of its own.
    Run,
}

/// A definition item read by `parse_definition`.
pub struct Definition {
    pub name: String,
    pub kind: DefKind,
    pub params: Vec<Param>,
    pub pipe: Pipe,
    pub flat: bool,
    /// `@pipe`: the input parameter, not among `params`.
    pub input: Option<String>,
    /// Written as a step: `@pipe` or the form without an input parameter.
    pub step: bool,
    /// The body when it gives a number.
    pub value: Option<Pipe>,
    /// The input a body that gives a number reads where it is not written (`size <= k`), so
    /// that the function takes it implicitly.
    pub implicit: Option<Ty>,
    /// Warnings of reading it.
    pub notes: Vec<String>,
}

/// A parameter of the function whose body is read, and the type its uses so far give it.
#[derive(Clone)]
pub(crate) struct ParamUse {
    pub(crate) name: String,
    pub(crate) ty: Option<Ty>,
    pub(crate) annotated: bool,
    /// Its uses, and those among them where a pipeline and a group fit alike (`t = r`, a body
    /// `r`).
    pub(crate) uses: usize,
    pub(crate) loose: usize,
}

impl<'a> Parser<'a> {
    pub(crate) fn param(&self, n: &str) -> Option<usize> {
        self.params.iter().position(|p| p.name == n)
    }

    /// Records a use of `n` as `ty` where `n` is a parameter; an error where an earlier use
    /// gave it another type.
    pub(crate) fn use_param(&mut self, n: &str, ty: Ty) -> Result<(), String> {
        let Some(i) = self.param(n) else { return Ok(()) };
        let p = &mut self.params[i];
        p.uses += 1;
        match &p.ty {
            Some(t) if *t == ty || matches!(t, Ty::Fn(..)) && t.fits(&ty) => Ok(()),
            Some(t) if p.annotated && matches!(t, Ty::Fn(..)) && !t.is_pipe() => Err(format!("parameter {n}:{t} is used where {ty} is wanted")),
            Some(t) if t.what() == ty.what() || matches!(t, Ty::Fn(..)) && !t.is_pipe() => Err(format!("parameter {n} is used as {t} and as {ty}")),
            Some(t) => Err(format!("parameter {n} is used as {} and as {}", t.what(), ty.what())),
            None => {
                p.ty = Some(ty);
                Ok(())
            }
        }
    }

    /// The signature of the function `n` defined.
    pub(crate) fn sig_named(&self, n: &str) -> Sig {
        let d = &self.defs[n];
        d.def.as_ref().map_or_else(|| def_sig(n, &d.params), |d| sig_of(d))
    }

    /// A call of the function `n` defined with parameters, after its name: a call of a
    /// `def` with the name arguments in place in its body, or an `@inline` body with all
    /// arguments in place.
    pub(crate) fn def_call(&mut self, n: &str, after_bar: bool) -> Result<Pipe, String> {
        let d = self.defs[n].clone();
        let sig = self.sig_named(n);
        if d.params.is_empty() && !self.input_ahead(false) {
            return Err(format!("{n} takes no arguments: {sig}"));
        }
        let mut reading = def_sig(n, &d.params);
        reading.pipe = true;
        let args = self.args(&reading, true).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()))?;
        let input = self.group_input(!d.params.is_empty())?;
        self.used.push(n.to_string());
        let call = self.call_of(n, args)?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        match input {
            _ if d.def.as_ref().is_some_and(|d| d.value.is_some()) => Err(format!("{n} gives a number, not candidates: {sig}; a step calls a function that gives candidates")),
            Some(i) if step => Ok(explicit(i, call)),
            Some(_) => Err(format!("{n} takes {}: {sig}", sig.takes())),
            None if !step && after_bar => Err(not_pipe(&sig)),
            None => Ok(call),
        }
    }

    /// The call of the function `n` defined with `args` read by its parameters.
    pub(crate) fn call_of(&self, n: &str, args: Vec<Arg>) -> Result<Pipe, String> {
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
            None => Subst::new(&d.params, &args, true, true, &open).pipe(&d.pipe),
        }
    }

    /// The arguments of a call of the function `n` defined whose body is an expression, after
    /// its name, and its input when written.
    pub(crate) fn number_def_call(&mut self, n: &str) -> Result<Pipe, String> {
        let d = self.defs[n].clone();
        let sig = self.sig_named(n);
        let mut reading = def_sig(n, &d.params);
        reading.pipe = true;
        let args = self.args(&reading, true).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()))?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        let input = match step {
            true => self.group_input(!d.params.is_empty())?,
            false => None,
        };
        if input.is_none() && step && self.no_input {
            return Err(format!("{n} needs its input here: {sig}"));
        }
        self.used.push(n.to_string());
        let Pipe::App(f, args) = self.call_of(n, args)? else { unreachable!("a function whose body is an expression is a def") };
        Ok(Pipe::App(f, args.iter().cloned().chain(input).collect()))
    }
}

/// The signature of the function `d` defined: its parameters and its input (`g` where the
/// input is implicit), its result `num` when the body is an expression.
pub fn sig_of(d: &Def) -> Sig {
    let mut sig = def_sig(&d.name, &d.params);
    if let Some(g) = &d.input {
        sig.input.as_mut().unwrap().name = g.clone();
    } else if !d.step && !d.params.is_empty() {
        sig.input = sig.params.pop();
    }
    sig.pipe = d.step;
    if d.value.is_some() {
        sig.result = Ty::Num;
    }
    if let Some(t) = &d.implicit {
        sig.input = Some(Param { name: if *t == Ty::Term { "t".into() } else { "g".into() }, ty: t.clone(), rep: Rep::One });
    }
    sig
}

/// Parses a definition item: `(let NAME p)`, `(def @inline (NAME) p)`, which `NAME` then
/// stands for where it is used, or `(def (NAME) p)`, a function called as a run of its own;
/// the names of `defs` it uses are added to `used`.
pub fn parse_definition(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    definition(s, defs, used).map_err(|e| hyphen_hint(e, s))
}

fn definition(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    let mut p = Parser::new(lex(s)?, defs);
    p.expect(Tok::Open, "(let or (def")?;
    let head = p.name("let or def")?;
    let mut params: Vec<String> = Vec::new();
    let mut types: Vec<Option<Ty>> = Vec::new();
    let mut piped = false;
    let (mut kind, name) = match head.as_str() {
        "let" => (DefKind::Let, p.name("a name after let")?),
        "def" => {
            let mut kind = DefKind::Run;
            while p.peek() == Some(&Tok::At) {
                p.at += 1;
                match p.name("an attribute after @")?.as_str() {
                    "inline" => kind = DefKind::Inline,
                    "pipe" => piped = true,
                    a => return Err(format!("unknown attribute @{a} of def; known: @inline @pipe")),
                }
            }
            p.expect(Tok::Open, "(NAME) after def")?;
            let name = p.name("a name after (def (")?;
            while p.peek() != Some(&Tok::Close) {
                let n = p.name(&format!("a parameter name or ) in (def ({name} ...)"))?;
                let ty = if p.peek() == Some(&Tok::Colon) {
                    p.at += 1;
                    let mut t = p.name("a type after :")?;
                    while p.peek() == Some(&Tok::Arrow) {
                        p.at += 1;
                        t = format!("{t}->{}", p.name("a type after ->")?);
                    }
                    match Ty::parse(&t) {
                        Ok(ty) if matches!(ty, Ty::Fn(..)) && !ty.is_function() => return Err(format!("type {t} of parameter {n}: a function takes one input, term or group, and gives num, term, term? or group")),
                        Ok(ty) if !matches!(ty, Ty::Term | Ty::MaybeTerm | Ty::Text | Ty::Any) => Some(ty),
                        _ => return Err(format!("unknown type {t} of parameter {n}; known: pipe group num name, and A->B as in term->num")),
                    }
                } else {
                    None
                };
                params.push(n);
                types.push(ty);
            }
            p.at += 1;
            (kind, name)
        }
        _ => return Err(format!("expected (let NAME pipeline) or (def (NAME) pipeline): {s}")),
    };
    let head: String = std::iter::once(name.as_str()).chain(params.iter().map(String::as_str)).collect::<Vec<_>>().join(" ");
    let what = match kind {
        DefKind::Let => format!("let {name}"),
        DefKind::Inline if piped => format!("def @inline @pipe ({head})"),
        DefKind::Inline => format!("def @inline ({head})"),
        DefKind::Run if piped => format!("def @pipe ({head})"),
        DefKind::Run => format!("def ({head})"),
    };
    if piped && (params.is_empty() || types.last().unwrap().as_ref().is_some_and(|t| *t != Ty::Group)) {
        return Err(format!("{what}: the last parameter of an @pipe function is its input, a group"));
    }
    let function = get(&name);
    let replaces = kind == DefKind::Run && defined_builtin(&name);
    if defined_builtin(&name) && !replaces {
        return Err(format!("{what}: {name} is a function the Rust code calls, replaced only by (def ({name}) p) or {name}=p"));
    }
    if !replaces && (function.is_some_and(|s| !s.is_number()) || resolve(&name).is_some() || MACROS.contains(&name.as_str()) || name == "extern" || name == "def") {
        return Err(format!("{what}: the name of a pass, form or macro"));
    }
    if !replaces && (var_index(&name).is_some() || function.is_some() || name == "none") {
        return Err(format!("{what}: the name of a variable or function"));
    }
    if kind == DefKind::Run && name.starts_with("sub_") && !replaces {
        let names: Vec<&str> = host::SUBS.iter().map(|(n, _)| *n).collect();
        return Err(format!("{what}: unknown sub_NAME; known: {}", names.join(" ")));
    }
    match defs.get(&name) {
        Some(d) if d.run => return Err(format!("{what}: {name} is already a function (def ({name}) ...)")),
        Some(_) if kind == DefKind::Run => return Err(format!("{what}: {name} is already defined by let or def @inline")),
        _ => {}
    }
    if replaces && !params.is_empty() {
        return Err(format!("{what}: {name} is called by the Rust code and takes no parameters"));
    }
    for (i, n) in params.iter().enumerate() {
        let taken = var_index(n).is_some() || get(n).is_some() || MACROS.contains(&n.as_str()) || resolve(n).is_some() || defined_builtin(n) || defs.contains_key(n);
        if taken || ["none", "def", "let", "extern"].contains(&n.as_str()) {
            return Err(format!("{what}: parameter {n} is the name of a variable, function or definition"));
        }
        if *n == name || params[..i].contains(n) {
            return Err(format!("{what}: parameter {n} is written twice"));
        }
    }
    let input = piped.then(|| params.last().unwrap().clone());
    if piped {
        *types.last_mut().unwrap() = Some(Ty::Group);
    }
    p.params = params.into_iter().zip(types).map(|(name, ty)| ParamUse { name, annotated: ty.is_some(), ty, uses: 0, loose: 0 }).collect();
    let mut value = match kind != DefKind::Let && p.expr_ahead() {
        true => {
            p.no_input = piped;
            let e = p.or()?;
            p.no_input = false;
            kind = DefKind::Run;
            Some(e)
        }
        false => None,
    };
    let implicit = value.as_ref().filter(|_| !piped).and_then(|e| p.input_ty(e));
    let (mut pipe, flat, tail) = match value {
        Some(_) => (Pipe::id(), false, None),
        None => {
            let (stages, tail) = p.stages_of_pipe()?;
            let flat = kind != DefKind::Run && stages.len() > 1;
            (seq_of(stages), flat, tail)
        }
    };
    if let Pipe::Var(Slot::Param(i, _)) = pipe {
        p.params[i].loose += 1;
    }
    p.expect(Tok::Close, ")")?;
    p.end()?;
    let starts = starts_with_value(&pipe);
    if piped && value.is_none() && !starts {
        return Err(format!("{what}: the body of an @pipe function starts with a value, as in {} | ..., or is an expression", input.as_deref().unwrap()));
    }
    let step = piped || value.is_none() && !starts || implicit.is_some();
    if let Some(e) = tail {
        if kind != DefKind::Run {
            return Err(format!("{what}: a function that gives a number is a run of its own, so it cannot be @inline or a let"));
        }
        value = Some(number_seq(std::mem::replace(&mut pipe, Pipe::id()), e));
    }
    let mut params = std::mem::take(&mut p.params);
    if piped {
        params.pop();
    }
    let notes = params
        .iter()
        .filter(|u| !u.annotated && u.ty.as_ref().is_some_and(Ty::is_pipe) && u.loose == u.uses)
        .map(|u| format!("({what} ...): parameter {0} is used only where a pipeline or a group fits, so it is read as a pipeline; write {0}:pipe, or {0}:group for a group", u.name))
        .collect();
    let params = params
        .into_iter()
        .map(|u| match u.ty {
            Some(ty) => Ok(Param { name: u.name, ty, rep: Rep::One }),
            None => Err(format!("{what}: parameter {} is never used in the body", u.name)),
        })
        .collect::<Result<Vec<_>, String>>()?;
    used.extend(p.used);
    Ok(Definition { name, kind, params, pipe, flat, input, step, value, implicit, notes })
}

/// The signature of a function `(def (NAME PARAM ...) p)`: its parameters, then the
/// candidates.
pub fn def_sig(name: &str, params: &[Param]) -> Sig {
    Sig {
        name: name.into(),
        params: params.to_vec(),
        input: Some(Param { name: "g".into(), ty: Ty::Group, rep: Rep::One }),
        result: Ty::Group,
        pipe: true,
        bookkeeping: false,
        simplify_only: false,
        uncounted: false,
        switch: false,
        doc: String::new(),
    }
}

fn def_head(d: &Def) -> String {
    let params = d.params.iter().map(|p| match &p.ty {
        Ty::Group => format!("{}:group", p.name),
        t @ Ty::Fn(..) if !t.is_pipe() => format!("{}:{t}", p.name),
        _ => p.name.clone(),
    });

    let head = std::iter::once(d.name.clone()).chain(params).chain(d.input.clone()).collect::<Vec<_>>().join(" ");
    match (d.inline, d.input.is_some()) {
        (true, true) => format!("@inline @pipe ({head})"),
        (true, _) => format!("@inline ({head})"),
        (_, true) => format!("@pipe ({head})"),
        _ => format!("({head})"),
    }
}

/// `(def (NAME PARAM ...) body)` on one line.
pub fn show_def(d: &Def) -> String {
    format!("(def {} {})", def_head(d), def_body(d, show(&d.body)))
}

/// `show_def` over several lines when it is wider than `WIDTH`.
pub fn pretty_def(d: &Def) -> String {
    let one = show_def(d);
    if one.len() <= WIDTH {
        return one;
    }
    format!("(def {}\n  {})", def_head(d), def_body(d, pretty_at(&d.body, 2)))
}

/// The body `s` of `d` as written: an `@inline` sequence that is not flat in parentheses.
fn def_body(d: &Def, s: String) -> String {
    match &d.value {
        Some(e) => return piped(e).unwrap_or_else(|| show_expr(e, 1)),
        None => {}
    }
    match &*d.body {
        Pipe::Seq(ps) if d.inline && !d.flat && ps.len() > 1 => format!("({s})"),
        _ => s,
    }
}

/// The body of a call of an `@inline` function with its pipeline arguments in place, as the
/// checks of group variables and assignments see it.
pub fn expand(c: &Call, args: &[Pipe]) -> Pipe {
    let pipes = args.iter().zip(&c.def.params).map(|(a, p)| p.ty.is_step().then_some(a)).collect();
    let s = Subst { names: Vec::new(), owned: Vec::new(), pipes, open: &|_| false };
    s.pipe(&c.body).expect("no name to put in place")
}

/// The body of a call of `def` with `args`: its name arguments in place (`open` as in
/// `Subst`).
fn instance(def: &Def, args: &[Pipe], open: &dyn Fn(&str) -> bool) -> Result<Arc<Pipe>, String> {
    if !def.has_names() {
        return Ok(def.body.clone());
    }
    let mut s = Subst::new(&def.params, args, false, def.inline, open);
    let input = match (&def.input, def.inline) {
        (Some(g), true) => {
            static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
            let fresh = format!("{g}#{}", NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
            s.owned.push((g.clone(), fresh.clone()));
            Some(fresh)
        }
        _ => None,
    };
    let body = s.pipe(&def.body)?;
    Ok(Arc::new(match input {
        // The input of an `@inline` call is bound under a name of its own in the caller's group
        // variables.
        Some(g) => {
            let save = Pipe::app("save", vec![Pipe::Name(g)]);
            match body {
                Pipe::Seq(ps) if def.flat => Pipe::Seq(std::iter::once(save).chain(ps).collect()),
                b => Pipe::Seq(vec![save, b]),
            }
        }
        None => body,
    }))
}

/// The arguments of a call put in place of the parameters in a body.
struct Subst<'s> {
    /// Each name parameter and its argument.
    names: Vec<(&'s str, &'s str)>,
    /// More of them, made for the call.
    owned: Vec<(String, String)>,
    /// By parameter position, the pipeline arguments put in place (`@inline`).
    pipes: Vec<Option<&'s Pipe>>,
    /// Whether a name is a parameter of a function still being read: a switch name only when
    /// that function is called.
    open: &'s dyn Fn(&str) -> bool,
}

impl<'s> Subst<'s> {
    /// `groups`: the group arguments are put in place by name too, in a body that shares the
    /// caller's group variables.
    fn new(params: &'s [Param], args: &'s [Pipe], pipes: bool, groups: bool, open: &'s dyn Fn(&str) -> bool) -> Subst<'s> {
        let mut s = Subst { names: Vec::new(), owned: Vec::new(), pipes: Vec::new(), open };
        for (p, a) in params.iter().zip(args) {
            match (&p.ty, a) {
                (Ty::Name, Pipe::Name(n)) => s.names.push((&p.name, n)),
                (Ty::Group, Pipe::Var(Slot::Local(n, Holds::Group))) if groups => s.names.push((&p.name, n)),
                (t, q) if t.is_step() => {
                    s.pipes.push(pipes.then_some(q));
                    continue;
                }
                _ => {}
            }
            s.pipes.push(None);
        }
        s
    }

    fn name(&self, n: &str) -> String {
        match self.owned.iter().find(|(p, _)| p == n) {
            Some((_, a)) => a.clone(),
            None => self.names.iter().find(|(p, _)| *p == n).map_or(n, |(_, a)| a).to_string(),
        }
    }

    fn switch<'n>(&'n self, n: &'n str, f: &str) -> Result<&'n str, String> {
        match self.names.iter().find(|(p, _)| *p == n) {
            None => Ok(n),
            Some((_, a)) if (self.open)(a) => Ok(a),
            Some((_, a)) => host::switch(a).ok_or_else(|| {
                let known = INNER.iter().chain(&host::FLAGS).copied().collect::<Vec<_>>().join(",");
                format!("unknown {f} name {a} (the argument for {n}); known: {known}")
            }),
        }
    }

    fn pipe(&self, p: &Pipe) -> Result<Pipe, String> {
        let all = |ps: &[Pipe]| ps.iter().map(|q| self.pipe(q)).collect::<Result<Vec<_>, String>>();
        Ok(match p {
            Pipe::Name(n) => Pipe::Name(self.name(n)),
            Pipe::Var(Slot::Local(n, Holds::Group)) => group(self.name(n)),
            Pipe::Var(Slot::Param(i, _)) => self.pipes.get(*i).copied().flatten().map_or_else(|| p.clone(), Pipe::clone),
            Pipe::App(f @ (Fun::Builtin(_) | Fun::Op(..)), args) => Pipe::App(f.clone(), all(args)?.into()),
            Pipe::App(Fun::Def(c), args) if args.len() < c.def.params.len() => p.clone(),
            Pipe::App(Fun::Def(c), args) => self.call(c, args)?,
            Pipe::Seq(ps) => Pipe::Seq(all(ps)?),
            Pipe::Expanded(m) => match m.switch_names() {
                Some((on, ns)) => Expanded::switches(on, &ns.into_iter().map(|n| self.switch(n, m.head)).collect::<Result<Vec<_>, _>>()?),
                None => smallest(self.pipe(&m.args[0])?),
            },
            Pipe::Bind(Slot::Local(n, Holds::Group), q) => Pipe::Bind(Slot::Local(self.name(n), Holds::Group), Arc::new(self.pipe(q)?)),
            Pipe::Bind(x, q) => Pipe::Bind(x.clone(), Arc::new(self.pipe(q)?)),
            Pipe::Num(_) | Pipe::Text(_) | Pipe::Var(_) => p.clone(),
        })
    }

    fn call(&self, c: &Call, given: &[Pipe]) -> Result<Pipe, String> {
        let args = given.iter().map(|a| self.pipe(a)).collect::<Result<Vec<_>, String>>()?;
        let renamed = c.def.inline && c.def.input.is_some() || args.iter().zip(given).any(|(a, b)| matches!((a, b), (Pipe::Name(x), Pipe::Name(y)) if x != y));
        let body = if renamed { instance(&c.def, &args, self.open)? } else { c.body.clone() };
        Ok(Pipe::App(Fun::Def(Arc::new(Call { def: c.def.clone(), body })), args.into()))
    }
}

/// Whether the expression `e` runs steps: a pipeline other than a group value inside it.
pub fn has_steps(e: &Pipe) -> bool {
    let group = |p: &Pipe| matches!(p, Pipe::Var(Slot::Local(_, Holds::Group)));
    match e {
        Pipe::Seq(ps) => !matches!(&ps[..ps.len() - 1], [g] if group(g)) || has_steps(&ps[ps.len() - 1]),
        Pipe::App(f, args) => args.iter().enumerate().any(|(i, a)| match f.param_ty(args, i) {
            Some(t) if !t.is_step() => has_steps(a),
            _ if a.picks() => has_steps(a),
            _ => !group(a),
        }),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::parser::parse_with;
    use crate::passes::Passes;

    #[test]
    fn a_def_call_is_an_application() {
        let p = Passes::parse("(def (f n:num) n + 1) (def (g p) p | rewrite) prepass=(if (f 2) (g tfunc))").unwrap();
        let Pipe::App(Fun::Builtin(b), args) = &p.prepass else { panic!("{:?}", p.prepass) };
        assert_eq!(b.name, "if");
        let Some((f, [two])) = args[0].call() else { panic!("{:?}", args[0]) };
        assert_eq!((f.def.name.as_str(), two), ("f", &Pipe::Num(2)));
        let Some((g, [tfunc])) = args[1].call() else { panic!("{:?}", args[1]) };
        assert_eq!((g.def.name.as_str(), show(tfunc).as_str()), ("g", "tfunc"));
        assert_eq!(show(&p.prepass), "(if (f 2) (g tfunc))");
    }

    #[test]
    fn let_is_def_inline() {
        let mut defs = Defs::new();
        for item in ["(let a relate | tfunc)", "(let b (relate | tfunc))"] {
            let d = parse_definition(item, &defs, &mut Vec::new()).unwrap();
            defs.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: d.params, def: None });
        }
        let mut inline = Defs::new();
        for item in ["(def @inline (a) relate | tfunc)", "(def @inline (b) (relate | tfunc))"] {
            let d = parse_definition(item, &inline, &mut Vec::new()).unwrap();
            assert_eq!(d.kind, DefKind::Inline);
            inline.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: d.params, def: None });
        }
        for p in ["lowbits | a | b | finish", "(best 1 a b)"] {
            let read = |defs: &Defs| parse_with(p, defs, &mut Vec::new()).unwrap();
            assert_eq!(read(&defs), read(&inline), "{p}");
        }
        assert_eq!(show(&parse_with("lowbits | a | b", &inline, &mut Vec::new()).unwrap()), "lowbits | relate | tfunc | (relate | tfunc)");
    }
}
