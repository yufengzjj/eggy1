//! Definitions: `(let NAME p)` and `(def ...)`, the functions they define, the types of their
//! parameters inferred from the body, and their calls with the arguments put in place.

use super::ast::{Expanded, Fun, Holds, Pipe, Slot, WIDTH, piped, pretty_at, show, show_expr, starts_with_value};
use super::builtins::{MACROS, get, resolve};
use super::host::{self, INNER};
use super::lexer::{Tok, lex};
use super::macros::smallest;
use super::infer::ParamUse;
use super::parser::{Arg, Parser, explicit, group, hyphen_hint, number_seq, seq_of};
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
    /// The last parameter when it is the group the body starts from (`(def (f p g) g | ...)`),
    /// bound to the step's group; `None` where the body runs on the input as it is (the input
    /// left implicit) or reads no group input.
    pub input: Option<String>,
    /// A call takes the step's input: the body does not start with a value, or starts from
    /// `input`, or is an expression that reads the input.
    pub step: bool,
    /// The body when it gives a number: a call gives a number (`body` is then a `filter` of
    /// it, for the checks).
    pub value: Option<Pipe>,
    /// `value` runs steps (`lowbits | size`), so a call is a run of its own.
    pub steps: bool,
    /// The input `value` reads where it is not written, so that a call takes it implicitly
    /// (`(def (under k) size <= k)`).
    pub implicit: Option<super::types::Ty>,
    /// `@timed`: a call past the time limit is skipped and gives its input.
    pub timed: bool,
    /// The position in `Passes::defs`, which a later definition of the name takes over; a call
    /// of one that is not `inline` runs the definition there when it runs.
    pub slot: Option<usize>,
}

impl Def {
    /// Whether a call runs the definition at `slot` when it runs, not the one it was read with.
    pub fn late(&self) -> bool {
        self.slot.is_some() && !self.inline
    }

    /// Whether a run of its body alone is a call: no parameters, no input, candidates.
    pub fn bare(&self) -> bool {
        self.params.is_empty() && self.input.is_none() && self.value.is_none()
    }

    /// Whether a parameter is a name, which a call puts in place in its own copy of the body;
    /// a group parameter too in an `inline` one, which shares the caller's group variables.
    pub fn has_names(&self) -> bool {
        self.params.iter().any(|p| p.ty == super::types::Ty::Name || p.ty == super::types::Ty::Group && self.inline) || self.inline && self.input.is_some()
    }

    /// The group variables bound when the body starts: the group parameters and the input.
    pub fn bound(&self) -> Vec<String> {
        let groups = self.params.iter().filter(|p| matches!(p.ty, super::types::Ty::Group | super::types::Ty::Term)).map(|p| p.name.clone());
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
/// binds it under a name of its own for each call); the `App` compares the arguments. A late
/// call runs the definition at its place.
impl PartialEq for Call {
    fn eq(&self, o: &Call) -> bool {
        match self.def.late() && o.def.late() {
            true => self.def.slot == o.def.slot && self.def.name == o.def.name,
            false => self.def == o.def,
        }
    }
}

impl Call {
    /// The call as the definition at its place in `defs` makes it, `args` its arguments.
    pub fn latest(self: &Arc<Call>, args: &[Pipe], defs: &[Arc<Def>]) -> Arc<Call> {
        let d = self.latest_def(defs);
        if Arc::ptr_eq(d, &self.def) {
            return self.clone();
        }
        let body = instance(d, args, &|_| false).unwrap_or_else(|e| unreachable!("a definition with the same signature takes the same names: {e}"));
        Arc::new(Call { def: d.clone(), body })
    }

    /// The definition the call runs: the one at its place in `defs`.
    pub fn latest_def<'d>(&'d self, defs: &'d [Arc<Def>]) -> &'d Arc<Def> {
        match self.def.slot.filter(|_| !self.def.inline).and_then(|i| defs.get(i)) {
            Some(d) if d.name == self.def.name => d,
            _ => &self.def,
        }
    }

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
    /// For an `@inline` function put in place whose body starts from its last parameter, a
    /// group: that parameter, which a call gives or leaves to the step's input (`main`).
    pub input: Option<String>,
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
    /// The last parameter when it is the group input, not among `params`.
    pub input: Option<String>,
    /// A call takes the step's input.
    pub step: bool,
    /// The body when it gives a number.
    pub value: Option<Pipe>,
    /// The input a body that gives a number reads where it is not written (`size <= k`), so
    /// that the function takes it implicitly.
    pub implicit: Option<Ty>,
    /// `@timed`.
    pub timed: bool,
    /// Warnings of reading it.
    pub notes: Vec<String>,
}

impl<'a> Parser<'a> {
    /// The signature of the function `n` defined.
    pub(crate) fn sig_named(&self, n: &str) -> Sig {
        let d = &self.defs[n];
        let mut sig = d.def.as_ref().map_or_else(|| def_sig(n, &d.params), |d| sig_of(d));
        if d.input.is_some() && d.pipe.picks() {
            sig.result = Ty::MaybeTerm;
        }
        sig
    }

    /// A call of the function `n` defined with parameters, after its name: a call of a
    /// `def` with the name arguments in place in its body, or an `@inline` body with all
    /// arguments in place.
    pub(crate) fn def_call(&mut self, n: &str) -> Result<Pipe, String> {
        let d = self.defs[n].clone();
        let sig = self.sig_named(n);
        // `(main NAME)` reads NAME as a group variable, also one nothing binds, for the checks to
        // report.
        if let (Some(_), true, Some(Tok::Name(g)), Some(Tok::Close)) = (&d.input, d.params.is_empty(), self.peek().cloned(), self.toks.get(self.at + 1))
            && !self.defs.contains_key(&g)
        {
            self.at += 1;
            self.group_name(&g)?;
            self.used.push(n.to_string());
            return self.call_of(n, Vec::new(), Some(group(g)));
        }
        let takes_input = d.input.is_some() || d.def.as_ref().is_some_and(|d| d.input.is_some());
        if d.params.is_empty() && !self.input_ahead(takes_input) {
            return Err(format!("{n} takes {}: {sig}", sig.arity()));
        }
        let reading = def_sig(n, &d.params);
        let args = match d.params.is_empty() && takes_input {
            true => Vec::new(),
            false => self.args(&reading, true).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()).replace(&format!("{n} takes {}", reading.arity()), &format!("{n} takes {}", sig.arity())))?,
        };
        let input = self.group_input(!d.params.is_empty() || takes_input)?;
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
                Ok(Pipe::Expanded(Box::new(Expanded { head: intern(n), args: args.into_iter().chain(input).collect(), steps, scoped: false, timed: false })))
            }
        }
    }

    /// The arguments of a call of the function `n` defined whose body is an expression, after
    /// its name, and its input when written.
    pub(crate) fn number_def_call(&mut self, n: &str) -> Result<Pipe, String> {
        let d = self.defs[n].clone();
        let sig = self.sig_named(n);
        let reading = def_sig(n, &d.params);
        let args = self.args(&reading, true).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()).replace(&format!("{n} takes {}", reading.arity()), &format!("{n} takes {}", sig.arity())))?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        let input = match step {
            true => self.group_input(!d.params.is_empty())?,
            false => None,
        };
        self.used.push(n.to_string());
        let Pipe::App(f, args) = self.call_of(n, args, None)? else { unreachable!("a function whose body is an expression is a def") };
        Ok(Pipe::App(f, args.iter().cloned().chain(input).collect()))
    }
}

/// `n` as a name that lives as long as the program.
fn intern(n: &str) -> &'static str {
    static NAMES: std::sync::Mutex<Vec<&'static str>> = std::sync::Mutex::new(Vec::new());
    let mut names = NAMES.lock().unwrap();
    match names.iter().find(|m| **m == n) {
        Some(m) => m,
        None => {
            let m: &'static str = Box::leak(n.to_string().into_boxed_str());
            names.push(m);
            m
        }
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
    sig.timed = d.timed;
    if d.value.is_some() {
        sig.result = Ty::Num;
    }
    if let Some(t) = &d.implicit {
        let name = d.input.clone().unwrap_or_else(|| if *t == Ty::Term { "t".into() } else { "g".into() });
        sig.input = Some(Param { name, ty: t.clone(), rep: Rep::One });
    }
    sig
}

/// Parses a definition item: `(let NAME p)`, `(def @inline (NAME) p)`, which `NAME` then
/// stands for where it is used, or `(def (NAME) p)`, a function called as a run of its own;
/// the names of `defs` it uses are added to `used`. A `def` may define a function `defs` has
/// again; the caller checks the signatures agree.
pub fn parse_definition(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    parse_definition_lexed(s, None, defs, used)
}

/// `parse_definition` of `s` lexed as `toks`, or lexed here when `None`.
pub(crate) fn parse_definition_lexed(s: &str, toks: Option<Vec<Tok>>, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    definition(s, toks, defs, used).map_err(|e| hyphen_hint(e, s))
}

/// The head of a definition item: how it defines its name, the name, the parameters and the
/// types written for them, `@timed`.
pub(crate) struct Head {
    pub(crate) kind: DefKind,
    pub(crate) name: String,
    params: Vec<String>,
    types: Vec<Option<Ty>>,
    timed: bool,
}

fn head(p: &mut Parser, s: &str) -> Result<Head, String> {
    p.expect(Tok::Open, "(let or (def")?;
    let head = p.name("let or def")?;
    let mut params: Vec<String> = Vec::new();
    let mut types: Vec<Option<Ty>> = Vec::new();
    let mut timed = false;
    let (kind, name) = match head.as_str() {
        "let" => (DefKind::Let, p.name("a name after let")?),
        "def" => {
            let mut kind = DefKind::Run;
            while p.peek() == Some(&Tok::At) {
                p.at += 1;
                match p.name("an attribute after @")?.as_str() {
                    "inline" => kind = DefKind::Inline,
                    "timed" => timed = true,
                    a => return Err(format!("unknown attribute @{a} of def; known: @inline @timed")),
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
                        Ok(ty) if !matches!(ty, Ty::MaybeTerm | Ty::Text | Ty::Any) => Some(ty),
                        _ => return Err(format!("unknown type {t} of parameter {n}; known: pipe group term num name, and A->B as in term->num")),
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
    Ok(Head { kind, name, params, types, timed })
}

/// The head of the definition item `item` lexed as `toks`, when it is one.
pub(crate) fn head_of(toks: &[Tok], item: &str) -> Option<Head> {
    // `head` reads no further than the first `)`.
    let end = toks.iter().position(|t| *t == Tok::Close).map_or(toks.len(), |i| i + 1);
    head(&mut Parser::new(toks[..end].to_vec(), &Defs::new()), item).ok()
}

/// The function a `(def ...)` item declares by its head alone, at `slot`, for the calls read
/// before its body: one that gives candidates, as a step. `None` for a `let`, an `@inline`
/// one and one with a parameter without a type.
pub(crate) fn declared(h: &Head, slot: usize) -> Option<Def> {
    if h.kind != DefKind::Run || h.types.iter().any(|t| t.is_none() || *t == Some(Ty::Term)) {
        return None;
    }
    let params: Vec<Param> = h.params.iter().zip(&h.types).map(|(n, t)| Param { name: n.clone(), ty: t.clone().unwrap(), rep: Rep::One }).collect();
    Some(Def { name: h.name.clone(), params, body: Arc::new(Pipe::id()), inline: false, flat: false, input: None, step: true, steps: false, value: None, implicit: None, timed: h.timed, slot: Some(slot) })
}

fn definition(s: &str, toks: Option<Vec<Tok>>, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    let mut p = Parser::new(toks.map_or_else(|| lex(s), Ok)?, defs);
    let Head { mut kind, name, params, types, timed } = head(&mut p, s)?;
    let head: String = std::iter::once(name.as_str()).chain(params.iter().map(String::as_str)).collect::<Vec<_>>().join(" ");
    let what = match kind {
        DefKind::Let => format!("let {name}"),
        DefKind::Inline => format!("def @inline ({head})"),
        DefKind::Run => format!("def ({head})"),
    };
    let function = get(&name);
    if function.is_some_and(|s| !s.is_number()) || resolve(&name).is_some() || MACROS.contains(&name.as_str()) || name == "extern" || name == "def" {
        return Err(format!("{what}: the name of a pass, form or macro"));
    }
    if var_index(&name).is_some() || function.is_some() || name == "none" {
        return Err(format!("{what}: the name of a variable or function"));
    }
    match defs.get(&name) {
        Some(d) if d.run && kind != DefKind::Run => return Err(format!("{what}: {name} is already a function (def ({name}) ...), which only a def defines again")),
        Some(d) if !d.run && kind == DefKind::Run => return Err(format!("{what}: {name} is already defined by let or def @inline")),
        _ => {}
    }
    for (i, n) in params.iter().enumerate() {
        let taken = var_index(n).is_some() || get(n).is_some() || MACROS.contains(&n.as_str()) || resolve(n).is_some() || defs.contains_key(n);
        if taken || ["none", "def", "let", "extern"].contains(&n.as_str()) {
            return Err(format!("{what}: parameter {n} is the name of a variable, function or definition"));
        }
        if *n == name || params[..i].contains(n) {
            return Err(format!("{what}: parameter {n} is written twice"));
        }
    }
    p.params = params.into_iter().zip(types).map(|(name, ty)| ParamUse { name, annotated: ty.is_some(), ty, uses: 0 }).collect();
    // A definition of a function that gives a group again reads a pipeline of them.
    let candidates = defs.get(&name).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_none());
    let start = p.at;
    let mut value = match kind != DefKind::Let && !candidates && p.expr_ahead() {
        true => {
            let e = p.or()?;
            kind = DefKind::Run;
            Some(e)
        }
        false => None,
    };
    if value.is_some() && p.peek() == Some(&Tok::Bar) {
        // Read again as a pipeline, whose error names the number before `|`.
        p.at = start;
        p.pipe()?;
    }
    let implicit = value.as_ref().and_then(|e| p.input_ty(e));
    let lead = value.is_none() && matches!((p.peek(), p.params.last()), (Some(Tok::Name(n)), Some(u)) if *n == u.name && matches!(u.ty, None | Some(Ty::Term | Ty::Group))) && matches!(p.toks.get(p.at + 1), Some(Tok::Bar | Tok::Close));
    let (mut pipe, flat, tail, lead) = match value {
        Some(_) => (Pipe::id(), false, None, None),
        None if lead => {
            let g = p.name("a parameter")?;
            p.count_param(&g);
            let first = vec![group(g.clone())];
            let (stages, tail) = if p.peek() == Some(&Tok::Close) { (first, None) } else { p.stages_after(first)? };
            if let (true, Some(e)) = (candidates, &tail) {
                return Err(format!("{} | {} gives a number, not a group: a pipeline that ends in a number goes where a number does, as in x = (a | size)", show(&seq_of(stages)), show_expr(e, 1)));
            }
            let flat = !candidates && kind != DefKind::Run && stages.len() > 1;
            (seq_of(stages), flat, tail, Some(g))
        }
        None if candidates => (p.pipe()?, false, None, None),
        None => {
            let (stages, tail) = p.stages_of_pipe()?;
            let flat = kind != DefKind::Run && stages.len() > 1;
            (seq_of(stages), flat, tail, None)
        }
    };
    p.expect(Tok::Close, ")")?;
    p.end()?;
    let whole = tail.as_ref().map(|e| number_seq(pipe.clone(), e.clone()));
    let body = match (&value, &whole) {
        (Some(v), _) => (None, Some(v)),
        (None, Some(w)) => (None, Some(w)),
        (None, None) => (Some(&pipe), None),
    };
    super::infer::solve(&mut p.params, &what, &name, body.0, body.1, implicit == Some(Ty::Term), lead.as_deref())?;
    let starts = starts_with_value(&pipe);
    // The last parameter is the input where it is a group the body starts from or reads.
    let input = match p.params.last() {
        Some(u) if (value.is_some() || starts) && u.ty == Some(Ty::Group) || lead.is_some() => Some(u.name.clone()),
        _ => None,
    };
    let implicit = match p.params.last().and_then(|u| u.ty.clone()) {
        Some(Ty::Term) if lead.is_some() => Some(Ty::Term),
        _ => implicit.filter(|_| input.is_none()),
    };
    let step = input.is_some() || value.is_none() && !starts || implicit.is_some();
    if let Some(e) = tail {
        if kind != DefKind::Run {
            return Err(format!("{what}: a function that gives a number is a run of its own, so it cannot be @inline or a let"));
        }
        value = Some(number_seq(std::mem::replace(&mut pipe, Pipe::id()), e));
    }
    if timed && value.is_some() {
        return Err(format!("{what}: @timed is for a function that gives a group, which a call past the time limit skips"));
    }
    let mut params = std::mem::take(&mut p.params);
    if input.is_some() {
        params.pop();
    }
    if kind == DefKind::Inline && params.iter().any(|u| u.ty == Some(Ty::Term)) {
        return Err(format!("{what}: a term parameter is for a def that runs, not @inline"));
    }
    let notes = Vec::new();
    let params: Vec<Param> = params.into_iter().map(|u| Param { name: u.name, ty: u.ty.expect("solve gives every parameter its type"), rep: Rep::One }).collect();
    if kind == DefKind::Run {
        super::flow::body_of(&params, input.as_deref(), implicit.as_ref(), value.as_ref(), &pipe).map_err(|e| format!("{name}: {e}"))?;
    }
    used.extend(p.used);
    Ok(Definition { name, kind, params, pipe, flat, input, step, value, implicit, timed, notes })
}

/// The signature of a function `(def (NAME PARAM ...) p)`: its parameters, then the
/// candidates.
pub fn def_sig(name: &str, params: &[Param]) -> Sig {
    Sig {
        name: name.into(),
        params: params.to_vec(),
        input: Some(Param { name: "g".into(), ty: Ty::Group, rep: Rep::One }),
        result: Ty::Group,
        timed: false,
        uncounted: false,
        switch: false,
        doc: String::new(),
    }
}

fn def_head(d: &Def) -> String {
    // Numbers and names are known from where they are written; the other types are printed so
    // that the text reads back as the same function.
    let params = d.params.iter().map(|p| match &p.ty {
        Ty::Num | Ty::Name => p.name.clone(),
        t => format!("{}:{t}", p.name),
    });
    let input = d.input.as_ref().map(|g| format!("{g}:{}", d.implicit.clone().unwrap_or(Ty::Group)));
    let head = std::iter::once(d.name.clone()).chain(params).chain(input).collect::<Vec<_>>().join(" ");
    let attrs = [(d.inline, "@inline "), (d.timed, "@timed ")];
    let attrs: String = attrs.iter().filter(|(on, _)| *on).map(|(_, a)| *a).collect();
    format!("{attrs}({head})")
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
            Some((_, a)) => host::switch(a).ok_or_else(|| super::warn::unknown(format!("unknown {f} name {a} (the argument for {n})"), a, INNER.iter().chain(&host::FLAGS).copied())),
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
                None if m.is_call() => Pipe::Expanded(Box::new(Expanded { args: all(&m.args)?, steps: all(&m.steps)?, ..(**m).clone() })),
                None => smallest(self.pipe(&m.args[0])?),
            },
            Pipe::Drop(q, e) => Pipe::Drop(Arc::new(self.pipe(q)?), *e),
            Pipe::Bind(Slot::Local(n, Holds::Group), q) => Pipe::Bind(Slot::Local(self.name(n), Holds::Group), Arc::new(self.pipe(q)?)),
            Pipe::Bind(x, q) => Pipe::Bind(x.clone(), Arc::new(self.pipe(q)?)),
            Pipe::FnValue(q) => Pipe::FnValue(Arc::new(self.pipe(q)?)),
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
        let p = Passes::parse("(def (f n:num) n + 1) (def (g p:pipe) p | rewrite) prepass=(if (f 2) (g tfunc))").unwrap();
        let Pipe::App(Fun::Builtin(b), args) = &p.prepass() else { panic!("{:?}", p.prepass()) };
        assert_eq!(b.name, "if");
        let Some((f, [two])) = args[0].call() else { panic!("{:?}", args[0]) };
        assert_eq!((f.def.name.as_str(), two), ("f", &Pipe::Num(2)));
        let Some((g, [tfunc])) = args[1].call() else { panic!("{:?}", args[1]) };
        assert_eq!((g.def.name.as_str(), show(tfunc).as_str()), ("g", "tfunc"));
        assert_eq!(show(&p.prepass()), "(if (f 2) (g tfunc))");
    }

    #[test]
    fn a_definition_read_alone_checks_what_its_steps_take() {
        let e = parse_definition("(def (f k:num) (if (size <= k) lowbits))", &Defs::new(), &mut Vec::new()).err().unwrap();
        assert!(e.starts_with("f: size takes t:term? and gives num; its input here is a group"), "{e}");
    }

    #[test]
    fn let_is_def_inline() {
        let mut defs = Defs::new();
        for item in ["(let a unshift | tfunc)", "(let b (unshift | tfunc))"] {
            let d = parse_definition(item, &defs, &mut Vec::new()).unwrap();
            defs.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: d.params, def: None, input: None });
        }
        let mut inline = Defs::new();
        for item in ["(def @inline (a) unshift | tfunc)", "(def @inline (b) (unshift | tfunc))"] {
            let d = parse_definition(item, &inline, &mut Vec::new()).unwrap();
            assert_eq!(d.kind, DefKind::Inline);
            inline.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: d.params, def: None, input: None });
        }
        for p in ["lowbits | a | b | shifted_xor", "(best 1 a b)"] {
            let read = |defs: &Defs| parse_with(p, defs, &mut Vec::new()).unwrap();
            assert_eq!(read(&defs), read(&inline), "{p}");
        }
        assert_eq!(show(&parse_with("lowbits | a | b", &inline, &mut Vec::new()).unwrap()), "lowbits | unshift | tfunc | (unshift | tfunc)");
    }
}
