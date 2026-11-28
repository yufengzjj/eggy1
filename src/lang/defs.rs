//! Definitions: `(let NAME p)` and `(def ...)`, the functions they define, the types of their
//! parameters inferred from the body, and their calls with the arguments put in place.

use super::ast::{Expanded, Fun, Holds, Pipe, Slot, WIDTH, piped, pretty_at, show, show_expr, starts_with_value, value_ty};
use super::builtins::{MACROS, get, resolve};
use super::elab::{Elab, Items, Stages, group, hyphen_hint, number_seq, seq_of};
use super::host::{self, INNER};
use super::infer::ParamUse;
use super::lexer::{Tok, lex};
use super::macros::smallest;
use super::syntax::{DefItem, Head, Node};
use super::tuples::fill;
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
    /// The type of the tuple the body gives (`body` then is that tuple or a pipeline that ends
    /// in one); `None` for a function that gives a group or a number.
    pub tuple: Option<super::types::Ty>,
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
        self.params.is_empty() && self.input.is_none() && self.value.is_none() && self.tuple.is_none()
    }

    /// Whether a parameter is a name, which a call puts in place in its own copy of the body;
    /// a group parameter too in an `inline` one, which shares the caller's group variables.
    pub fn has_names(&self) -> bool {
        self.params.iter().any(|p| p.ty == super::types::Ty::Name || p.ty == super::types::Ty::Group && self.inline) || self.inline && self.input.is_some()
    }

    /// The group variables bound when the body starts: the group parameters and the input.
    pub fn bound(&self) -> Vec<String> {
        let groups = self.params.iter().filter(|p| matches!(p.ty, super::types::Ty::Group | super::types::Ty::Term | super::types::Ty::Tuple(_))).map(|p| p.name.clone());
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
    /// The type of the tuple the body gives.
    pub tuple: Option<Ty>,
    /// `@timed`.
    pub timed: bool,
    /// Warnings of reading it.
    pub notes: Vec<String>,
}

/// `n` as a name that lives as long as the program.
pub(crate) fn intern(n: &str) -> &'static str {
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
    if let Some(t) = &d.tuple {
        sig.result = t.clone();
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
    definition(s, None, defs, used)
}

/// The function a `(def ...)` item declares by its head alone, at `slot`, for the calls read
/// before its body: one that gives candidates, as a step. `None` for a `let`, an `@inline`
/// one and one with a parameter without a type.
pub(crate) fn declared(h: &Head, slot: usize) -> Option<Def> {
    if h.kind != DefKind::Run || h.types.iter().any(|t| t.is_none() || *t == Some(Ty::Term)) {
        return None;
    }
    let params: Vec<Param> = h.params.iter().zip(&h.types).map(|(n, t)| Param { name: n.clone(), ty: t.clone().unwrap(), rep: Rep::One }).collect();
    Some(Def { name: h.name.clone(), params, body: Arc::new(Pipe::id()), inline: false, flat: false, input: None, step: true, steps: false, value: None, implicit: None, tuple: None, timed: h.timed, slot: Some(slot) })
}

/// The definition item `s`, lexed as `toks` or here when `None`; the names of `defs` it uses
/// are added to `used`. A `def` may define a function `defs` has again; the caller checks the
/// signatures agree.
pub(crate) fn definition(s: &str, toks: Option<&[Tok]>, defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    let mut go = || {
        let lexed;
        let toks = match toks {
            Some(t) => t,
            None => {
                lexed = lex(s)?;
                &lexed
            }
        };
        let item = super::reader::definition(toks, s)?;
        elaborate(&item, toks, defs, used)
    };
    go().map_err(|e| hyphen_hint(e, s))
}

impl<'a> Elab<'a> {
    /// A call of the `def` `n` in parentheses, its arguments in `c`, and nothing after them.
    pub(crate) fn def_call_in(&mut self, n: &str, c: &mut Items) -> Result<Pipe, String> {
        let p = self.inside(|e| e.def_call(n, c))?;
        self.close(c)?;
        Ok(p)
    }
}

fn elaborate(item: &DefItem, toks: &[Tok], defs: &Defs, used: &mut Vec<String>) -> Result<Definition, String> {
    let Head { kind, name, params, types, timed } = &item.head;
    let (mut kind, name, timed) = (*kind, name.clone(), *timed);
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
    let mut p = Elab::new(toks, defs);
    p.params = params.iter().zip(types).map(|(name, ty)| ParamUse { name: name.clone(), annotated: ty.is_some(), ty: ty.clone(), uses: 0 }).collect();
    // A definition of a function that gives a group again reads a pipeline of them.
    let candidates = defs.get(&name).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_none());
    let ss = Stages::of(&item.body);
    let x = &ss.at(0)[0];
    let single = ss.len() == 1 && ss.at(0).len() == 1;
    let read = (|| -> Result<_, String> {
        let indexed = match single {
            true => p.tuple_index(x)?,
            false => None,
        };
        let (value, indexed) = match indexed {
            Some((e, Ty::Num)) if kind != DefKind::Let && !candidates => (Some(e), None),
            Some(i) => (None, Some(i)),
            None if kind != DefKind::Let && !candidates && single && p.value_body(x) => (Some(p.expr(x)?), None),
            None => (None, None),
        };
        if value.is_some() {
            kind = DefKind::Run;
        }
        let implicit = value.as_ref().and_then(|e| p.input_ty(e));
        let lead = value.is_none() && ss.at(0).len() == 1 && matches!((&x.node, p.params.last()), (Node::Name(n), Some(u)) if *n == u.name && matches!(u.ty, None | Some(Ty::Term | Ty::Group)));
        let (pipe, flat, tail, lead) = match (value.as_ref(), indexed) {
            (Some(_), _) => (Pipe::id(), false, None, None),
            (None, Some((e, t))) => (p.index_step(e, t)?, false, None, None),
            _ => match () {
            () if lead => {
                let g = x.name().unwrap().to_string();
                p.count_param(&g);
                let first = vec![group(g.clone())];
                let (stages, tail) = if ss.len() == 1 { (first, None) } else { p.stages(ss.from(1), first)? };
                if let (true, Some(e)) = (candidates, &tail) {
                    return Err(format!("{} | {} gives a number, not a group: a pipeline that ends in a number goes where a number does, as in x = (a | size)", super::ast::show(&seq_of(stages)), super::ast::show_expr(e, 1)));
                }
                let flat = !candidates && kind != DefKind::Run && stages.len() > 1;
                (seq_of(stages), flat, tail, Some(g))
            }
            () if candidates => (p.pipe(ss)?, false, None, None),
            () => {
                let (stages, tail) = p.stages(ss, Vec::new())?;
                let flat = kind != DefKind::Run && stages.len() > 1;
                (seq_of(stages), flat, tail, None)
            }
            },
        };
        let whole = tail.as_ref().map(|e| number_seq(pipe.clone(), e.clone()));
        let body = match (&value, &whole) {
            (Some(v), _) => (None, Some(v)),
            (None, Some(w)) => (None, Some(w)),
            (None, None) => (Some(&pipe), None),
        };
        super::infer::solve(&mut p.params, &what, &name, body.0, body.1, implicit == Some(Ty::Term), lead.as_deref())?;
        Ok((pipe, flat, tail, lead, value, implicit))
    })();
    // A parameter written alone in a position of a tuple gives the tuple its type, which its
    // other uses infer.
    let holes = std::mem::take(&mut p.holes);
    if let Some(n) = holes.iter().find(|n| p.param(n).is_none_or(|i| p.params[i].ty.is_none())) {
        return Err(format!("{what}: cannot infer the type of {n} in {name}: write {n}:TYPE"));
    }
    let (mut pipe, flat, mut tail, lead, mut value, implicit) = read?;
    if !holes.is_empty() {
        let mut bound = Vec::new();
        pipe = fill(&pipe, &p.params, &mut bound);
        tail = tail.map(|e| fill(&e, &p.params, &mut bound));
        value = value.map(|e| fill(&e, &p.params, &mut bound));
        if let Some(ty) = value_ty(&pipe) {
            check_tuple(&ty)?;
        }
    }
    let tuple = value_ty(&pipe).filter(|t| value.is_none() && tail.is_none() && t.positions().is_some());
    if tuple.is_some() && kind != DefKind::Run {
        return Err(format!("{what}: a function that gives a tuple is a run of its own, so it cannot be @inline or a let"));
    }
    let implicit = match &tuple {
        Some(_) => p.tuple_reads(&pipe).then_some(Ty::Group),
        None => implicit,
    };
    let starts = starts_with_value(&pipe);
    // The last parameter is the input where it is a group the body starts from or reads.
    let input = match p.params.last() {
        Some(u) if (value.is_some() || tuple.is_some() || starts) && u.ty == Some(Ty::Group) || lead.is_some() => Some(u.name.clone()),
        _ => None,
    };
    let implicit = match p.params.last().and_then(|u| u.ty.clone()) {
        Some(Ty::Term) if lead.is_some() => Some(Ty::Term),
        _ => implicit.filter(|_| input.is_none()),
    };
    let step = input.is_some() || value.is_none() && tuple.is_none() && !starts || implicit.is_some();
    if let Some(e) = tail {
        if kind != DefKind::Run {
            return Err(format!("{what}: a function that gives a number is a run of its own, so it cannot be @inline or a let"));
        }
        value = Some(number_seq(std::mem::replace(&mut pipe, Pipe::id()), e));
    }
    // A call skipped past the time limit gives what it takes: its group input, or the tuple
    // its last parameter takes.
    let takes_tuple = tuple.is_some() && p.params.last().and_then(|u| u.ty.as_ref()) == tuple.as_ref();
    if timed && (value.is_some() || tuple.is_some() && !takes_tuple) {
        return Err(format!("{what}: @timed is for a function that gives what it takes, which a call past the time limit gives instead: a group, or the tuple its last parameter takes"));
    }
    let mut params = std::mem::take(&mut p.params);
    if input.is_some() {
        params.pop();
    }
    if kind == DefKind::Inline && params.iter().any(|u| u.ty == Some(Ty::Term)) {
        return Err(format!("{what}: a term parameter is for a def that runs, not @inline"));
    }
    if kind == DefKind::Inline && params.iter().any(|u| u.ty.as_ref().is_some_and(|t| t.positions().is_some())) {
        return Err(format!("{what}: a tuple parameter is for a def that runs, not @inline"));
    }
    let params: Vec<Param> = params.into_iter().map(|u| Param { name: u.name, ty: u.ty.expect("solve gives every parameter its type"), rep: Rep::One }).collect();
    if kind == DefKind::Run {
        super::flow::body_of(&params, input.as_deref(), implicit.as_ref(), value.as_ref(), &pipe).map_err(|e| format!("{name}: {e}"))?;
    }
    used.extend(p.used);
    Ok(Definition { name, kind, params, pipe, flat, input, step, value, implicit, tuple, timed, notes: Vec::new() })
}

/// An error for a tuple type with a position that holds no value a tuple holds.
fn check_tuple(t: &Ty) -> Result<(), String> {
    match t.positions() {
        Some(ts) => {
            ts.iter().try_for_each(check_tuple)?;
            Ty::tuple(ts.to_vec()).map(|_| ())
        }
        None => Ok(()),
    }
}

impl<'a> Elab<'a> {
    /// Whether the body of a definition that is the one item `x` is an expression: it gives
    /// a number where it is a step, or is `none`.
    fn value_body(&self, x: &super::syntax::Syn) -> bool {
        x.name() == Some("none") || self.number_item(x)
    }
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
pub(crate) fn instance(def: &Def, args: &[Pipe], open: &dyn Fn(&str) -> bool) -> Result<Arc<Pipe>, String> {
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
pub(crate) struct Subst<'s> {
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
    pub(crate) fn new(params: &'s [Param], args: &'s [Pipe], pipes: bool, groups: bool, open: &'s dyn Fn(&str) -> bool) -> Subst<'s> {
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

    pub(crate) fn pipe(&self, p: &Pipe) -> Result<Pipe, String> {
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
            Pipe::Tuple(ps) => Pipe::Tuple(ps.iter().map(|(q, t)| Ok((self.pipe(q)?, t.clone()))).collect::<Result<Vec<_>, String>>()?.into()),
            Pipe::Index(q, i) => Pipe::Index(Arc::new(self.pipe(q)?), *i),
            Pipe::Unpack(slots, q) => {
                let slots = slots.iter().map(|x| match x {
                    Slot::Local(n, Holds::Group) => Slot::Local(self.name(n), Holds::Group),
                    x => x.clone(),
                });
                Pipe::Unpack(slots.collect(), Arc::new(self.pipe(q)?))
            }
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
    use crate::lang::elab::parse_with;
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
