//! The built-in functions of the pipeline language: their signatures, declared in
//! `src/builtins.pipe` (`docs/lang-lib/builtins.md`), which the parser reads calls by and the
//! checks read the attributes of; the dispatch table `BUILTINS`, which pairs each with its
//! implementation; and the implementations that do not depend on the simplification: the
//! combinators, the operators, `print` and `assert`.

use super::ast::{Fun, Holds, Pipe, Slot};
use super::eval::{Env, Steps, Value, dedup, go};
use super::host::{self, Cand, Ctx, Error, Fns, Term, count_won, stats};
use super::types::{Kind, Param, Rep, Sig, Ty};
use super::vars::NONE;
use std::collections::HashMap;
use std::sync::LazyLock;

/// The declarations of `text` in order: `(extern [@ATTR ...] (NAME PARAM:TYPE ... INPUT:TYPE)
/// RESULT)`, each after a comment line that describes it.
pub fn parse(text: &str) -> Result<Vec<Sig>, String> {
    let mut out: Vec<Sig> = Vec::new();
    let mut doc: Option<String> = None;
    let mut decl = String::new();
    let mut decl_doc = None;
    for (n, line) in text.lines().enumerate() {
        let at = |e: String| format!("line {}: {e}", n + 1);
        let code = line.split('#').next().unwrap_or("").trim();
        if !decl.is_empty() {
            decl += " ";
            decl += code;
        } else if code.is_empty() {
            doc = line.trim().strip_prefix('#').map(|c| c.trim().to_string());
            continue;
        } else {
            decl = code.to_string();
            decl_doc = doc.take();
        }
        let depth = decl.chars().fold(0i32, |d, c| d + i32::from(c == '(') - i32::from(c == ')'));
        if depth > 0 {
            continue;
        }
        let text = std::mem::take(&mut decl);
        let mut sig = one(&text).map_err(at)?;
        sig.doc = decl_doc.take().filter(|d| !d.is_empty()).ok_or_else(|| at(format!("{} has no description: write one comment line right before it", sig.name)))?;
        if out.iter().any(|s| s.name == sig.name) {
            return Err(at(format!("{} is declared twice", sig.name)));
        }
        out.push(sig);
    }
    if !decl.is_empty() {
        return Err(format!("unclosed declaration: {decl}"));
    }
    Ok(out)
}

fn one(text: &str) -> Result<Sig, String> {
    let toks: Vec<&str> = text.split_inclusive(['(', ')']).flat_map(|s| {
        let (word, paren) = s.split_at(s.len() - usize::from(s.ends_with(['(', ')'])));
        word.split_whitespace().chain((!paren.is_empty()).then_some(paren))
    }).collect();
    let bad = || format!("expected (extern [@ATTR ...] (NAME PARAM:TYPE ... INPUT:TYPE) RESULT): {text}");
    let [open, kw, rest @ ..] = toks.as_slice() else { return Err(bad()) };
    if (*open, *kw) != ("(", "extern") {
        return Err(bad());
    }
    let mut rest = rest.iter().copied().peekable();
    let (mut timed, mut uncounted, mut switch) = (false, false, false);
    while let Some(a) = rest.next_if(|t| t.starts_with('@')) {
        match a {
            "@timed" => timed = true,
            "@uncounted" => uncounted = true,
            "@switch" => switch = true,
            _ => return Err(format!("unknown attribute {a}; known: @timed @uncounted @switch")),
        }
    }
    if uncounted && !timed {
        return Err("@uncounted says how a skip past the time limit counts, so it needs @timed".into());
    }
    if rest.next() != Some("(") {
        return Err(bad());
    }
    let name = rest.next().filter(|n| *n != ")").ok_or_else(bad)?.to_string();
    let mut params = Vec::new();
    loop {
        match rest.next() {
            Some(")") => break,
            Some(p) => params.push(param(p).map_err(|e| format!("{name}: {e}"))?),
            None => return Err(bad()),
        }
    }
    let result = match rest.next().ok_or_else(|| format!("{name}: expected a result type"))? {
        ")" => None,
        r => {
            let r = Ty::parse(r).map_err(|e| format!("{name}: {e}"))?;
            if rest.next() != Some(")") {
                return Err(bad());
            }
            Some(r)
        }
    };
    if rest.next().is_some() {
        return Err(bad());
    }
    let Some(result) = result else {
        if switch || params.iter().any(|p| matches!(p.ty, Ty::Term | Ty::MaybeTerm | Ty::Group)) {
            return Err(format!("{name}: a function without a result has no input and no @switch"));
        }
        return Ok(Sig { name, params, input: None, result: Ty::Nothing, timed, uncounted, switch, doc: String::new() });
    };
    if OPERATORS.contains(&name.as_str()) {
        return operator(name, params, result, timed || uncounted || switch);
    }
    let input = params.pop().ok_or_else(|| format!("{name}: the last parameter is the input, term or group"))?;
    if input.rep != Rep::One || !matches!(input.ty, Ty::Term | Ty::Group) && !(input.ty == Ty::MaybeTerm && matches!(result, Ty::Num | Ty::Text)) && !(input.ty == Ty::Text && result == Ty::Group) {
        return Err(format!("{name}: the input {input} must be term or group, term? for a function that gives a number or a text, or text for one that gives a group"));
    }
    if !matches!(result, Ty::Num | Ty::Term | Ty::MaybeTerm | Ty::Group | Ty::Text) {
        return Err(format!("{name}: a function gives num, term, term?, group or text"));
    }
    if Kind::of(&input.ty, &result).is_none() {
        return Err(format!("{name}: no calling kind takes {} to {}", input.ty, result));
    }
    for (i, p) in params.iter().enumerate() {
        match &p.ty {
            Ty::MaybeTerm if result == Ty::Num => {}
            Ty::Term | Ty::MaybeTerm => return Err(format!("{name}: {p}: only the input is a term, or a term? parameter of a function that gives a number")),
            t @ Ty::Fn(..) if !t.is_function() => return Err(format!("{name}: {p}: a function takes one input, term or group, and gives num, term, term? or group")),
            Ty::Any if p.rep != Rep::Many || i + 1 != params.len() => return Err(format!("{name}: {p}: any is only for a last parameter any...")),
            t if p.rep == Rep::Many && !t.is_pipe() && *t != Ty::Any || p.rep == Rep::Opt && (t.is_expr() || *t == Ty::Text) => return Err(format!("{name}: {p}: only pipe and any take ..., only pipe, group and name take ?")),
            _ => {}
        }
    }
    if switch && !matches!(input.ty, Ty::Term) {
        return Err(format!("{name}: @switch is for a pass over one term"));
    }
    Ok(Sig { name, params, input: Some(input), result, timed, uncounted, switch, doc: String::new() })
}

/// The operators of the language, as the parser reads them.
pub const OPERATORS: [&str; 13] = ["+", "-", "*", "/", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "!"];

/// The declaration of an operator: numbers to a number, no input and no attribute; only the
/// last operand may be `group->num...`, a function of the operator's own input that it
/// calls while the result is still open (`&&`, `||`).
fn operator(name: String, params: Vec<Param>, result: Ty, attrs: bool) -> Result<Sig, String> {
    let lazy = |p: &Param| p.rep == Rep::Many && p.ty == Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Num));
    let n = params.len();
    let operand = |(i, p): (usize, &Param)| p.ty == Ty::Num && p.rep == Rep::One || i + 1 == n && lazy(p);
    if attrs || result != Ty::Num || params.is_empty() || !params.iter().enumerate().all(operand) {
        return Err(format!("{name}: an operator takes numbers to num, without attributes; only its last operand may be group->num..."));
    }
    Ok(Sig { name, params, input: None, result, timed: false, uncounted: false, switch: false, doc: String::new() })
}

pub(crate) fn param(p: &str) -> Result<Param, String> {
    let (name, ty) = p.split_once(':').ok_or_else(|| format!("expected NAME:TYPE, found {p}"))?;
    let (ty, rep) = match (ty.strip_suffix("..."), ty.strip_suffix('?')) {
        (Some(t), _) => (t, Rep::Many),
        (_, Some(t)) if !t.ends_with("term") => (t, Rep::Opt),
        _ => (ty, Rep::One),
    };
    let ty = Ty::parse(ty).map_err(|e| format!("{e}, in {p}"))?;
    Ok(Param { name: name.to_string(), ty, rep })
}

static TABLE: LazyLock<(Vec<Sig>, HashMap<String, usize>)> = LazyLock::new(|| {
    let sigs = parse(include_str!("../builtins.pipe")).unwrap_or_else(|e| panic!("src/builtins.pipe: {e}"));
    let index = sigs.iter().enumerate().map(|(i, s)| (s.name.clone(), i)).collect();
    (sigs, index)
});

/// Every built-in function, in the order of `src/builtins.pipe`.
pub fn all() -> &'static [Sig] {
    &TABLE.0
}

/// The built-in function `name`.
pub fn get(name: &str) -> Option<&'static Sig> {
    TABLE.1.get(name).map(|i| &TABLE.0[*i])
}

/// The position of the built-in function `name` in `all`.
pub fn index(name: &str) -> Option<usize> {
    TABLE.1.get(name).copied()
}

/// The names that expand when parsed instead of naming functions or variables.
pub const MACROS: [&str; 3] = ["let", "on", "off"];

/// The names of the functions a step can call, and of `on` and `off`, for error messages.
pub fn step_names() -> impl Iterator<Item = &'static str> {
    all().iter().filter(|s| !s.is_number()).map(|s| s.name.as_str()).chain(["on", "off"])
}

/// The names of the functions an expression can call, for error messages.
pub fn number_names() -> impl Iterator<Item = &'static str> {
    all().iter().filter(|s| s.is_number() && !s.is_op()).map(|s| s.name.as_str())
}

/// A call of `s` with placeholder arguments: `1`, `x`, `id`; optional ones left out.
#[cfg(test)]
pub(crate) fn sample(s: &Sig) -> String {
    match s.name.as_str() {
        "!" => return "!1".into(),
        _ if s.kind() == Kind::FromText => return format!("({} \"x\")", s.name),
        op if s.is_op() => return format!("(1 {op} 1)"),
        _ => {}
    }
    let args: Vec<&str> = s
        .params
        .iter()
        .filter(|p| p.rep != Rep::Opt)
        .map(|p| match &p.ty {
            t if t.is_expr() => "1",
            t if t.is_pipe() => "id",
            Ty::Text => "\"m\"",
            Ty::Any => "1",
            Ty::MaybeTerm => "(main x)",
            _ => "x",
        })
        .collect();
    if args.is_empty() { s.name.clone() } else { format!("({} {})", s.name, args.join(" ")) }
}

/// How a built-in function runs: the conversion `apply` or `Env::value` makes of the input
/// for its calling kind, and the Rust code it calls.
#[derive(Clone, Copy)]
pub(crate) enum Impl {
    /// Parsed into a form of the tree: `seq` is a sequence, `smallest` a macro.
    Form,
    /// Declared but not implemented, which parsing a call reports.
    Missing,
    /// `group -> group`, with the call's arguments.
    Group(fn(&[Pipe], Vec<Cand>, &Env) -> Steps),
    /// `term -> group`, with the call's arguments: on each element, the result groups joined; a
    /// term given back keeps the origin it came with.
    Join(fn(&[Pipe], &Cand, &Env) -> Steps),
    /// `term -> term` over the tree, with the call's function arguments: on each candidate, an
    /// unchanged result keeping it.
    Each(fn(&Term, &Ctx, &Fns<'_>) -> Option<Term>),
    /// `term -> term?`: on each candidate, no result dropping it; the `State::used` bit its
    /// form sets when kept (`linear_mba::ALTERNATIVES`).
    Alt(fn(&Term, &Ctx, &Fns<'_>) -> Option<Term>, u8),
    /// A polish pass (`term -> term`), as `Each`.
    Polish(fn(&Term, &Ctx, &Fns<'_>) -> Term),
    /// `term -> term` over candidates, with the call's arguments: on each, `None` keeping it; a
    /// term given back keeps the origin it came with.
    EachCand(fn(&[Pipe], &Cand, &Env) -> Option<Cand>),
    /// A number function with arguments, on the list whole.
    Num(fn(&[Pipe], &[Cand], &Env) -> u64),
    /// `term -> num` without arguments: on the one term it is given, 0 for none.
    TermNum(fn(&Cand, &Env) -> u64),
    /// `group -> num` without arguments: on the list whole, 0 for no candidates.
    GroupNum(fn(&[Cand], &Env) -> u64),
    /// `text -> group`: the candidates read from the text.
    FromText(fn(&str, &Env) -> Steps),
    /// `term -> text`: on the one term it is given, the empty text for none.
    TermText(fn(&Cand, &Env) -> String),
    /// An operator; its applications hold it (`Fun::Op`) and `Env::value` evaluates them inline.
    Operator(Operator),
}

/// The operators: `+ - * /` (`arith`), the comparisons, `!`, and `&&`, `||`, which
/// evaluate their operands in turn only until one decides the result.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Operator {
    Arith(char),
    Cmp(Cmp),
    Not,
    And,
    Or,
}

/// A built-in function: its declaration in `src/builtins.pipe` and how it runs.
pub struct Builtin {
    pub name: &'static str,
    pub sig: &'static Sig,
    pub(crate) imp: Impl,
    /// `sig.timed` and `sig.uncounted`, read for every step run.
    pub(crate) timed: bool,
    pub(crate) uncounted: bool,
    /// For a function that gives a number (not an operator), its parameter count: an argument
    /// past them is the input written (`(minimal g)`, `(size (main r))`).
    input_at: Option<usize>,
}

impl Builtin {
    /// The position of the input written in the arguments `args` of a function that gives a
    /// number; `None` where it takes the input of the step.
    pub fn input_at(&self, args: &[Pipe]) -> Option<usize> {
        self.input_at.filter(|n| args.len() > *n)
    }
}

impl PartialEq for Builtin {
    fn eq(&self, o: &Builtin) -> bool {
        std::ptr::eq(self, o)
    }
}

impl std::fmt::Debug for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(self.name)
    }
}

/// Every built-in function, in the order of `src/builtins.pipe`, with its implementation.
pub static BUILTINS: std::sync::LazyLock<Vec<Builtin>> = std::sync::LazyLock::new(|| {
    let imp = |sig: &Sig| implementation(&sig.name).unwrap_or(Impl::Missing);
    super::builtins::all().iter().map(|sig| Builtin { name: sig.name.as_str(), sig, imp: imp(sig), timed: sig.timed, uncounted: sig.uncounted, input_at: (sig.is_number() && !sig.is_op()).then_some(sig.params.len()) }).collect()
});

/// The built-in function `name`.
pub fn builtin(name: &str) -> Option<&'static Builtin> {
    super::builtins::index(name).map(|i| &BUILTINS[i])
}

/// The Rust code of the built-in function `name`: `IMPLS`, or what the simplification
/// implements (`builtin_passes::implementation`).
fn implementation(name: &str) -> Option<Impl> {
    if let Some((_, imp)) = IMPLS.iter().find(|(n, _)| *n == name) {
        return Some(*imp);
    }
    host::implementation(name)
}

/// The built-in functions the language implements, by name.
const IMPLS: &[(&str, Impl)] = &[
    ("seq", Impl::Form),
    ("smallest", Impl::Form),
    ("union", Impl::Group(union)),
    ("best", Impl::Group(best)),
    ("first", Impl::Group(first)),
    ("fix", Impl::Group(fix)),
    ("if", Impl::Group(|a, set, env| go(if env.holds(&a[0], &set) { &a[1] } else { &a[2] }, set, env))),
    ("retry", Impl::Group(retry)),
    ("wins", Impl::Group(wins)),
    ("filter", Impl::Group(|a, set, env| Ok(set.into_iter().filter(|x| env.holds(&a[0], std::slice::from_ref(x))).collect()))),
    ("save", Impl::Group(save)),
    ("clear", Impl::Group(clear)),
    ("note", Impl::Group(note)),
    ("take_min", Impl::Group(take_min)),
    ("id", Impl::Group(|_, set, _| Ok(set))),
    ("none", Impl::Group(|_, _, _| Ok(Vec::new()))),
    ("assert", Impl::Group(assert)),
    ("print", Impl::Group(print)),
    ("same", Impl::Num(|a, set, env| set.first().zip(env.group_of(&a[0], set).first()).is_some_and(|(m, c)| c.same(m)) as u64)),
    ("any", Impl::Num(|a, set, env| set.iter().any(|x| env.holds(&a[0], std::slice::from_ref(x))) as u64)),
    ("all", Impl::Num(|a, set, env| (!set.is_empty() && set.iter().all(|x| env.holds(&a[0], std::slice::from_ref(x)))) as u64)),
    ("moved", Impl::GroupNum(|_, env| env.moved.get() as u64)),
    ("input", Impl::TermNum(|m, env| (m.term() == env.lex.borrow().input) as u64)),
    ("index", Impl::Group(|a, set, env| {
        let i = env.value(&a[0], &set);
        Ok(usize::try_from(i).ok().filter(|_| i != NONE).and_then(|i| set.into_iter().nth(i)).into_iter().collect())
    })),
    ("+", Impl::Operator(Operator::Arith('+'))),
    ("-", Impl::Operator(Operator::Arith('-'))),
    ("*", Impl::Operator(Operator::Arith('*'))),
    ("/", Impl::Operator(Operator::Arith('/'))),
    ("<", Impl::Operator(Operator::Cmp(Cmp::Lt))),
    ("<=", Impl::Operator(Operator::Cmp(Cmp::Le))),
    (">", Impl::Operator(Operator::Cmp(Cmp::Gt))),
    (">=", Impl::Operator(Operator::Cmp(Cmp::Ge))),
    ("==", Impl::Operator(Operator::Cmp(Cmp::Eq))),
    ("!=", Impl::Operator(Operator::Cmp(Cmp::Ne))),
    ("&&", Impl::Operator(Operator::And)),
    ("||", Impl::Operator(Operator::Or)),
    ("!", Impl::Operator(Operator::Not)),
];

/// The name argument `p`.
pub(crate) fn name(p: &Pipe) -> &str {
    match p {
        Pipe::Name(n) => n,
        p => unreachable!("{p:?} is not a name"),
    }
}

/// The step a built-in function `name` called without arguments is.
pub fn resolve(name: &str) -> Option<Pipe> {
    let b = builtin(name).filter(|b| !matches!(b.imp, Impl::Form | Impl::Missing) && !b.sig.is_number() && !b.sig.required())?;
    Some(Pipe::App(Fun::Builtin(b), Vec::new().into()))
}

/// `a op b` for `+ - * /`, `none` as +∞: `+` and `*` give `none` on overflow or a `none`
/// operand, `-` stops at 0 (`n - none` is 0), `/` gives `none` for a 0 divisor and 0 for a
/// `none` one.
pub fn arith(op: char, a: u64, b: u64) -> u64 {
    match op {
        '+' if a != NONE && b != NONE => a.checked_add(b).unwrap_or(NONE),
        '*' if a != NONE && b != NONE => a.checked_mul(b).unwrap_or(NONE),
        '+' | '*' => NONE,
        '-' if b == NONE => 0,
        '-' if a == NONE => NONE,
        '-' => a.saturating_sub(b),
        _ if b == 0 => NONE,
        _ if b == NONE => 0,
        _ if a == NONE => NONE,
        _ => a / b,
    }
}

/// A comparison operator.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Cmp {
    pub const ALL: [(Cmp, &'static str); 6] = [(Cmp::Lt, "<"), (Cmp::Le, "<="), (Cmp::Gt, ">"), (Cmp::Ge, ">="), (Cmp::Eq, "=="), (Cmp::Ne, "!=")];

    pub fn symbol(self) -> &'static str {
        Cmp::ALL.iter().find(|(c, _)| *c == self).unwrap().1
    }

    pub fn holds(self, a: u64, b: u64) -> bool {
        match self {
            Cmp::Lt => a < b,
            Cmp::Le => a <= b,
            Cmp::Gt => a > b,
            Cmp::Ge => a >= b,
            Cmp::Eq => a == b,
            Cmp::Ne => a != b,
        }
    }
}

fn union(ps: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let mut out = Vec::new();
    for p in ps {
        out.extend(go(p, set.clone(), env)?);
    }
    Ok(dedup(out))
}

fn best(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let (k, ps) = args.split_first().unwrap();
    let mut out = Vec::new();
    for p in ps {
        out.extend(go(p, set.clone(), env)?);
    }
    if stats::on() {
        count_won(&out, &set, env);
    }
    let mut out = dedup(out);
    out.sort_by_cached_key(|c| c.size());
    out.truncate(env.times(k, &set).max(1));
    Ok(out)
}

pub(crate) fn first(ps: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    for p in ps {
        let out = go(p, set.clone(), env)?;
        if !out.is_empty() && out != set {
            return Ok(out);
        }
    }
    Ok(set)
}

fn fix(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [n, p] = args else { unreachable!() };
    let mut set = set;
    for _ in 0..env.times(n, &set) {
        let out = go(p, set.clone(), env)?;
        let same = match (out.first(), set.first()) {
            (Some(a), Some(b)) => a.same(b),
            (a, b) => a.is_none() && b.is_none(),
        };
        env.moved.set(!same);
        set = out;
        if same {
            break;
        }
    }
    Ok(set)
}

fn retry(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [c, a, b] = args else { unreachable!() };
    let out = go(a, set.clone(), env)?;
    if !env.holds(c, &out) {
        return Ok(out);
    }
    let again = go(b, set, env)?;
    let take = match (again.first(), out.first()) {
        (Some(b), Some(a)) => b.size() <= a.size(),
        (b, _) => b.is_some(),
    };
    Ok(if take { again } else { out })
}

pub(crate) fn wins(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let [n, p] = args else { unreachable!() };
    let n = env.times(n, &set);
    if n == 0 {
        return Ok(set);
    }
    let outer = env.wins.replace(0);
    let mut set = set;
    loop {
        let before = env.wins.get();
        set = go(p, set, env)?;
        if env.wins.get() == before || env.wins.get() >= n {
            break;
        }
    }
    env.wins.set(outer + env.wins.get());
    Ok(set)
}

pub(crate) fn assert(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    if env.value(&args[0], &set) != 0 {
        return Ok(set);
    }
    let Pipe::Text(msg) = &args[1] else { unreachable!("assert takes a text") };
    env.ctx(|c| c.mark_cut());
    Err(Error::BackendError(msg.clone()))
}

fn print(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let shown: Vec<String> = args
        .iter()
        .map(|a| match a {
            Pipe::Text(t) => t.clone(),
            Pipe::Name(n) => n.clone(),
            Pipe::Var(Slot::Local(n, Holds::Fn(t))) => format!("{n}:{t}"),
            Pipe::App(Fun::Builtin(b), _) if !b.sig.is_number() => b.sig.to_string(),
            Pipe::App(Fun::Def(c), _) if c.def.value.is_none() => super::defs::sig_of(&c.def).to_string(),
            Pipe::FnValue(f) => match &**f {
                Pipe::App(Fun::Def(c), _) => super::defs::sig_of(&c.def).to_string(),
                Pipe::App(Fun::Builtin(b), _) => b.sig.to_string(),
                f => unreachable!("a function value is a def or a built-in: {f:?}"),
            },
            Pipe::Var(Slot::Local(g, Holds::Group)) => env.reg(g).iter().map(|c| env.infix(c)).collect::<Vec<_>>().join(", "),
            e => match env.value(e, &set) {
                NONE => "none".into(),
                v => v.to_string(),
            },
        })
        .collect();
    let line = shown.join(" ");
    #[cfg(test)]
    PRINTED.with(|p| p.borrow_mut().push(line.clone()));
    eprintln!("{line}");
    Ok(set)
}

#[cfg(test)]
thread_local! {
    /// The lines `print` wrote on this thread.
    pub(crate) static PRINTED: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

fn save(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    env.lex.borrow().regs.borrow_mut().insert(name(&args[0]).to_string(), Value::Group(set.clone()));
    Ok(set)
}

fn clear(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    env.lex.borrow().notes.borrow_mut().push((name(&args[0]).to_string(), None));
    Ok(set)
}

fn note(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let r = name(&args[0]);
    let Some(min) = set.iter().reduce(|a, c| if c.size() < a.size() { c } else { a }) else { return Ok(set) };
    {
        let lex = env.lex.borrow();
        let mut notes = lex.notes.borrow_mut();
        if let Some((_, kept)) = notes.iter_mut().rev().find(|(n, _)| n == r)
            && kept.as_ref().is_none_or(|k| min.size() < k.size())
        {
            *kept = Some(min.clone());
        }
    }
    Ok(set)
}

fn take_min(args: &[Pipe], set: Vec<Cand>, env: &Env) -> Steps {
    let r = name(&args[0]);
    let kept = {
        let lex = env.lex.borrow();
        let mut notes = lex.notes.borrow_mut();
        notes.iter().rposition(|(n, _)| n == r).and_then(|i| notes.remove(i).1)
    };
    Ok(match kept {
        Some(c) if set.first().is_some_and(|m| c.size() < m.size()) => dedup(std::iter::once(c).chain(set).collect()),
        _ => set,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::linear_mba;
    use crate::lang::eval::timed;

    #[test]
    fn declarations() {
        let s = get("if").unwrap();
        assert_eq!(s.to_string(), "(if c:group->num a:pipe b:pipe? g:group) group");
        assert_eq!(s.arity(), "3 or 4 arguments; | gives the last");
        assert_eq!(get("best").unwrap().arity(), "3 or more arguments; | gives the last");
        assert_eq!(get("retry").unwrap().arity(), "4 arguments; | gives the last");
        assert_eq!(get("id").unwrap().arity(), "1 argument; | gives the last");
        assert_eq!(get("print").unwrap().arity(), "1 or more arguments");
        assert_eq!(get("save").unwrap().decl(), "(extern (save r:group g:group) group)");
        assert_eq!(get("relate").unwrap().decl(), "(extern @switch @timed (relate sub:pipe t:term) term)");
        assert!(get("simba").unwrap().switch && !get("finish").unwrap().switch);
        assert_eq!(get("print").unwrap().to_string(), "(print x:any...)");
        assert_eq!(get("assert").unwrap().kind(), Kind::Effect);
        assert!(get("load").is_none() && get("main").is_none());
        assert_eq!(get("&&").unwrap().decl(), "(extern (&& a:num b:group->num...) num)");
        assert_eq!(get("!").unwrap().kind(), Kind::Op);
        assert_eq!(all().iter().filter(|s| s.is_op()).map(|s| s.name.as_str()).collect::<Vec<_>>(), OPERATORS);
        assert_eq!(get("simba").unwrap().kind(), Kind::Alt);
        assert_eq!(get("prepass").unwrap().kind(), Kind::Join);
        assert!(!get("egglog").unwrap().required());
        assert!(all().iter().all(|s| !s.doc.is_empty()));
        let ok = "# The input.\n(extern (x g:group) group)\n\n# Two lines\n# The second describes it.\n(extern @timed (y n:name\n  t:term) term?)";
        let sigs = parse(ok).unwrap();
        assert_eq!(sigs[1].doc, "The second describes it.");
        assert_eq!(sigs[1].decl(), "(extern @timed (y n:name t:term) term?)");
        for (bad, msg) in [
            ("(extern (x g:group) group)", "no description"),
            ("# a\n(extern (x g:group) group)\n# b\n(extern (x g:group) group)", "declared twice"),
            ("# a\n(extern (x g:group) term)", "no calling kind"),
            ("# a\n(extern (x n:num) num)", "must be term or group"),
            ("# a\n(extern (x t:term g:group) group)", "only the input"),
            ("# a\n(extern (x n:num... g:group) group)", "only pipe and any take"),
            ("# a\n(extern (x n:int g:group) group)", "unknown type int"),
            ("# a\n(extern @pure (x g:group) group)", "unknown attribute"),
            ("# a\n(extern @uncounted (x g:group) group)", "@uncounted says how"),
            ("# a\n(extern @switch (x g:group) group)", "@switch is for a pass over one term"),
            ("# a\n(extern (x g:group) group", "unclosed"),
            ("# a\n(def (x g:group) group)", "expected (extern"),
            ("# a
(extern @timed (+ a:num b:num) num)", "an operator takes"),
            ("# a\n(extern @pipe (x g:group) group)", "unknown attribute"),
            ("# a\n(extern (x g:group))", "a function without a result has no input"),
            ("# a
(extern (+ a:num g:group) num)", "an operator takes"),
            ("# a
(extern (+ a:group->num... b:num) num)", "an operator takes"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn condition_signatures() {
        let ty = |f: &str| get(f).unwrap().params[0].ty.clone();
        for f in ["filter", "any", "all"] {
            assert_eq!(ty(f), Ty::parse("term->num").unwrap(), "{f}");
        }
        for f in ["if", "retry"] {
            assert_eq!(ty(f), Ty::parse("group->num").unwrap(), "{f}");
        }
        for f in ["best", "fix", "wins"] {
            assert_eq!(ty(f), Ty::Num, "{f}");
        }
        assert_eq!(get("filter").unwrap().arity(), "2 arguments; | gives the last");
        let sigs = parse("# a\n(extern (x c:term->num p:group->group... g:group) group)").unwrap();
        assert_eq!(sigs[0].to_string(), "(x c:term->num p:pipe... g:group) group");
        assert_eq!(parse("# a\n(extern (x f:term->term g:group) group)").unwrap()[0].to_string(), "(x f:term->term g:group) group");
        assert!(Ty::parse("term->term").unwrap().fits(&Ty::pipe()) && !Ty::parse("term->num").unwrap().fits(&Ty::parse("group->num").unwrap()) && !Ty::pipe().fits(&Ty::parse("term->term").unwrap()));
        for (bad, msg) in [
            ("# a\n(extern (x p:num->term g:group) group)", "a function takes one input, term or group"),
            ("# a\n(extern (x c:term->num? g:group) group)", "only pipe and any take"),
            ("# a\n(extern (x g:group) term->num)", "a function gives num"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn every_builtin_has_an_implementation_and_every_implementation_an_extern() {
        use crate::lang::types::{Kind, Rep};
        for b in BUILTINS.iter() {
            let kind = b.sig.kind();
            let runs_as_declared = match b.imp {
                Impl::Form => ["seq", "smallest"].contains(&b.name),
                Impl::Missing => false,
                Impl::Group(_) => kind == Kind::Group || kind == Kind::Pick || kind == Kind::Effect,
                Impl::Join(_) => kind == Kind::Join,
                Impl::Each(_) | Impl::Polish(_) | Impl::EachCand(_) => kind == Kind::Each,
                Impl::Alt(..) => kind == Kind::Alt,
                Impl::Num(_) => b.sig.is_number() && !b.sig.is_op() && !b.sig.params.is_empty(),
                Impl::Operator(o) => {
                    let reps: Vec<Rep> = b.sig.params.iter().map(|p| p.rep).collect();
                    let arity: &[Rep] = match o {
                        Operator::Not => &[Rep::One],
                        Operator::Arith(_) | Operator::Cmp(_) => &[Rep::One, Rep::One],
                        Operator::And | Operator::Or => &[Rep::One, Rep::Many],
                    };
                    kind == Kind::Op && reps == arity
                }
                Impl::TermNum(_) => kind == Kind::TermNum && b.sig.params.is_empty(),
                Impl::GroupNum(_) => kind == Kind::GroupNum && b.sig.params.is_empty(),
                Impl::FromText(_) => kind == Kind::FromText && b.sig.params.is_empty(),
                Impl::TermText(_) => kind == Kind::TermText && b.sig.params.is_empty(),
            };
            assert!(runs_as_declared, "{}: no implementation for its calling kind", b.sig.decl());
        }
        let term = linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string());
        let polish = linear_mba::POLISH.iter().map(|(n, _)| format!("polish_{n}"));
        let mut rust: Vec<String> = IMPLS.iter().chain(crate::builtin_passes::IMPLS).map(|(n, _)| n.to_string()).chain(term).chain(polish).collect();
        for n in &rust {
            assert!(builtin(n).is_some(), "{n} has no extern in src/builtins.pipe");
        }
        rust.sort();
        rust.dedup();
        assert_eq!(rust.len(), BUILTINS.len(), "an implementation is given twice");
        assert!(linear_mba::ALTERNATIVES.iter().all(|(a, _)| matches!(builtin(a).map(|b| b.imp), Some(Impl::Alt(..)))));
    }

    #[test]
    fn timed_matches_the_attribute() {
        for s in crate::lang::builtins::all().iter().filter(|s| !s.is_number() && !s.is_text()) {
            let call = crate::lang::builtins::sample(s);
            assert_eq!(timed(&crate::lang::parser::parse(&call).unwrap()), s.timed, "{}", s.decl());
        }
    }
}
