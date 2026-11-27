//! The signatures of the built-in functions of the pipeline language, declared in
//! `src/builtins.pipe` (`docs/pipe-language.md`). `crate::pipe_lang` parses calls by them
//! and `sched::Passes::check` reads their attributes; nothing here runs per evaluation.

use crate::sched::Pass;
use std::collections::HashMap;
use std::fmt;
use std::sync::LazyLock;

/// A parameter or result type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    Num,
    Term,
    /// `term?`: one candidate or none.
    MaybeTerm,
    Group,
    Pipe,
    Reg,
    Name,
}

impl Ty {
    const WORDS: [(Ty, &'static str); 7] = [(Ty::Num, "num"), (Ty::Term, "term"), (Ty::MaybeTerm, "term?"), (Ty::Group, "group"), (Ty::Pipe, "pipe"), (Ty::Reg, "reg"), (Ty::Name, "name")];

    pub fn word(self) -> &'static str {
        Ty::WORDS.iter().find(|(t, _)| *t == self).unwrap().1
    }

    fn of(w: &str) -> Option<Ty> {
        Ty::WORDS.iter().find(|(_, s)| *s == w).map(|(t, _)| *t)
    }

    /// What an argument of this type is, for messages.
    pub(crate) fn what(self) -> &'static str {
        match self {
            Ty::Num => "an expression",
            Ty::Pipe => "a pipeline",
            Ty::Reg => "a register name",
            Ty::Name => "a name",
            _ => "a candidate",
        }
    }
}

fn noun(t: Ty) -> &'static str {
    noun_of(t.what())
}

fn noun_of(w: &str) -> &str {
    w.strip_prefix("an ").or_else(|| w.strip_prefix("a ")).unwrap_or(w)
}

/// How often a parameter is written: once, one or more times (`TYPE...`), or maybe (`TYPE?`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rep {
    One,
    Many,
    Opt,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub rep: Rep,
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let suffix = match self.rep {
            Rep::One => "",
            Rep::Many => "...",
            Rep::Opt => "?",
        };
        write!(f, "{}:{}{suffix}", self.name, self.ty.word())
    }
}

/// How a function is called, from its input and result types (`docs/pipe-language.md`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `group -> group`: on the whole list.
    Group,
    /// `term -> term`: on each candidate, an unchanged result keeping it.
    Each,
    /// `term -> term?`: on each candidate, no result dropping it.
    Alt,
    /// `term -> group`: on the main candidate, the result replacing the list.
    Main,
    /// `term -> num`: on the main candidate, 0 without candidates.
    TermNum,
    /// `group -> num`: on the whole list, 0 without candidates.
    GroupNum,
}

impl Kind {
    pub const ALL: [(Kind, &'static str); 6] = [
        (Kind::Group, "on the whole list (group -> group)"),
        (Kind::Each, "on each candidate (term -> term)"),
        (Kind::Alt, "alternatives, on each candidate, none when no form is found (term -> term?)"),
        (Kind::Main, "on the main candidate, the result replacing the list (term -> group)"),
        (Kind::TermNum, "numbers of the main candidate (term -> num)"),
        (Kind::GroupNum, "numbers of the whole list (group -> num)"),
    ];

    fn of(input: Ty, result: Ty) -> Option<Kind> {
        Some(match (input, result) {
            (Ty::Group, Ty::Group) => Kind::Group,
            (Ty::Term, Ty::Term) => Kind::Each,
            (Ty::Term, Ty::MaybeTerm) => Kind::Alt,
            (Ty::Term, Ty::Group) => Kind::Main,
            (Ty::Term, Ty::Num) => Kind::TermNum,
            (Ty::Group, Ty::Num) => Kind::GroupNum,
            _ => return None,
        })
    }
}

/// The signature of a built-in function.
#[derive(Clone, Debug, PartialEq)]
pub struct Sig {
    pub name: String,
    /// The parameters written in a call.
    pub params: Vec<Param>,
    /// The implicit input, `term` or `group`.
    pub input: Param,
    pub result: Ty,
    /// `@bookkeeping`: only moves candidates, so it runs past the time limit too.
    pub bookkeeping: bool,
    /// `@simplify_only`: only in `pipeline`.
    pub simplify_only: bool,
    /// The comment line before the declaration.
    pub doc: String,
}

impl Sig {
    pub fn kind(&self) -> Kind {
        Kind::of(self.input.ty, self.result).unwrap()
    }

    /// Whether it gives a number, so belongs in expressions, not steps.
    pub fn is_number(&self) -> bool {
        self.result == Ty::Num
    }

    /// Whether a call must write an argument.
    pub fn required(&self) -> bool {
        self.params.iter().any(|p| p.rep != Rep::Opt)
    }

    /// The arguments a call takes, in words: `an expression and one or more pipelines`.
    pub fn takes(&self) -> String {
        let mut words: Vec<(String, usize)> = Vec::new();
        for p in &self.params {
            let w = match p.rep {
                Rep::One => p.ty.what().to_string(),
                Rep::Many => format!("one or more {}s", noun(p.ty)),
                Rep::Opt => format!("an optional {}", noun(p.ty)),
            };
            match words.last_mut() {
                Some((last, n)) if *last == w && p.rep == Rep::One => *n += 1,
                _ => words.push((w, 1)),
            }
        }
        let words: Vec<String> = words
            .into_iter()
            .map(|(w, n)| match n {
                1 => w,
                n => format!("{} {}s", ["two", "three", "four"].get(n - 2).copied().unwrap_or("several"), noun_of(&w)),
            })
            .collect();
        match words.as_slice() {
            [] => "no arguments".into(),
            [a] => a.clone(),
            [rest @ .., last] => format!("{} and {last}", rest.join(", ")),
        }
    }

    /// The declaration as `src/builtins.pipe` writes it.
    pub fn decl(&self) -> String {
        let mut attrs = String::new();
        if self.bookkeeping {
            attrs += "@bookkeeping ";
        }
        if self.simplify_only {
            attrs += "@simplify_only ";
        }
        format!("(extern {attrs}{self})")
    }
}

/// `(NAME PARAM:TYPE ... INPUT:TYPE) RESULT`.
impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for p in self.params.iter().chain([&self.input]) {
            write!(f, " {p}")?;
        }
        write!(f, ") {}", self.result.word())
    }
}

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
    let spaced = text.replace('(', " ( ").replace(')', " ) ");
    let toks: Vec<&str> = spaced.split_whitespace().collect();
    let bad = || format!("expected (extern [@ATTR ...] (NAME PARAM:TYPE ... INPUT:TYPE) RESULT): {text}");
    let [open, kw, rest @ ..] = toks.as_slice() else { return Err(bad()) };
    if (*open, *kw) != ("(", "extern") {
        return Err(bad());
    }
    let mut rest = rest.iter().copied().peekable();
    let (mut bookkeeping, mut simplify_only) = (false, false);
    while let Some(a) = rest.next_if(|t| t.starts_with('@')) {
        match a {
            "@bookkeeping" => bookkeeping = true,
            "@simplify_only" => simplify_only = true,
            _ => return Err(format!("unknown attribute {a}; known: @bookkeeping @simplify_only")),
        }
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
    let result = rest.next().and_then(Ty::of).ok_or_else(|| format!("{name}: expected a result type"))?;
    if rest.next() != Some(")") || rest.next().is_some() {
        return Err(bad());
    }
    let input = params.pop().ok_or_else(|| format!("{name}: the last parameter is the input, term or group"))?;
    if input.rep != Rep::One || !matches!(input.ty, Ty::Term | Ty::Group) {
        return Err(format!("{name}: the input {input} must be term or group"));
    }
    if !matches!(result, Ty::Num | Ty::Term | Ty::MaybeTerm | Ty::Group) {
        return Err(format!("{name}: a function gives num, term, term? or group"));
    }
    if Kind::of(input.ty, result).is_none() {
        return Err(format!("{name}: no calling kind takes {} to {}", input.ty.word(), result.word()));
    }
    for p in &params {
        match (p.ty, p.rep) {
            (Ty::Term | Ty::MaybeTerm | Ty::Group, _) => return Err(format!("{name}: {p}: only the input is a candidate")),
            (Ty::Num | Ty::Reg | Ty::Name, Rep::Many) | (Ty::Num, Rep::Opt) => return Err(format!("{name}: {p}: only pipe takes ..., only pipe, reg and name take ?")),
            _ => {}
        }
    }
    Ok(Sig { name, params, input, result, bookkeeping, simplify_only, doc: String::new() })
}

fn param(p: &str) -> Result<Param, String> {
    let (name, ty) = p.split_once(':').ok_or_else(|| format!("expected NAME:TYPE, found {p}"))?;
    let (ty, rep) = match (ty.strip_suffix("..."), ty.strip_suffix('?')) {
        (Some(t), _) => (t, Rep::Many),
        (_, Some(t)) if t != "term" => (t, Rep::Opt),
        _ => (ty, Rep::One),
    };
    let ty = Ty::of(ty).ok_or_else(|| format!("unknown type {ty} in {p}; known: num term term? group pipe reg name"))?;
    Ok(Param { name: name.to_string(), ty, rep })
}

static TABLE: LazyLock<(Vec<Sig>, HashMap<String, usize>)> = LazyLock::new(|| {
    let sigs = parse(include_str!("builtins.pipe")).unwrap_or_else(|e| panic!("src/builtins.pipe: {e}"));
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

/// The names that expand when parsed instead of naming functions or variables.
pub const MACROS: [&str; 3] = ["let", "on", "off"];

/// The built-in function a pass of a parsed pipeline calls.
pub fn of_pass(p: &Pass) -> Option<&'static Sig> {
    let name = match p {
        Pass::Set(i) => crate::pipe::SET_PASSES[*i],
        Pass::Egglog(_) => "egglog",
        Pass::Save(_) => "save",
        Pass::Load(_) => "load",
        Pass::Label(_) => "label",
        Pass::Term { name, .. } => name,
        Pass::Off(_) | Pass::On(_) | Pass::Assign(..) => return None,
    };
    get(name)
}

/// The functions a step can call, for error messages: by name, or as a call when it needs
/// arguments.
pub fn step_names() -> Vec<String> {
    let steps = || all().iter().filter(|s| !s.is_number());
    let bare = steps().filter(|s| !s.required()).map(|s| s.name.clone());
    let calls = steps().filter(|s| !s.params.is_empty()).map(|s| format!("({} {})", s.name, s.params.iter().map(Param::to_string).collect::<Vec<_>>().join(" ")));
    bare.chain(calls).chain(["(off NAME...)".into(), "(on NAME...)".into()]).collect()
}

/// The functions an expression can call, for error messages.
pub fn number_names() -> Vec<String> {
    all().iter().filter(|s| s.is_number()).map(|s| if s.required() { format!("({} ...)", s.name) } else { s.name.clone() }).collect()
}

/// Every declaration with its description, grouped by calling kind (`--show-builtins`).
pub fn listing() -> String {
    let mut out = String::from("# The built-in functions (src/builtins.pipe), by how they are called.\n");
    for (kind, title) in Kind::ALL {
        out += &format!("\n# --- {title}\n");
        for s in all().iter().filter(|s| s.kind() == kind) {
            out += &format!("# {}\n{}\n", s.doc, s.decl());
        }
    }
    out
}

/// A call of `s` with placeholder arguments: `1`, `x`, `id`; optional ones left out.
#[cfg(test)]
pub(crate) fn sample(s: &Sig) -> String {
    let args: Vec<&str> = s
        .params
        .iter()
        .filter(|p| p.rep != Rep::Opt)
        .map(|p| match p.ty {
            Ty::Num => "1",
            Ty::Pipe => "id",
            _ => "x",
        })
        .collect();
    if args.is_empty() { s.name.clone() } else { format!("({} {})", s.name, args.join(" ")) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declarations() {
        let s = get("if").unwrap();
        assert_eq!(s.to_string(), "(if c:num a:pipe b:pipe? g:group) group");
        assert_eq!(s.takes(), "an expression, a pipeline and an optional pipeline");
        assert_eq!(get("best").unwrap().takes(), "an expression and one or more pipelines");
        assert_eq!(get("retry").unwrap().takes(), "an expression and two pipelines");
        assert_eq!(get("id").unwrap().takes(), "no arguments");
        assert_eq!(get("save").unwrap().decl(), "(extern @bookkeeping (save r:reg g:group) group)");
        assert_eq!(get("simba").unwrap().kind(), Kind::Alt);
        assert_eq!(get("prepass").unwrap().kind(), Kind::Main);
        assert!(get("egglog").unwrap().simplify_only && !get("egglog").unwrap().required());
        assert!(all().iter().all(|s| !s.doc.is_empty()));
        let ok = "# The input.\n(extern (x g:group) group)\n\n# Two lines\n# The second describes it.\n(extern @bookkeeping (y n:name\n  t:term) term?)";
        let sigs = parse(ok).unwrap();
        assert_eq!(sigs[1].doc, "The second describes it.");
        assert_eq!(sigs[1].decl(), "(extern @bookkeeping (y n:name t:term) term?)");
        for (bad, msg) in [
            ("(extern (x g:group) group)", "no description"),
            ("# a\n(extern (x g:group) group)\n# b\n(extern (x g:group) group)", "declared twice"),
            ("# a\n(extern (x g:group) term)", "no calling kind"),
            ("# a\n(extern (x n:num) num)", "must be term or group"),
            ("# a\n(extern (x t:term g:group) group)", "only the input"),
            ("# a\n(extern (x n:num... g:group) group)", "only pipe takes"),
            ("# a\n(extern (x n:int g:group) group)", "unknown type int"),
            ("# a\n(extern @pure (x g:group) group)", "unknown attribute"),
            ("# a\n(extern (x g:group) group", "unclosed"),
            ("# a\n(def (x g:group) group)", "expected (extern"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }
}
