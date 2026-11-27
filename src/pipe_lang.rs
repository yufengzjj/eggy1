//! The pipeline language (`docs/pipe-language.md`): `a | b` runs `b` on the candidates of
//! `a`, `(FORM args...)` is a combinator or a pass with arguments, `NAME = VALUE` assigns a
//! variable, conditions are expressions (`(if (mul >= 4 && shift < 1) (off small_blocks))`).
//! Parsed into `sched::Pipe`.

use crate::builtins::{self, Param, Rep, Sig, Ty};
use crate::pipe::{CONDS, FEATURES, resolve};
use crate::sched::{Call, CallArg, Cmp, Def, Expr, INNER, NONE, NVARS, Pass, Pipe, is_switch, var, var_index};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Open,
    Close,
    Bar,
    Or,
    And,
    Not,
    Cmp(&'static str),
    Arith(char),
    Num(u64),
    Name(String),
    Assign,
    At,
    Colon,
}

fn name_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '/'
}

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let cs: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        let next = cs.get(i + 1).copied();
        let two = |a: char| next == Some(a);
        let (tok, len) = match c {
            '#' => {
                while i < cs.len() && cs[i] != '\n' {
                    i += 1;
                }
                continue;
            }
            c if c.is_whitespace() => {
                i += 1;
                continue;
            }
            '(' => (Tok::Open, 1),
            ')' => (Tok::Close, 1),
            '|' if two('|') => (Tok::Or, 2),
            '|' => (Tok::Bar, 1),
            '&' if two('&') => (Tok::And, 2),
            '!' if two('=') => (Tok::Cmp("!="), 2),
            '!' => (Tok::Not, 1),
            '<' if two('=') => (Tok::Cmp("<="), 2),
            '<' => (Tok::Cmp("<"), 1),
            '>' if two('=') => (Tok::Cmp(">="), 2),
            '>' => (Tok::Cmp(">"), 1),
            '=' if two('=') => (Tok::Cmp("=="), 2),
            '=' => (Tok::Assign, 1),
            '@' => (Tok::At, 1),
            ':' => (Tok::Colon, 1),
            '+' | '-' | '*' | '/' => (Tok::Arith(c), 1),
            c if c.is_ascii_digit() => {
                let n: String = cs[i..].iter().take_while(|c| c.is_ascii_digit()).collect();
                let len = n.len();
                let v = n.parse().ok().filter(|v| *v != NONE).ok_or_else(|| format!("number too large: {n}"))?;
                (Tok::Num(v), len)
            }
            c if name_start(c) => {
                let len = cs[i..].iter().take_while(|c| name_char(**c)).count();
                (Tok::Name(cs[i..i + len].iter().collect()), len)
            }
            _ if s.contains("(extern") => return Err(NO_EXTERN.into()),
            _ => return Err(format!("unexpected character {c:?} in pipeline")),
        };
        out.push(tok);
        i += len;
    }
    Ok(out)
}

/// The functions of `src/builtins.pipe` whose arguments `construct` reads; the rest without
/// arguments are passes (`crate::pipe::resolve`).
#[cfg(test)]
pub(crate) const FORMS: [&str; 23] = [
    "seq", "union", "best", "first", "fix", "if", "retry", "smallest", "scope", "regions", "again", "tag", "cand", "smaller", "wins", "filter", "save", "load", "label",
    "clear", "note", "take_min", "egglog",
];

/// The number functions whose arguments `number` reads; the rest are `CONDS` and `FEATURES`.
#[cfg(test)]
pub(crate) const NUMBER_FORMS: [&str; 4] = ["size", "same", "any", "all"];

const NO_WITH: &str = "(with KEY=VALUE ... p) is no longer read: write (KEY = VALUE | ... | p), as in (rewrites = 8 | semi_leaves = 2 | rewrite); with's bit_splits=N is bit_split_budget = N";
const NO_TIME_LIMIT: &str = "(time-limit N) is no longer read: write time_limit = N, or time_limit = none for no limit";
const NO_TRUE: &str = "true is no longer a condition: write 1, or (any 1) for true only where there are candidates";
pub(crate) const NO_EXTERN: &str = "extern declarations are only read from src/builtins.pipe";

/// An argument of a call, as its parameter's type reads it.
#[derive(Clone)]
enum Arg {
    Num(Expr),
    Name(String),
    Pipe(Pipe),
    Pipes(Vec<Pipe>),
    Absent,
}

/// The arguments of a call in order; each read as its signature says, so a mismatch is a
/// bug that the tests of every declaration find.
struct Args(std::vec::IntoIter<Arg>);

impl Args {
    fn num(&mut self) -> Expr {
        let Some(Arg::Num(e)) = self.0.next() else { unreachable!() };
        e
    }

    fn name(&mut self) -> String {
        let Some(Arg::Name(n)) = self.0.next() else { unreachable!() };
        n
    }

    fn maybe_name(&mut self) -> Option<String> {
        match self.0.next() {
            Some(Arg::Name(n)) => Some(n),
            _ => None,
        }
    }

    fn pipe(&mut self) -> Box<Pipe> {
        self.maybe_pipe().unwrap()
    }

    fn maybe_pipe(&mut self) -> Option<Box<Pipe>> {
        match self.0.next() {
            Some(Arg::Pipe(p)) => Some(Box::new(p)),
            _ => None,
        }
    }

    fn pipes(&mut self) -> Vec<Pipe> {
        let Some(Arg::Pipes(ps)) = self.0.next() else { unreachable!() };
        ps
    }
}

/// The pipeline a call of the group function `f` with `args` stands for; `None` when no
/// Rust code implements `f`.
fn construct(f: &str, args: Vec<Arg>) -> Option<Pipe> {
    let empty = args.is_empty();
    let mut a = Args(args.into_iter());
    Some(match f {
        "seq" => Pipe::Seq(a.pipes()),
        "union" => Pipe::Union(a.pipes()),
        "first" => Pipe::First(a.pipes()),
        "best" => Pipe::Best(a.num(), a.pipes()),
        "fix" => Pipe::Fix(a.num(), a.pipe()),
        "wins" => Pipe::Wins(a.num(), a.pipe()),
        "if" => Pipe::If(a.num(), a.pipe(), a.maybe_pipe().unwrap_or_else(|| Box::new(Pipe::Pass(Pass::id())))),
        "retry" => Pipe::Retry(a.num(), a.pipe(), a.pipe()),
        "smallest" => smallest(*a.pipe()),
        "scope" => Pipe::Scope(a.pipe()),
        "regions" => Pipe::Regions(a.pipe()),
        "again" => Pipe::Again(a.pipe()),
        "tag" => Pipe::Tag(a.name(), a.pipe()),
        "cand" => Pipe::Cand(a.name(), a.pipe()),
        "smaller" => Pipe::Smaller(a.name(), a.pipe()),
        "filter" => Pipe::Filter(a.num()),
        "save" | "load" | "label" | "clear" | "note" | "take_min" => Pipe::Pass(resolve(&format!("{f}/{}", a.name()))?),
        "egglog" => Pipe::Pass(Pass::Egglog(a.maybe_name().map_or_else(|| "egglog".into(), |l| format!("egglog/{l}")))),
        _ if empty => Pipe::Pass(resolve(f)?),
        _ => return None,
    })
}

/// The expression a call of the number function `f` with `args` stands for; `None` when no
/// Rust code implements `f`.
fn number(f: &str, args: Vec<Arg>) -> Option<Expr> {
    let mut a = Args(args.into_iter());
    Some(match f {
        "size" => a.maybe_name().map_or(Expr::Feature(0), Expr::Size),
        "same" => Expr::Same(a.name()),
        "any" => Expr::Any(Box::new(a.num())),
        "all" => Expr::All(Box::new(a.num())),
        _ => match CONDS.iter().position(|c| *c == f) {
            Some(i) => Expr::Is(i),
            None => Expr::Feature(FEATURES.iter().position(|c| *c == f)?),
        },
    })
}

fn unimplemented(s: &Sig) -> String {
    format!("{s} is declared in src/builtins.pipe but nothing implements it")
}

/// The expression a name stands for: a variable, a function of the candidates or `none`.
fn name_expr(n: &str) -> Result<Expr, String> {
    if let Some(s) = builtins::get(n).filter(|s| s.is_number()) {
        if s.required() {
            return Err(format!("{n} needs parentheses: ({n} ...); {s}"));
        }
        return number(n, vec![Arg::Absent; s.params.len()]).ok_or_else(|| unimplemented(s));
    }
    if let Some(i) = var_index(n) {
        Ok(Expr::Var(i))
    } else if n == "none" {
        Ok(Expr::Num(NONE))
    } else if n == "true" {
        Err(NO_TRUE.into())
    } else if let Some(s) = builtins::get(n) {
        Err(format!("{n} gives candidates, not a number: {s}; an expression reads variables and number functions"))
    } else {
        Err(format!("unknown name {n} in an expression; known: {} and the variables", builtins::number_names().join(" ")))
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
    pub value: Option<Expr>,
    /// Warnings of reading it.
    pub notes: Vec<String>,
}

/// A parameter of the function whose body is read, and the type its uses so far give it.
#[derive(Clone)]
struct ParamUse {
    name: String,
    ty: Option<Ty>,
    annotated: bool,
    /// Its uses, and those among them where a pipeline and a group fit alike (`t = r`, a body
    /// `r`).
    uses: usize,
    loose: usize,
}

/// The right side of an assignment, by the type of what it gives.
enum Rhs {
    Num(Expr),
    Group(Pipe),
}

struct Parser<'a> {
    toks: Vec<Tok>,
    at: usize,
    defs: &'a Defs,
    /// The names of `defs` expanded.
    used: Vec<String>,
    params: Vec<ParamUse>,
    /// The group variables bound so far in the text, which a name alone can read as a value.
    groups: Vec<String>,
    /// In the body of a function that is an expression, outside any step: a function of the
    /// candidates needs its input written.
    no_input: bool,
    /// The stage read follows a `|`.
    after_bar: bool,
    /// An atom already read, which the expression read next starts with.
    pending: Option<Expr>,
}

fn seq_of(mut stages: Vec<Pipe>) -> Pipe {
    if stages.len() == 1 { stages.pop().unwrap() } else { Pipe::Seq(stages) }
}

impl<'a> Parser<'a> {
    fn new(toks: Vec<Tok>, defs: &'a Defs) -> Parser<'a> {
        Parser { toks, at: 0, defs, used: Vec::new(), params: Vec::new(), groups: Vec::new(), no_input: false, after_bar: false, pending: None }
    }

    /// Whether `n` is a group value: a group parameter, or a group variable bound before in
    /// the text that names nothing else.
    fn group_value(&self, n: &str) -> bool {
        match self.param(n) {
            Some(i) => self.params[i].ty == Some(Ty::Group),
            None => self.groups.iter().any(|g| g == n) && !self.defs.contains_key(n) && !known_name(n) && resolve(n).is_none(),
        }
    }

    /// An explicit input ahead: a group value's name, a parenthesized stage (run on the
    /// step's input unless it starts with a value), or with `loose` a name that names nothing
    /// else, read as a group variable (the checks find it unbound); `None` (nothing read)
    /// otherwise.
    fn group_input(&mut self, loose: bool) -> Result<Option<Pipe>, String> {
        match self.peek().cloned() {
            Some(Tok::Name(n)) if self.input_name(&n, loose) => {
                self.at += 1;
                self.use_param(&n, Ty::Group)?;
                Ok(Some(Pipe::Value(n)))
            }
            Some(Tok::Open) => {
                let outer = std::mem::take(&mut self.no_input);
                let p = self.stage();
                self.no_input = outer;
                let p = p?;
                if outer && !starts_with_value(&p) {
                    return Err(format!("{} needs its input here, outside any step: start it with a value, as in (g | ...)", stage(&p)));
                }
                Ok(Some(p))
            }
            _ => Ok(None),
        }
    }

    fn input_name(&self, n: &str, loose: bool) -> bool {
        self.group_value(n) || self.param(n).is_some_and(|i| self.params[i].ty.is_none()) || loose && self.param(n).is_none() && self.unknown(n)
    }

    /// Whether an explicit input is ahead, as `group_input` reads it.
    fn input_ahead(&self, loose: bool) -> bool {
        match self.peek() {
            Some(Tok::Name(n)) => self.input_name(n, loose),
            Some(Tok::Open) => true,
            _ => false,
        }
    }

    /// Whether `n` names no variable, function, definition or word of the language.
    fn unknown(&self, n: &str) -> bool {
        !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || defined_builtin(n) || ["none", "true", "def", "extern"].contains(&n))
    }

    /// The signature of the function `n` defined.
    fn sig_named(&self, n: &str) -> Sig {
        let d = &self.defs[n];
        d.def.as_ref().map_or_else(|| def_sig(n, &d.params), |d| sig_of(d))
    }

    /// Whether an expression is ahead, for the body of a function: a number, `!`, or a name
    /// of a variable, number function or numeric parameter, maybe after `(`.
    fn expr_ahead(&self) -> bool {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        match self.peek_at(k) {
            Some(Tok::Num(_) | Tok::Not) => true,
            Some(Tok::Name(n)) if self.peek_at(k + 1) != Some(&Tok::Assign) => match self.param(n) {
                Some(i) => self.params[i].ty == Some(Ty::Num),
                None => {
                    let number_def = self.defs.get(n).and_then(|d| d.def.as_ref()).is_some_and(|d| d.value.is_some());
                    number_def || n == "none" || builtins::get(n).map_or(var_index(n).is_some() && !self.defs.contains_key(n), |s| s.is_number())
                }
            },
            _ => false,
        }
    }
    fn peek(&self) -> Option<&Tok> {
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

    fn expect(&mut self, t: Tok, what: &str) -> Result<(), String> {
        match self.next() {
            Some(x) if x == t => Ok(()),
            x => Err(format!("expected {what}, found {}", show_tok(x.as_ref()))),
        }
    }

    fn name(&mut self, what: &str) -> Result<String, String> {
        match self.next() {
            Some(Tok::Name(n)) => Ok(n),
            x => Err(format!("expected {what}, found {}", show_tok(x.as_ref()))),
        }
    }

    fn param(&self, n: &str) -> Option<usize> {
        self.params.iter().position(|p| p.name == n)
    }

    /// Records a use of `n` as `ty` where `n` is a parameter; an error where an earlier use
    /// gave it another type.
    fn use_param(&mut self, n: &str, ty: Ty) -> Result<(), String> {
        let Some(i) = self.param(n) else { return Ok(()) };
        let p = &mut self.params[i];
        p.uses += 1;
        match p.ty {
            Some(t) if t != ty => Err(format!("parameter {n} is used as {} and as {}", t.what(), ty.what())),
            _ => {
                p.ty = Some(ty);
                Ok(())
            }
        }
    }

    fn pipe(&mut self) -> Result<Pipe, String> {
        let (stages, tail) = self.stages_of_pipe()?;
        let p = seq_of(stages);
        match tail {
            Some(e) => Err(format!("{} | {} gives a number, not candidates: a pipeline that ends in a number goes where a number does, as in x = (a | size)", show(&p), show_expr(&e, 1))),
            None => Ok(p),
        }
    }

    /// Whether a step that gives a number is ahead: a number function or a function defined
    /// that gives a number, maybe after `(`.
    fn number_step_ahead(&self) -> bool {
        let k = (0..).find(|k| self.peek_at(*k) != Some(&Tok::Open)).unwrap();
        match self.peek_at(k) {
            Some(Tok::Name(n)) if self.peek_at(k + 1) != Some(&Tok::Assign) && self.param(n).is_none() => builtins::get(n).is_some_and(|s| s.is_number()) || self.number_def(n),
            _ => false,
        }
    }

    /// The stages of a pipeline `a | b | ...`, and the expression of a last step that gives a
    /// number (`a | size`).
    fn stages_of_pipe(&mut self) -> Result<(Vec<Pipe>, Option<Expr>), String> {
        self.stages_after(Vec::new())
    }

    /// The stages of a pipeline whose first `stages` are read already.
    fn stages_after(&mut self, mut stages: Vec<Pipe>) -> Result<(Vec<Pipe>, Option<Expr>), String> {
        if !stages.is_empty() {
            if self.peek() != Some(&Tok::Bar) {
                return Ok((stages, None));
            }
            self.at += 1;
        }
        loop {
            if !stages.is_empty() && self.number_step_ahead() {
                let e = self.or()?;
                if let (Some(Tok::Bar), Some(m)) = (self.peek(), self.peek_at(1)) {
                    return Err(format!("{} gives a number; {} takes candidates: a step that gives a number can only end a pipeline", show_expr(&e, 1), show_tok(Some(m))));
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
        let k = usize::from(self.peek() == Some(&Tok::Open));
        if let Some(e) = self.old_form(k) {
            return Err(e.into());
        }
        let args_follow = |p: &Self| matches!(p.peek_at(1), Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not));
        if let (Some(Tok::Name(n)), Some(Tok::Bar), Some(Tok::Name(m))) = (self.peek(), self.peek_at(1), self.peek_at(2))
            && self.param(n).is_none()
            && (builtins::get(n).is_some_and(|s| s.is_number()) || self.number_def(n))
        {
            return Err(format!("{n} gives a number; {m} takes candidates: a step that gives a number can only end a pipeline"));
        }
        match self.next() {
            Some(Tok::Name(n)) if self.group_value(&n) => {
                self.use_param(&n, Ty::Group)?;
                Ok(Pipe::Value(n))
            }
            Some(Tok::Name(n)) if self.param(&n).is_some() => {
                self.use_param(&n, Ty::Pipe)?;
                Ok(Pipe::Param(self.param(&n).unwrap(), n))
            }
            Some(Tok::Name(n)) if self.defs.contains_key(&n) => {
                let d = &self.defs[&n];
                if !d.params.is_empty() {
                    return Err(format!("{n} needs parentheses: ({n} ...); {}", self.sig_named(&n)));
                }
                if self.number_def(&n) {
                    return Err(format!("{n} gives a number, not candidates: {}; a step calls a function that gives candidates", self.sig_named(&n)));
                }
                if after_bar && d.def.as_ref().is_some_and(|d| !d.step) {
                    return Err(not_pipe(&self.sig_named(&n)));
                }
                if d.def.as_ref().is_some_and(|d| d.inline && d.input.is_some()) {
                    let p = self.call_of(&n, Vec::new())?;
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
                    Some(Tok::Name(n)) if self.defs.get(&n).is_some_and(|d| !d.params.is_empty() || d.run && args_follow(self)) => {
                        self.at += 1;
                        self.def_call(&n, after_bar)?
                    }
                    Some(Tok::Name(n)) if self.param(&n).is_some_and(|i| self.params[i].ty != Some(Ty::Group)) && args_follow(self) => {
                        self.at += 1;
                        let Some(input) = self.group_input(true)? else { return Err(format!("parameter {n} takes a group value: ({n} g)")) };
                        self.use_param(&n, Ty::Pipe)?;
                        Pipe::Seq(vec![input, Pipe::Param(self.param(&n).unwrap(), n)])
                    }
                    Some(Tok::Name(n)) => match builtins::get(&n) {
                        Some(s) if s.is_number() => return Err(not_a_step(s)),
                        Some(s) if !s.params.is_empty() => {
                            self.at += 1;
                            self.call(s)?
                        }
                        Some(s) if args_follow(self) => {
                            self.at += 1;
                            let Some(input) = self.group_input(false)? else { return Err(format!("{n} takes no arguments: {s}")) };
                            explicit(input, construct(&n, Vec::new()).ok_or_else(|| unimplemented(s))?)
                        }
                        _ => self.pipe()?,
                    },
                    _ => self.pipe()?,
                };
                self.expect(Tok::Close, ")")?;
                Ok(p)
            }
            x => Err(format!("expected a pass or (, found {}", show_tok(x.as_ref()))),
        }
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
        let number_var = var_index(n).is_some();
        let group_var = self.groups.iter().any(|g| g == n);
        if let (Some(Tok::Open), Some(e)) = (self.peek(), self.old_form(1)) {
            return Err(e.into());
        }
        let rhs = match self.number_ahead(number_var) {
            true => self.or().map(Rhs::Num).map_err(|e| match assignable(n) {
                Err(a) if !group_var && !e.contains("unknown variable") => format!("{a}; the right side is not a step either: {e}"),
                _ => e,
            }),
            false => self.rhs_group(number_var, true),
        }?;
        self.no_assign()?;
        match rhs {
            Rhs::Num(e) if number_var => self.assign_number(n, e),
            Rhs::Num(e) if group_var => Err(format!("{n} is a group variable, so it cannot hold a number: {} gives a number", show_expr(&e, 1))),
            Rhs::Num(_) => Err(assignable(n).unwrap_err()),
            Rhs::Group(p) if number_var => Err(format!("{n} is a variable that holds a number, so it cannot be bound to candidates: {} gives candidates", stage(&p))),
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
        let number_fn = builtins::get(n).is_some_and(|s| s.is_number()) || self.number_def(n);
        if k > 0 && matches!(after, Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not)) {
            return match self.param(n) {
                Some(i) => self.params[i].ty == Some(Ty::Num),
                None => number_fn,
            };
        }
        match self.param(n) {
            Some(i) => return self.params[i].ty.map_or(number_var, |t| t == Ty::Num),
            None if number_fn => return true,
            None => {}
        }
        if self.defs.contains_key(n) || self.group_value(n) {
            false
        } else if var_index(n).is_some() {
            resolve(n).is_none() || number_var && !(k > 0 && after == Some(&Tok::Bar))
        } else if ["none", "true", "def", "extern"].contains(&n.as_str()) || builtins::MACROS.contains(&n.as_str()) {
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
        let args = matches!(self.peek_at(2), Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not));
        match self.peek_at(1) {
            Some(Tok::Name(n)) => {
                n == "on"
                    || n == "off"
                    || self.defs.get(n).is_some_and(|d| !d.params.is_empty() || d.run && args)
                    || self.param(n).is_some_and(|i| self.params[i].ty != Some(Ty::Group)) && args
                    || builtins::get(n).is_some_and(|s| !s.params.is_empty() || args)
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
                    if let (Some(Tok::Bar), Some(m)) = (self.peek(), self.peek_at(1)) {
                        return Err(format!("{} gives a number; {} takes candidates: a step that gives a number can only end a pipeline", show_expr(&e, 1), show_tok(Some(m))));
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
            Some(e) => Rhs::Num(Expr::Of(Box::new(e), Box::new(p))),
            None => Rhs::Group(p),
        })
    }

    /// The expression that starts with the atom `e` read already.
    fn expr_from(&mut self, e: Expr) -> Result<Expr, String> {
        self.pending = Some(e);
        let r = self.or();
        self.pending = None;
        r
    }

    /// `n = e` for the variable `n` that holds a number.
    fn assign_number(&mut self, n: &str, e: Expr) -> Result<Pipe, String> {
        let i = assignable(n)?;
        if let Expr::Num(k) = e {
            if is_switch(i) && k == NONE {
                return Err(format!("{n} is a switch: assign it 0 (off) or 1 (on)"));
            }
            crate::sched::check_cap(i, k)?;
        }
        Ok(Pipe::Pass(Pass::Assign(i, e)))
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
            None => !(self.defs.contains_key(n) || known_name(n) || resolve(n).is_some() || defined_builtin(n) || ["none", "true", "def", "extern"].contains(&n.as_str())),
        }
    }

    /// The right side of `n = p` read as a group: a group variable alone, or one step.
    fn bound_step(&mut self) -> Result<Pipe, String> {
        let p = match self.group_var_ahead() {
            true => {
                let u = self.name("a group variable")?;
                self.group_name(&u)?;
                Pipe::Value(u)
            }
            false => self.stage()?,
        };
        if let Pipe::Param(i, _) = p {
            self.params[i].loose += 1;
        }
        self.no_assign()?;
        Ok(p)
    }

    /// `n = p`: the candidates of the step `p` bound to the group variable `n`.
    fn bind(&mut self, n: &str, p: Pipe) -> Result<Pipe, String> {
        if self.defs.contains_key(n) {
            return Err(format!("{n} is defined by let or def @inline and cannot be assigned"));
        } else if known_name(n) || resolve(n).is_some() || defined_builtin(n) || ["none", "def", "extern"].contains(&n) {
            return Err(assignable(n).err().unwrap_or_else(|| format!("{n} cannot be assigned")));
        }
        self.groups.push(n.to_string());
        Ok(Pipe::Bind(n.to_string(), Box::new(p)))
    }

    /// `n` written where a group variable is: an error for a variable that holds a number.
    fn group_name(&mut self, n: &str) -> Result<(), String> {
        if self.param(n).is_some() {
            return self.use_param(n, Ty::Group);
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

    fn end(&self) -> Result<(), String> {
        match self.peek() {
            None => Ok(()),
            t => Err(format!("unexpected {} after the pipeline", show_tok(t))),
        }
    }

    fn at_close(&self) -> bool {
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
    fn arg(&mut self) -> Result<Expr, String> {
        let e = self.arg_of()?;
        self.no_assign()?;
        Ok(e)
    }

    fn arg_of(&mut self) -> Result<Expr, String> {
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(Expr::Not(Box::new(self.arg_of()?)));
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
    fn args(&mut self, s: &Sig, sig: bool) -> Result<Vec<Arg>, String> {
        let f = s.name.as_str();
        let arity = || format!("{f} takes {}: {s}", s.takes());
        let pipes = s.params.iter().filter(|p| p.ty == Ty::Pipe).count();
        let mut args = Vec::new();
        for (i, p) in s.params.iter().enumerate() {
            let whole = pipes == 1 && i + 1 == s.params.len() && p.rep == Rep::One;
            let named = matches!(self.peek(), Some(Tok::Name(_)));
            args.push(match (p.ty, p.rep) {
                (_, Rep::Opt) if self.at_close() => Arg::Absent,
                (Ty::Name | Ty::Group, Rep::Opt) if !named => Arg::Absent,
                (_, Rep::One) if self.at_close() => return Err(arity()),
                (Ty::Num, _) => Arg::Num(self.arg().map_err(|e| if sig { format!("{e}; {f} takes {}: {s}", s.takes()) } else { e })?),
                (Ty::Pipe, _) if matches!(self.peek(), Some(Tok::Num(_))) => return Err(arity()),
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
                (Ty::Name, _) => {
                    let n = self.name(&format!("a name after {f}"))?;
                    self.use_param(&n, p.ty)?;
                    Arg::Name(n)
                }
                (Ty::Pipe, Rep::Many) => Arg::Pipes(self.stages(f, &arity)?),
                (Ty::Pipe, _) if whole => Arg::Pipe(self.pipe()?),
                (Ty::Pipe, _) => {
                    self.no_bar(f)?;
                    Arg::Pipe(self.stage()?)
                }
                _ => unreachable!("{s}"),
            });
        }
        if !self.at_close() && !(s.pipe && self.input_ahead(!s.params.is_empty())) {
            if pipes > 0 {
                self.no_bar(f)?;
            }
            return Err(arity());
        }
        Ok(args)
    }

    /// A call of the function `n` defined with parameters, after its name: a call of a
    /// `def` with the name arguments in place in its body, or an `@inline` body with all
    /// arguments in place.
    fn def_call(&mut self, n: &str, after_bar: bool) -> Result<Pipe, String> {
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
    fn call_of(&self, n: &str, args: Vec<Arg>) -> Result<Pipe, String> {
        let d = &self.defs[n];
        let args: Vec<CallArg> = args
            .into_iter()
            .zip(&d.params)
            .map(|(a, p)| match a {
                Arg::Name(s) if p.ty == Ty::Group => CallArg::Group(s),
                Arg::Name(s) => CallArg::Name(s),
                Arg::Pipe(p) => CallArg::Pipe(p),
                Arg::Num(e) => CallArg::Num(e),
                _ => unreachable!("a parameter of a def is a pipeline, an expression, a group or a name"),
            })
            .collect();
        let open = |s: &str| self.param(s).is_some();
        match &d.def {
            Some(def) => Ok(Pipe::Call(Arc::new(Call { body: instance(def, &args, &open)?, def: def.clone(), args }))),
            None => Subst::new(&d.params, &args, true, true, &open).pipe(&d.pipe),
        }
    }

    /// The macro `(off NAME ...)` or `(on NAME ...)` after its name: one pass for all the
    /// names, since a sequence of them would end their effect.
    fn switches(&mut self, f: &str) -> Result<Pipe, String> {
        let mut ns = Vec::new();
        while !self.at_close() {
            let n = self.name(&format!("a pass name after {f}"))?;
            if self.param(&n).is_some() {
                self.use_param(&n, Ty::Name)?;
                ns.push(intern(&n));
                continue;
            }
            let known = || INNER.iter().chain(&crate::sched::FLAGS).copied().collect::<Vec<_>>().join(",");
            ns.push(crate::sched::switch(&n).ok_or_else(|| format!("unknown {f} name {n}; known: {}", known()))?);
        }
        if ns.is_empty() {
            return Err(format!("{f} needs a pass name"));
        }
        Ok(Pipe::Pass(if f == "off" { Pass::Off(ns) } else { Pass::On(ns) }))
    }

    /// The arguments of a call of the number function `s` after its name: names, and
    /// expressions up to `)`.
    fn number_call(&mut self, s: &'static Sig) -> Result<Expr, String> {
        let f = s.name.as_str();
        let mut args = Vec::new();
        for p in &s.params {
            args.push(match p.ty {
                _ if self.at_close() && p.rep == Rep::Opt => Arg::Absent,
                _ if self.at_close() => return Err(format!("{f} takes {}: {s}", s.takes())),
                Ty::Num => {
                    let outer = std::mem::take(&mut self.no_input);
                    let e = self.or();
                    self.no_input = outer;
                    Arg::Num(e?)
                }
                _ if p.rep == Rep::Opt && !matches!(self.peek(), Some(Tok::Name(_))) => Arg::Absent,
                _ => {
                    let n = self.name("a group variable")?;
                    self.group_name(&n)?;
                    Arg::Name(n)
                }
            });
        }
        let e = number(f, args).ok_or_else(|| unimplemented(s))?;
        if !self.at_close() {
            if let Some(g) = self.group_input(!s.params.is_empty())? {
                return Ok(Expr::Of(Box::new(e), Box::new(g)));
            }
            return Err(format!("{f} takes {}: {s}", s.takes()));
        }
        if self.no_input && !matches!(e, Expr::Size(_)) {
            return Err(no_input(f));
        }
        Ok(e)
    }

    /// The arguments of a call of the function `n` defined whose body is an expression, after
    /// its name, and its input when written.
    fn number_def_call(&mut self, n: &str) -> Result<Expr, String> {
        let d = self.defs[n].clone();
        let sig = self.sig_named(n);
        let mut reading = def_sig(n, &d.params);
        reading.pipe = true;
        let args = self.args(&reading, true).map_err(|e| e.replace(&reading.to_string(), &sig.to_string()))?;
        let step = d.def.as_ref().is_none_or(|d| d.step);
        let input = match step {
            true => self.group_input(!d.params.is_empty())?.map(Box::new),
            false => None,
        };
        if input.is_none() && step && self.no_input {
            return Err(format!("{n} needs its input here: {sig}"));
        }
        self.used.push(n.to_string());
        let Pipe::Call(c) = self.call_of(n, args)? else { unreachable!("a function whose body is an expression is a def") };
        Ok(Expr::Call(c, input))
    }

    fn or(&mut self) -> Result<Expr, String> {
        let mut es = vec![self.and()?];
        while self.peek() == Some(&Tok::Or) {
            self.at += 1;
            es.push(self.and()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { Expr::Or(es) })
    }

    fn and(&mut self) -> Result<Expr, String> {
        let mut es = vec![self.not()?];
        while self.peek() == Some(&Tok::And) {
            self.at += 1;
            es.push(self.not()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { Expr::And(es) })
    }

    fn not(&mut self) -> Result<Expr, String> {
        if self.pending.is_none() && self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(Expr::Not(Box::new(self.not()?)));
        }
        let a = self.sum()?;
        self.no_assign()?;
        let Some(Tok::Cmp(op)) = self.peek() else { return Ok(a) };
        let op = Cmp::ALL.iter().find(|(_, s)| s == op).unwrap().0;
        self.at += 1;
        Ok(Expr::Cmp(op, Box::new(a), Box::new(self.sum()?)))
    }

    fn sum(&mut self) -> Result<Expr, String> {
        let mut a = self.product()?;
        while let Some(Tok::Arith(op @ ('+' | '-'))) = self.peek().cloned() {
            self.at += 1;
            a = Expr::Bin(op, Box::new(a), Box::new(self.product()?));
        }
        Ok(a)
    }

    fn product(&mut self) -> Result<Expr, String> {
        let mut a = self.atom()?;
        while let Some(Tok::Arith(op @ ('*' | '/'))) = self.peek().cloned() {
            self.at += 1;
            a = Expr::Bin(op, Box::new(a), Box::new(self.atom()?));
        }
        Ok(a)
    }

    /// Whether, after the name of a function that gives a number and has no parameters, its
    /// input or the `)` is ahead: `(f)`, `(f t)`, `(f (a | b))`, not `(f < 3)`.
    fn number_input_ahead(&self) -> bool {
        match (self.peek_at(1), self.peek_at(2)) {
            (Some(Tok::Close | Tok::Open), _) => true,
            (Some(Tok::Name(g)), Some(Tok::Close)) => self.input_name(g, false),
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
    fn number_pipe(&mut self) -> Result<Expr, String> {
        let outer = std::mem::take(&mut self.no_input);
        let parts = self.stages_of_pipe();
        self.no_input = outer;
        let (stages, tail) = parts?;
        let p = seq_of(stages);
        let Some(e) = tail else { return Err(format!("({}) gives candidates, not a number: end it with a step that gives a number, as in (a | size)", show(&p))) };
        if outer && !starts_with_value(&p) {
            return Err(format!("({} | {}) needs its input here, outside any step: start it with a value, as in (g | ...)", show(&p), show_expr(&e, 1)));
        }
        Ok(Expr::Of(Box::new(e), Box::new(p)))
    }

    /// A number, a name, `(size R)`, `(same R)`, `(any C)`, `(all C)`, `( expr )` or a
    /// pipeline that ends in a number in parentheses.
    fn atom(&mut self) -> Result<Expr, String> {
        if let Some(e) = self.pending.take() {
            return Ok(e);
        }
        match self.next() {
            Some(Tok::Num(n)) => Ok(Expr::Num(n)),
            Some(Tok::Name(n)) => {
                self.no_assign()?;
                if let Some(i) = self.param(&n) {
                    self.use_param(&n, Ty::Num)?;
                    return Ok(Expr::Param(i, n));
                }
                if self.number_def(&n) && self.defs[&n].params.is_empty() {
                    if self.no_input {
                        return Err(no_input(&n));
                    }
                    self.used.push(n.clone());
                    let def = self.defs[&n].def.clone().unwrap();
                    return Ok(Expr::Call(Arc::new(Call { body: def.body.clone(), def, args: Vec::new() }), None));
                }
                if self.defs.get(&n).is_some_and(|d| d.run) {
                    return Err(format!("{n} gives candidates, not a number: {}; an expression reads variables and number functions", self.sig_named(&n)));
                }
                if self.group_value(&n) {
                    return Err(format!("{n} is a group of candidates, not a number: read it with (size {n}) or a function of it, ({n} ...)"));
                }
                let e = name_expr(&n)?;
                if self.no_input && builtins::get(&n).is_some() {
                    return Err(no_input(&n));
                }
                Ok(e)
            }
            Some(Tok::Open) => {
                // `(size)` and `(size + 1)` are parenthesized expressions, `(size r)` a call.
                let call = match self.peek() {
                    Some(Tok::Name(k)) => builtins::get(k).filter(|s| {
                        let named = matches!(self.peek_at(1), Some(Tok::Name(_))) && self.peek_at(2) == Some(&Tok::Close);
                        let input = matches!(self.peek_at(1), Some(Tok::Name(g)) if self.group_value(g)) && self.peek_at(2) == Some(&Tok::Close) || self.peek_at(1) == Some(&Tok::Open);
                        s.is_number() && (!s.params.is_empty() && (s.required() || named) || input)
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

fn show_tok(t: Option<&Tok>) -> String {
    match t {
        None => "the end".into(),
        Some(t) => match t {
            Tok::Open => "(".into(),
            Tok::Close => ")".into(),
            Tok::Bar => "|".into(),
            Tok::Or => "||".into(),
            Tok::And => "&&".into(),
            Tok::Not => "!".into(),
            Tok::Cmp(c) => c.to_string(),
            Tok::Arith(c) => c.to_string(),
            Tok::Num(n) => n.to_string(),
            Tok::Name(n) => n.clone(),
            Tok::Assign => "=".into(),
            Tok::At => "@".into(),
            Tok::Colon => ":".into(),
        },
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
    } else if let Some(s) = builtins::get(n).filter(|s| s.is_number()) {
        format!("{n} is computed from the candidates and cannot be assigned: {s}")
    } else if let Some(s) = builtins::get(n) {
        format!("{n} is a function and cannot be assigned: {s}")
    } else {
        format!("unknown variable {n}; known: {}", (0..NVARS).map(|i| var(i).name).collect::<Vec<_>>().join(" "))
    })
}

fn known_name(n: &str) -> bool {
    var_index(n).is_some() || builtins::get(n).is_some() || builtins::MACROS.contains(&n)
}

/// `p` on the group value `input` instead of the candidates (`(f x g)`, `g | (f x)`).
fn explicit(input: Pipe, p: Pipe) -> Pipe {
    Pipe::Seq(vec![input, p])
}

/// Whether `p` gives its candidates whatever its input: it starts with a group value.
pub fn starts_with_value(p: &Pipe) -> bool {
    match p {
        Pipe::Value(_) => true,
        Pipe::Seq(ps) => ps.first().is_some_and(starts_with_value),
        Pipe::Call(c) => !c.def.step,
        _ => false,
    }
}

fn not_pipe(s: &Sig) -> String {
    format!("{} is not @pipe, so | cannot give it its input: call it with all its arguments, {s}", s.name)
}

fn no_input(f: &str) -> String {
    format!("{f} needs its input here, outside any step: write it, as in ({f} g)")
}

/// The signature of the function `d` defined: its parameters and its input (`g` where the
/// input is implicit), its result `num` when the body is an expression.
pub fn sig_of(d: &Def) -> Sig {
    let mut sig = def_sig(&d.name, &d.params);
    if let Some(g) = &d.input {
        sig.input.name = g.clone();
    } else if !d.step && !d.params.is_empty() {
        sig.input = sig.params.pop().unwrap();
    }
    sig.pipe = d.step;
    if d.value.is_some() {
        sig.result = Ty::Num;
    }
    sig
}

/// The error for a number function written as a step.
fn not_a_step(s: &Sig) -> String {
    format!("{} gives a number, not candidates: {s}; a step calls a function that gives candidates", s.name)
}

/// The step a name written alone is: a function called without arguments.
fn bare(n: &str) -> Result<Pipe, String> {
    if let Some(s) = builtins::get(n) {
        return match s {
            _ if s.is_number() => Err(not_a_step(s)),
            _ if s.required() => Err(format!("{n} needs parentheses: ({n} ...); {s}")),
            _ => construct(n, vec![Arg::Absent; s.params.len()]).ok_or_else(|| unimplemented(s)),
        };
    }
    // `save/t` for `(save t)`: a function of one name, or a macro.
    let one_name = |h: &str| builtins::get(h).is_some_and(|s| matches!(s.params.as_slice(), [p] if matches!(p.ty, Ty::Group | Ty::Name)));
    Err(match n.split_once('/') {
        _ if n == "extern" => NO_EXTERN.into(),
        _ if builtins::MACROS.contains(&n) => format!("{n} needs parentheses: ({n} ...)"),
        Some((h, r)) if one_name(h) || h == "on" || h == "off" => format!("write {n} as ({h} {r})"),
        _ if var_index(n).is_some() => format!("{n} is a variable, not a step: assign it with {n} = VALUE, or read it in an expression"),
        _ => format!("unknown pass {n}; known: {}", builtins::step_names().join(" ")),
    })
}

/// `e` with a note on a word of `s` such as `time-limit` (outside comments), which reads as a
/// subtraction: the first whose name with `_` is known, else the first not made of numbers.
fn hyphen_hint(e: String, s: &str) -> String {
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
pub fn parse_assign(name: &str, val: &str) -> Result<Pass, String> {
    let go = || {
        assignable(name)?;
        let defs = Defs::new();
        let mut p = Parser::new(lex(val)?, &defs);
        let Pipe::Pass(a) = p.assign(name)? else { unreachable!() };
        p.end()?;
        Ok(a)
    };
    go().map_err(|e| hyphen_hint(e, val))
}

/// The right side of an assignment.
pub fn show_assigned(e: &Expr) -> String {
    show_expr(e, 1)
}

/// Parses `s` in the pipeline language.
pub fn parse(s: &str) -> Result<Pipe, String> {
    parse_with(s, &Defs::new(), &mut Vec::new())
}

/// Parses `s`, where the names of `defs` stand for their pipelines; the names expanded are
/// added to `used`.
pub fn parse_with(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Pipe, String> {
    let go = || {
        let mut p = Parser::new(lex(s)?, defs);
        let pipe = p.pipe()?;
        p.end()?;
        Ok((pipe, p.used))
    };
    let (pipe, names) = go().map_err(|e| hyphen_hint(e, s))?;
    used.extend(names);
    Ok(pipe)
}

/// Whether `name` is a function the Rust code defines and calls, which `(def (NAME) p)`
/// (written also `NAME=p`) replaces: `pipeline`, `prepass`, `polish`, `rewrite`, `simba`,
/// `sub/NAME`.
pub fn defined_builtin(name: &str) -> bool {
    ["pipeline", "prepass", "polish", "rewrite", "simba"].contains(&name) || name.strip_prefix("sub/").is_some_and(|n| crate::sched::SUBS.iter().any(|(s, _)| *s == n))
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
                    let t = p.name("a type after :")?;
                    Some(match t.as_str() {
                        "pipe" => Ty::Pipe,
                        "group" => Ty::Group,
                        "num" => Ty::Num,
                        "name" => Ty::Name,
                        _ => return Err(format!("unknown type {t} of parameter {n}; known: pipe group num name")),
                    })
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
    if piped && (params.is_empty() || types.last().unwrap().is_some_and(|t| t != Ty::Group)) {
        return Err(format!("{what}: the last parameter of an @pipe function is its input, a group"));
    }
    let function = builtins::get(&name);
    let replaces = kind == DefKind::Run && defined_builtin(&name);
    if defined_builtin(&name) && !replaces {
        return Err(format!("{what}: {name} is a function the Rust code calls, replaced only by (def ({name}) p) or {name}=p"));
    }
    if !replaces && (function.is_some_and(|s| !s.is_number()) || resolve(&name).is_some() || builtins::MACROS.contains(&name.as_str()) || name == "extern" || name == "def") {
        return Err(format!("{what}: the name of a pass, form or macro"));
    }
    if !replaces && (var_index(&name).is_some() || function.is_some() || name == "none") {
        return Err(format!("{what}: the name of a variable or function"));
    }
    if kind == DefKind::Run && name.starts_with("sub/") && !replaces {
        let names: Vec<&str> = crate::sched::SUBS.iter().map(|(n, _)| *n).collect();
        return Err(format!("{what}: unknown sub/NAME; known: {}", names.join(" ")));
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
        let taken = var_index(n).is_some() || builtins::get(n).is_some() || builtins::MACROS.contains(&n.as_str()) || resolve(n).is_some() || defined_builtin(n) || defs.contains_key(n);
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
            p.no_input = true;
            let e = p.or()?;
            p.no_input = false;
            kind = DefKind::Run;
            Some(e)
        }
        false => None,
    };
    let (mut pipe, flat, tail) = match value {
        Some(_) => (Pipe::Pass(Pass::id()), false, None),
        None => {
            let (stages, tail) = p.stages_of_pipe()?;
            let flat = kind != DefKind::Run && stages.len() > 1;
            (seq_of(stages), flat, tail)
        }
    };
    if let Pipe::Param(i, _) = pipe {
        p.params[i].loose += 1;
    }
    p.expect(Tok::Close, ")")?;
    p.end()?;
    let starts = starts_with_value(&pipe);
    if piped && value.is_none() && !starts {
        return Err(format!("{what}: the body of an @pipe function starts with a value, as in {} | ..., or is an expression", input.as_deref().unwrap()));
    }
    let step = piped || value.is_none() && !starts;
    if let Some(e) = tail {
        if kind != DefKind::Run {
            return Err(format!("{what}: a function that gives a number is a run of its own, so it cannot be @inline or a let"));
        }
        value = Some(Expr::Of(Box::new(e), Box::new(std::mem::replace(&mut pipe, Pipe::Pass(Pass::id())))));
    }
    let mut params = std::mem::take(&mut p.params);
    if piped {
        params.pop();
    }
    let notes = params
        .iter()
        .filter(|u| !u.annotated && u.ty == Some(Ty::Pipe) && u.loose == u.uses)
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
    Ok(Definition { name, kind, params, pipe, flat, input, step, value, notes })
}

/// The signature of a function `(def (NAME PARAM ...) p)`: its parameters, then the
/// candidates.
pub fn def_sig(name: &str, params: &[Param]) -> Sig {
    Sig {
        name: name.into(),
        params: params.to_vec(),
        input: Param { name: "g".into(), ty: Ty::Group, rep: Rep::One },
        result: Ty::Group,
        pipe: true,
        bookkeeping: false,
        simplify_only: false,
        uncounted: false,
        doc: String::new(),
    }
}

fn def_head(d: &Def) -> String {
    let params = d.params.iter().map(|p| if p.ty == Ty::Group { format!("{}:group", p.name) } else { p.name.clone() });
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
        Some(Expr::Of(e, p)) => return show_steps(e, p),
        Some(e) => return show_expr(e, 1),
        None => {}
    }
    match &*d.body {
        Pipe::Seq(ps) if d.inline && !d.flat && ps.len() > 1 => format!("({s})"),
        _ => s,
    }
}

/// The body of a call of an `@inline` function with its pipeline arguments in place, as the
/// checks of registers and assignments see it.
pub fn expand(c: &Call) -> Pipe {
    let pipes = c.args.iter().map(|a| if let CallArg::Pipe(q) = a { Some(q) } else { None }).collect();
    let s = Subst { names: Vec::new(), owned: Vec::new(), pipes, open: &|_| false };
    s.pipe(&c.body).expect("no name to put in place")
}

/// The body of a call of `def` with `args`: its name arguments in place (`open` as in
/// `Subst`).
fn instance(def: &Def, args: &[CallArg], open: &dyn Fn(&str) -> bool) -> Result<Arc<Pipe>, String> {
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
            let save = Pipe::Pass(Pass::Save(g));
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
    fn new(params: &'s [Param], args: &'s [CallArg], pipes: bool, groups: bool, open: &'s dyn Fn(&str) -> bool) -> Subst<'s> {
        let mut s = Subst { names: Vec::new(), owned: Vec::new(), pipes: Vec::new(), open };
        for (p, a) in params.iter().zip(args) {
            match a {
                CallArg::Name(n) => {
                    s.names.push((&p.name, n));
                    s.pipes.push(None);
                }
                CallArg::Group(n) => {
                    if groups {
                        s.names.push((&p.name, n));
                    }
                    s.pipes.push(None);
                }
                CallArg::Pipe(q) => s.pipes.push(pipes.then_some(q)),
                CallArg::Num(_) => s.pipes.push(None),
            }
        }
        s
    }

    fn name(&self, n: &str) -> String {
        match self.owned.iter().find(|(p, _)| p == n) {
            Some((_, a)) => a.clone(),
            None => self.names.iter().find(|(p, _)| *p == n).map_or(n, |(_, a)| a).to_string(),
        }
    }

    fn switch(&self, n: &'static str, f: &str) -> Result<&'static str, String> {
        match self.names.iter().find(|(p, _)| *p == n) {
            None => Ok(n),
            Some((_, a)) if (self.open)(a) => Ok(intern(a)),
            Some((_, a)) => crate::sched::switch(a).ok_or_else(|| {
                let known = INNER.iter().chain(&crate::sched::FLAGS).copied().collect::<Vec<_>>().join(",");
                format!("unknown {f} name {a} (the argument for {n}); known: {known}")
            }),
        }
    }

    fn expr(&self, e: &Expr) -> Result<Expr, String> {
        let b = |e: &Expr| self.expr(e).map(Box::new);
        let all = |cs: &[Expr]| cs.iter().map(|c| self.expr(c)).collect::<Result<Vec<_>, String>>();
        Ok(match e {
            Expr::Size(r) => Expr::Size(self.name(r)),
            Expr::Same(r) => Expr::Same(self.name(r)),
            Expr::Of(e, p) => Expr::Of(b(e)?, Box::new(self.pipe(p)?)),
            Expr::Call(c, input) => Expr::Call(Arc::new(self.call(c)?), input.as_ref().map(|p| self.pipe(p).map(Box::new)).transpose()?),
            Expr::Not(c) => Expr::Not(b(c)?),
            Expr::Any(c) => Expr::Any(b(c)?),
            Expr::All(c) => Expr::All(b(c)?),
            Expr::And(cs) => Expr::And(all(cs)?),
            Expr::Or(cs) => Expr::Or(all(cs)?),
            Expr::Cmp(op, x, y) => Expr::Cmp(*op, b(x)?, b(y)?),
            Expr::Bin(op, x, y) => Expr::Bin(*op, b(x)?, b(y)?),
            Expr::Num(_) | Expr::Feature(_) | Expr::Is(_) | Expr::Var(_) | Expr::Param(..) => e.clone(),
        })
    }

    fn pass(&self, p: &Pass) -> Result<Pass, String> {
        Ok(match p {
            Pass::Save(r) => Pass::Save(self.name(r)),
            Pass::Load(r) => Pass::Load(self.name(r)),
            Pass::Label(r) => Pass::Label(self.name(r)),
            Pass::Clear(r) => Pass::Clear(self.name(r)),
            Pass::Note(r) => Pass::Note(self.name(r)),
            Pass::TakeMin(r) => Pass::TakeMin(self.name(r)),
            Pass::Egglog(l) => match l.strip_prefix("egglog/") {
                Some(l) => Pass::Egglog(format!("egglog/{}", self.name(l))),
                None => p.clone(),
            },
            Pass::Off(ns) => Pass::Off(ns.iter().map(|n| self.switch(n, "off")).collect::<Result<_, _>>()?),
            Pass::On(ns) => Pass::On(ns.iter().map(|n| self.switch(n, "on")).collect::<Result<_, _>>()?),
            Pass::Assign(i, e) => Pass::Assign(*i, self.expr(e)?),
            Pass::Set(_) | Pass::Term { .. } => p.clone(),
        })
    }

    fn pipe(&self, p: &Pipe) -> Result<Pipe, String> {
        let all = |ps: &[Pipe]| ps.iter().map(|q| self.pipe(q)).collect::<Result<Vec<_>, String>>();
        let b = |q: &Pipe| self.pipe(q).map(Box::new);
        Ok(match p {
            Pipe::Pass(q) => Pipe::Pass(self.pass(q)?),
            Pipe::Seq(ps) => Pipe::Seq(all(ps)?),
            Pipe::Union(ps) => Pipe::Union(all(ps)?),
            Pipe::First(ps) => Pipe::First(all(ps)?),
            Pipe::Best(k, ps) => Pipe::Best(self.expr(k)?, all(ps)?),
            Pipe::Fix(n, q) => Pipe::Fix(self.expr(n)?, b(q)?),
            Pipe::Wins(n, q) => Pipe::Wins(self.expr(n)?, b(q)?),
            Pipe::If(c, x, y) => Pipe::If(self.expr(c)?, b(x)?, b(y)?),
            Pipe::Retry(c, x, y) => Pipe::Retry(self.expr(c)?, b(x)?, b(y)?),
            Pipe::Smallest(m) => smallest(self.pipe(&m.source)?),
            Pipe::Scope(q) => Pipe::Scope(b(q)?),
            Pipe::Regions(q) => Pipe::Regions(b(q)?),
            Pipe::Again(q) => Pipe::Again(b(q)?),
            Pipe::Tag(n, q) => Pipe::Tag(self.name(n), b(q)?),
            Pipe::Cand(n, q) => Pipe::Cand(self.name(n), b(q)?),
            Pipe::Smaller(n, q) => Pipe::Smaller(self.name(n), b(q)?),
            Pipe::Filter(c) => Pipe::Filter(self.expr(c)?),
            Pipe::Param(i, _) => self.pipes.get(*i).copied().flatten().map_or_else(|| p.clone(), Pipe::clone),
            Pipe::Bind(n, q) => Pipe::Bind(self.name(n), b(q)?),
            Pipe::Value(n) => Pipe::Value(self.name(n)),
            Pipe::Call(c) => Pipe::Call(Arc::new(self.call(c)?)),
        })
    }

    fn call(&self, c: &Call) -> Result<Call, String> {
        let args = c
            .args
            .iter()
            .map(|a| {
                Ok(match a {
                    CallArg::Name(n) => CallArg::Name(self.name(n)),
                    CallArg::Group(n) => CallArg::Group(self.name(n)),
                    CallArg::Pipe(q) => CallArg::Pipe(self.pipe(q)?),
                    CallArg::Num(e) => CallArg::Num(self.expr(e)?),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let renamed = c.def.inline && c.def.input.is_some() || args.iter().zip(&c.args).any(|(a, b)| matches!((a, b), (CallArg::Name(x), CallArg::Name(y)) if x != y));
        let body = if renamed { instance(&c.def, &args, self.open)? } else { c.body.clone() };
        Ok(Call { def: c.def.clone(), args, body })
    }
}

/// The macro `(smallest p)`: `(clear s) | p' | (take_min s)`, `s` a note register no other
/// `smallest` and no name a user writes has, `p'` being `p` with `(note s)` after each step
/// in its text that computes candidates (`crate::pipe::computes`, and a pipeline parameter),
/// also in the pipeline arguments of calls and in the bodies of `@inline` calls, but not in
/// the bodies of other calls.
pub fn smallest(p: Pipe) -> Pipe {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let s = format!("smallest#{}", NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
    let (body, scoped) = match &p {
        Pipe::Seq(ps) => (noted_stages(ps, &s, false), true),
        q => (noted_stage(q, &s, false), false),
    };
    let mut steps = vec![Pipe::Pass(Pass::Clear(s.clone()))];
    steps.extend(body);
    steps.push(Pipe::Pass(Pass::TakeMin(s)));
    Pipe::Smallest(Box::new(crate::sched::Smallest { source: p, steps, scoped }))
}

/// `p` with `(note s)` inside and after it (`smallest`); `inline` inside the body of an
/// `@inline` call, where a parameter's argument has the notes of the text it is written in.
fn noted_stage(p: &Pipe, s: &str, inline: bool) -> Vec<Pipe> {
    let q = noted(p, s, inline);
    if crate::pipe::computes(p) || matches!(p, Pipe::Param(..)) && !inline { vec![q, Pipe::Pass(Pass::Note(s.into()))] } else { vec![q] }
}

fn noted_stages(ps: &[Pipe], s: &str, inline: bool) -> Vec<Pipe> {
    ps.iter().flat_map(|p| noted_stage(p, s, inline)).collect()
}

/// `noted_stage` as one stage.
fn noted_one(p: &Pipe, s: &str, inline: bool) -> Pipe {
    let mut ps = noted_stage(p, s, inline);
    if ps.len() == 1 { ps.pop().unwrap() } else { Pipe::Seq(ps) }
}

/// `p` with `(note s)` after the steps inside it.
fn noted(p: &Pipe, s: &str, inline: bool) -> Pipe {
    let one = |q: &Pipe| Box::new(noted_one(q, s, inline));
    let all = |ps: &[Pipe]| ps.iter().map(|q| noted_one(q, s, inline)).collect();
    let e = |x: &Expr| noted_expr(x, s, inline);
    match p {
        Pipe::Pass(Pass::Assign(i, x)) => Pipe::Pass(Pass::Assign(*i, e(x))),
        Pipe::Filter(x) => Pipe::Filter(e(x)),
        Pipe::Pass(_) | Pipe::Param(..) | Pipe::Value(_) => p.clone(),
        Pipe::Seq(ps) => Pipe::Seq(noted_stages(ps, s, inline)),
        Pipe::Union(ps) => Pipe::Union(all(ps)),
        Pipe::First(ps) => Pipe::First(all(ps)),
        Pipe::Best(k, ps) => Pipe::Best(e(k), all(ps)),
        Pipe::Fix(n, q) => Pipe::Fix(e(n), one(q)),
        Pipe::Wins(n, q) => Pipe::Wins(e(n), one(q)),
        Pipe::If(c, a, b) => Pipe::If(e(c), one(a), one(b)),
        Pipe::Retry(c, a, b) => Pipe::Retry(e(c), one(a), one(b)),
        Pipe::Scope(q) => Pipe::Scope(one(q)),
        Pipe::Regions(q) => Pipe::Regions(one(q)),
        Pipe::Again(q) => Pipe::Again(one(q)),
        Pipe::Tag(n, q) => Pipe::Tag(n.clone(), one(q)),
        Pipe::Cand(n, q) => Pipe::Cand(n.clone(), one(q)),
        Pipe::Smaller(n, q) => Pipe::Smaller(n.clone(), one(q)),
        Pipe::Bind(n, q) => Pipe::Bind(n.clone(), one(q)),
        Pipe::Smallest(m) => {
            let steps = noted_stages(&m.steps, s, inline);
            Pipe::Smallest(Box::new(crate::sched::Smallest { source: m.source.clone(), steps, scoped: m.scoped }))
        }
        Pipe::Call(c) => {
            let body = if c.def.inline { Arc::new(noted_one(&c.body, s, true)) } else { c.body.clone() };
            Pipe::Call(Arc::new(Call { def: c.def.clone(), args: noted_args(&c.args, s, inline), body }))
        }
    }
}

fn noted_args(args: &[CallArg], s: &str, inline: bool) -> Vec<CallArg> {
    args.iter()
        .map(|a| match a {
            CallArg::Pipe(q) => CallArg::Pipe(noted_one(q, s, inline)),
            CallArg::Num(x) => CallArg::Num(noted_expr(x, s, inline)),
            a => a.clone(),
        })
        .collect()
}

/// `e` with `(note s)` after the steps of the pipelines inside it.
fn noted_expr(e: &Expr, s: &str, inline: bool) -> Expr {
    let b = |x: &Expr| Box::new(noted_expr(x, s, inline));
    match e {
        Expr::Of(x, p) if !matches!(**p, Pipe::Value(_)) => Expr::Of(b(x), Box::new(noted_one(p, s, inline))),
        Expr::Of(x, p) => Expr::Of(b(x), p.clone()),
        Expr::Call(c, input) => {
            let input = input.as_ref().map(|p| Box::new(noted_one(p, s, inline)));
            Expr::Call(Arc::new(Call { def: c.def.clone(), args: noted_args(&c.args, s, inline), body: c.body.clone() }), input)
        }
        Expr::Not(x) => Expr::Not(b(x)),
        Expr::Any(x) => Expr::Any(b(x)),
        Expr::All(x) => Expr::All(b(x)),
        Expr::And(xs) => Expr::And(xs.iter().map(|x| noted_expr(x, s, inline)).collect()),
        Expr::Or(xs) => Expr::Or(xs.iter().map(|x| noted_expr(x, s, inline)).collect()),
        Expr::Cmp(op, x, y) => Expr::Cmp(*op, b(x), b(y)),
        Expr::Bin(op, x, y) => Expr::Bin(*op, b(x), b(y)),
        Expr::Num(_) | Expr::Feature(_) | Expr::Is(_) | Expr::Size(_) | Expr::Same(_) | Expr::Var(_) | Expr::Param(..) => e.clone(),
    }
}

/// Whether `e` runs steps: a pipeline other than a group value inside it.
pub fn has_steps(e: &Expr) -> bool {
    let mut steps = false;
    e.each(&mut |p| steps |= !matches!(p, Pipe::Value(_)));
    steps
}

/// `s` for as long as the program runs: the name of a parameter written where a switch is,
/// which `Pass::Off` and `Pass::On` hold until a call puts the switch in its place.
fn intern(s: &str) -> &'static str {
    static NAMES: std::sync::Mutex<Vec<&'static str>> = std::sync::Mutex::new(Vec::new());
    let mut names = NAMES.lock().unwrap();
    if let Some(n) = names.iter().find(|n| **n == s) {
        return n;
    }
    let n: &'static str = Box::leak(s.to_string().into_boxed_str());
    names.push(n);
    n
}

/// Whether `s` looks like the old `seq(a,b)` syntax, for an error message: a name directly
/// followed by `(`.
pub fn is_old_syntax(s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    cs.windows(2).any(|w| name_char(w[0]) && w[1] == '(')
}

/// `e` where an operand of precedence `need` stands: `||` is 1, `&&` 2, `!` 3, a comparison
/// 4, `+ -` 5, `* /` 6, the rest 7.
fn show_expr(e: &Expr, need: u8) -> String {
    let (s, prec) = match e {
        Expr::Num(NONE) => ("none".into(), 7),
        Expr::Num(n) => (n.to_string(), 7),
        Expr::Feature(i) => (FEATURES[*i].to_string(), 7),
        Expr::Is(i) => (CONDS[*i].to_string(), 7),
        Expr::Size(r) => (format!("(size {r})"), 7),
        Expr::Same(r) => (format!("(same {r})"), 7),
        Expr::Var(i) => (var(*i).name.to_string(), 7),
        Expr::Param(_, n) => (n.clone(), 7),
        Expr::Of(e, p) => match &**p {
            Pipe::Value(r) if matches!(**e, Expr::Is(_) | Expr::Same(_) | Expr::Any(_) | Expr::All(_)) || matches!(**e, Expr::Feature(i) if i != 0) => {
                let s = show_expr(e, 7);
                let inner = s.strip_prefix('(').and_then(|s| s.strip_suffix(')')).unwrap_or(&s);
                (format!("({inner} {r})"), 7)
            }
            _ => (format!("({})", show_steps(e, p)), 7),
        },
        Expr::Call(c, input) => {
            let args = c.args.iter().map(show_call_arg).chain(input.as_deref().map(stage));
            let all: Vec<String> = args.collect();
            (if all.is_empty() { c.def.name.clone() } else { form(&c.def.name, &all) }, 7)
        }
        Expr::Any(c) => (format!("(any {})", show_expr(c, 1)), 7),
        Expr::All(c) => (format!("(all {})", show_expr(c, 1)), 7),
        Expr::Not(c) => (format!("!{}", show_expr(c, 7)), 3),
        Expr::And(cs) => (cs.iter().map(|c| show_expr(c, 3)).collect::<Vec<_>>().join(" && "), 2),
        Expr::Or(cs) => (cs.iter().map(|c| show_expr(c, 2)).collect::<Vec<_>>().join(" || "), 1),
        Expr::Cmp(op, a, b) => (format!("{} {} {}", show_expr(a, 5), op.symbol(), show_expr(b, 5)), 4),
        Expr::Bin(op, a, b) => {
            let prec = if matches!(op, '+' | '-') { 5 } else { 6 };
            (format!("{} {op} {}", show_expr(a, prec), show_expr(b, prec + 1)), prec)
        }
    };
    if prec < need { format!("({s})") } else { s }
}

/// The steps `p` and the number `e` of them, `p | e`.
fn show_steps(e: &Expr, p: &Pipe) -> String {
    format!("{} | {}", show(p), show_expr(e, 1))
}

/// `e` as an argument of a form.
fn show_arg(e: &Expr) -> String {
    match e {
        Expr::Not(x) => format!("!{}", show_arg(x)),
        e => show_expr(e, 7),
    }
}

/// `p` written as a stage: a sequence in parentheses.
pub fn show_stage(p: &Pipe) -> String {
    stage(p)
}

fn stage(p: &Pipe) -> String {
    match p {
        Pipe::Seq(ps) if ps.len() > 1 => format!("({})", show(p)),
        _ => show(p),
    }
}

fn form(head: &str, args: &[String]) -> String {
    format!("({head} {})", args.join(" "))
}

fn show_pass(p: &Pass) -> String {
    if let Pass::Assign(i, v) = p {
        return format!("{} = {}", var(*i).name, show_assigned(v));
    }
    let n = p.name();
    match n.split_once('/') {
        Some((h @ ("save" | "load" | "label" | "clear" | "note" | "take_min" | "off" | "on" | "egglog"), r)) => form(h, &[r.to_string()]),
        _ => n,
    }
}

fn is_id(p: &Pipe) -> bool {
    *p == Pipe::Pass(Pass::id())
}

/// `p` in the pipeline language, on one line.
pub fn show(p: &Pipe) -> String {
    let stages = |ps: &[Pipe]| ps.iter().map(stage).collect::<Vec<_>>();
    let with = |head: Vec<String>, p: &Pipe| {
        let mut a = head;
        a.push(show(p));
        a
    };
    match p {
        Pipe::Pass(p) => show_pass(p),
        Pipe::Seq(ps) if ps.len() > 1 => stages(ps).join(" | "),
        Pipe::Seq(ps) => form("seq", &stages(ps)),
        Pipe::Union(ps) => form("union", &stages(ps)),
        Pipe::First(ps) => form("first", &stages(ps)),
        Pipe::Best(k, ps) => form("best", &[vec![show_arg(k)], stages(ps)].concat()),
        Pipe::Fix(n, p) => form("fix", &with(vec![show_arg(n)], p)),
        Pipe::Wins(n, p) => form("wins", &with(vec![show_arg(n)], p)),
        Pipe::If(c, a, b) if is_id(b) => form("if", &[show_arg(c), stage(a)]),
        Pipe::If(c, a, b) => form("if", &[show_arg(c), stage(a), stage(b)]),
        Pipe::Retry(c, a, b) => form("retry", &[show_arg(c), stage(a), stage(b)]),
        Pipe::Smallest(m) => form("smallest", &[show(&m.source)]),
        Pipe::Scope(p) => form("scope", &[show(p)]),
        Pipe::Regions(p) => form("regions", &[show(p)]),
        Pipe::Again(p) => form("again", &[show(p)]),
        Pipe::Tag(n, p) => form("tag", &with(vec![n.clone()], p)),
        Pipe::Cand(n, p) => form("cand", &with(vec![n.clone()], p)),
        Pipe::Smaller(n, p) => form("smaller", &with(vec![n.clone()], p)),
        Pipe::Filter(c) => form("filter", &[show_arg(c)]),
        Pipe::Call(c) if c.args.is_empty() => c.def.name.clone(),
        Pipe::Call(c) => form(&c.def.name, &c.args.iter().map(show_call_arg).collect::<Vec<_>>()),
        Pipe::Param(_, n) | Pipe::Value(n) => n.clone(),
        Pipe::Bind(n, q) => format!("{n} = {}", bound(q, show(q))),
    }
}

/// The right side `q` of a `Bind`, written `s`, as a stage: an assignment in parentheses.
fn bound(q: &Pipe, s: String) -> String {
    match q {
        Pipe::Seq(ps) if ps.len() > 1 => format!("({s})"),
        Pipe::Bind(..) | Pipe::Pass(Pass::Assign(..)) => format!("({s})"),
        _ => s,
    }
}

const WIDTH: usize = 100;

/// `p` in the pipeline language over several lines, each at most about `WIDTH` wide, nested
/// pipelines indented.
pub fn pretty(p: &Pipe) -> String {
    pretty_at(p, 0)
}

fn pretty_at(p: &Pipe, indent: usize) -> String {
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
        Pipe::Union(ps) => nested("union", vec![], many(ps)),
        Pipe::First(ps) => nested("first", vec![], many(ps)),
        Pipe::Best(k, ps) => nested("best", vec![show_arg(k)], many(ps)),
        Pipe::Fix(n, q) => nested("fix", vec![show_arg(n)], vec![(q, false)]),
        Pipe::Wins(n, q) => nested("wins", vec![show_arg(n)], vec![(q, false)]),
        Pipe::If(c, a, b) if is_id(b) => nested("if", vec![show_arg(c)], vec![(a, true)]),
        Pipe::If(c, a, b) => nested("if", vec![show_arg(c)], vec![(a, true), (b, true)]),
        Pipe::Retry(c, a, b) => nested("retry", vec![show_arg(c)], vec![(a, true), (b, true)]),
        Pipe::Smallest(m) => nested("smallest", vec![], vec![(&m.source, false)]),
        Pipe::Scope(q) => nested("scope", vec![], vec![(q, false)]),
        Pipe::Regions(q) => nested("regions", vec![], vec![(q, false)]),
        Pipe::Again(q) => nested("again", vec![], vec![(q, false)]),
        Pipe::Tag(n, q) => nested("tag", vec![n.clone()], vec![(q, false)]),
        Pipe::Cand(n, q) => nested("cand", vec![n.clone()], vec![(q, false)]),
        Pipe::Smaller(n, q) => nested("smaller", vec![n.clone()], vec![(q, false)]),
        Pipe::Call(c) if !c.args.is_empty() => {
            let names = c.args.iter().take_while(|a| matches!(a, CallArg::Name(_) | CallArg::Num(_))).count();
            let pipes: Vec<(&Pipe, bool)> = c.args[names..].iter().filter_map(|a| if let CallArg::Pipe(q) = a { Some((q, true)) } else { None }).collect();
            if names + pipes.len() < c.args.len() {
                return one;
            }
            nested(&c.def.name, c.args[..names].iter().map(show_call_arg).collect(), pipes)
        }
        Pipe::Bind(n, q) => format!("{n} = {}", bound(q, pretty_at(q, indent + 2))),
        Pipe::Pass(_) | Pipe::Filter(_) | Pipe::Call(_) | Pipe::Param(..) | Pipe::Value(_) => one,
    }
}

fn show_call_arg(a: &CallArg) -> String {
    match a {
        CallArg::Name(n) | CallArg::Group(n) => n.clone(),
        CallArg::Pipe(p) => stage(p),
        CallArg::Num(e) => show_arg(e),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sched::Passes;

    #[test]
    fn defaults_read_back() {
        let d = Passes::default();
        for p in [&d.pipeline, &d.prepass, &d.polish, &d.rewrite, &d.simba] {
            assert_eq!(&parse(&show(p)).unwrap(), p, "{}", show(p));
            assert_eq!(&parse(&pretty(p)).unwrap(), p, "{}", pretty(p));
        }
    }

    #[test]
    fn forms_and_conditions() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        same("lowbits | rewrite | polish", "(seq lowbits rewrite polish)");
        same("(if mixed rewrite)", "(if mixed rewrite id)");
        same("(if (!minimal || tiny) (rewrite | polish))", "(if (!minimal || (tiny)) (seq rewrite polish) id)");
        same("(filter (mul >= 4 && vars < 3))", "(filter ((mul >= 4) && (vars < 3)))");
        assert_eq!(parse("(off lowbits relate)").unwrap(), Pipe::Pass(Pass::Off(vec!["lowbits", "relate"])));
        same("(fix restarts prepass | egglog)", "(fix restarts (prepass | egglog))");
        same("# comment
(best 2 rewrite (scope relate)) # more", "(best 2 rewrite (scope relate))");
        let p = parse("(filter (size > (size f) * 3/4 || (same r)))").unwrap();
        let Pipe::Filter(Expr::Or(cs)) = &p else { panic!("{p:?}") };
        assert_eq!(cs[1], Expr::Same("r".into()));
        let three_quarters = Expr::Bin('/', Box::new(Expr::Bin('*', Box::new(Expr::Size("f".into())), Box::new(Expr::Num(3)))), Box::new(Expr::Num(4)));
        assert_eq!(cs[0], Expr::Cmp(Cmp::Gt, Box::new(Expr::Feature(0)), Box::new(three_quarters)));
        for ok in [
            "(if !(minimal && tiny) id)",
            "(filter (any (mul >= 2)))",
            "(filter (all !tiny && size * 2 + 1 <= (size t) - vars))",
            "(fix (restarts - 1) prepass)",
            "(best (keep + 1) id)",
            "(if (size < split_size) id)",
            "(wins (2 * 4) id)",
            "(filter !(same r))",
            "(if mul id)",
            "(filter (mul + tiny))",
            "(fix mixed id)",
            "(if ((mul >= 4) + 1) id)",
            "(best (size > 3) id)",
            "(if (none > size) id)",
            "(fix (time_limit / 2 - (mul < 1)) id)",
        ] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
        }
        assert_eq!(show(&parse("(if !(mul < 1 || tiny) id)").unwrap()), "(if !(mul < 1 || tiny) id)");
        assert_eq!(show(&parse("(fix (2 * (keep + 1)) id)").unwrap()), "(fix (2 * (keep + 1)) id)");
        for bad in [
            "nope",
            "(if mixed a | b)",
            "(union rewrite | relate)",
            "(fix many id)",
            "(if nope id)",
            "(off nope)",
            "seq",
            "(retry mixed id)",
            "rewrite)",
            "seq(rewrite,polish)",
        ] {
            assert!(parse(bad).is_err(), "{bad}");
        }
        assert!(is_old_syntax("seq(a,b)") && !is_old_syntax("(seq a b)"));
    }

    #[test]
    fn numbers_and_hyphens() {
        let p = parse("split_runs = size-mul").unwrap();
        assert_eq!(p, Pipe::Pass(Pass::Assign(var_index("split_runs").unwrap(), Expr::Bin('-', Box::new(Expr::Feature(0)), Box::new(Expr::Feature(3))))));
        assert_eq!(parse("(if (restarts-1 > size-mul) id)").unwrap(), parse("(if (restarts - 1 > size - mul) id)").unwrap());
        assert_eq!(parse("(if 1 none id)").unwrap(), Pipe::If(Expr::Num(1), Box::new(Pipe::Pass(resolve("none").unwrap())), Box::new(Pipe::Pass(Pass::id()))));
        for ok in ["(if 1 none rewrite)", "(filter !0)", "(if (any 1) none)", "(if (1 && mixed) id)"] {
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
        let assign = |n: &str, v: Expr| Pipe::Pass(Pass::Assign(at(n), v));
        assert_eq!(parse("split_runs = 4").unwrap(), assign("split_runs", Expr::Num(4)));
        same("split_runs=4 | rewrite", "split_runs = 4 | rewrite");
        same("(split_runs=4)", "split_runs   =   4");
        let p = parse("split_runs = vars * 2 + 1 | split_bits").unwrap();
        let rhs = Expr::Bin('+', Box::new(Expr::Bin('*', Box::new(Expr::Feature(1)), Box::new(Expr::Num(2)))), Box::new(Expr::Num(1)));
        assert_eq!(p, Pipe::Seq(vec![assign("split_runs", rhs), parse("split_bits").unwrap()]));
        assert_eq!(parse("rewrites = none").unwrap(), assign("rewrites", Expr::Num(NONE)));
        assert_eq!(parse("relate = 0").unwrap(), assign("relate", Expr::Num(0)));
        assert_eq!(parse("cut = 1").unwrap(), assign("cut", Expr::Num(1)));
        assert_eq!(parse("split_runs = none + 1").unwrap(), assign("split_runs", Expr::Bin('+', Box::new(Expr::Num(NONE)), Box::new(Expr::Num(1)))));
        assert_eq!(parse("split_runs = mixed").unwrap(), assign("split_runs", Expr::Is(CONDS.iter().position(|c| *c == "mixed").unwrap())));
        same("(if mixed split_runs = 3)", "(if mixed (split_runs = 3))");
        same("(union split_runs = 3 rewrite)", "(union (split_runs = 3) rewrite)");
        same("semi_leaves = split_runs - 1 | rewrite", "semi_leaves = (split_runs - 1) | rewrite");
        for ok in [
            "split_runs = 4 | rewrite",
            "split_runs = vars * 2 | split_bits",
            "rewrites = none | relate = 0 | cut = 1 | time_limit = (size t) * 10 | rewrite",
            "(if mixed semi_leaves = 2 (time_limit = none | rewrite))",
            "(best 1 (bit_split_budget = cand_bit_splits | rewrite) (time_limit = time_limit / 2 | rewrite))",
            "semi/shapes = 0 | rewrite",
            "keep = 1 | restarts = restarts - 1 | iter_limit = 3 | match_limit = 8 | prove_minimal = 0 | rewrite",
            "(if (rerun_input && printed && !relate) id)",
            "split_runs = relate + cut | rewrite",
        ] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
            assert_eq!(parse(&pretty(&p)).unwrap(), p, "{ok}: {}", pretty(&p));
        }
        assert_eq!(show(&parse("split_runs=vars*2|rewrite").unwrap()), "split_runs = vars * 2 | rewrite");
        for (bad, msg) in [
            ("(if (size = 3) id)", "compare with =="),
            ("(filter (vars = 2 || mul > 1))", "compare with =="),
            ("(if size = 3 id)", "compare with =="),
            ("(fix n = 3 id)", "compare with =="),
            ("nope = 1", "unknown variable nope"),
            ("size = 1", "cannot be assigned"),
            ("mixed = 1", "cannot be assigned"),
            ("minimal = 1", "prove_minimal"),
            ("relate = none", "switch"),
            ("split_runs = on", "unknown name on"),
            ("(if nope id)", "unknown name nope"),
            ("(if same id)", "same needs parentheses"),
            ("split_runs = 18446744073709551615", "number too large"),
            ("split_runs =", "found the end"),
            ("(with rewrites=8 semi_leaves=2 rewrite)", "write (KEY = VALUE | ... | p)"),
            ("rewrite | (with bit_splits=2 rewrite)", "bit_split_budget"),
            ("with", "no longer read"),
            ("(time-limit 500) | rewrite", "write time_limit = N"),
            ("rewrite | time-limit", "time_limit = none for no limit"),
            ("(if true id)", "write 1"),
            ("(filter (true && mixed))", "(any 1)"),
            ("split_runs = size-mul-x", "size-mul-x reads as size - mul - x: names use _, not -"),
            ("tfunc-whole", "write tfunc_whole"),
            ("split_runs = size-mul | tfunc-whole", "tfunc-whole reads as tfunc - whole"),
            ("(if (prove-minimal) id)", "write prove_minimal"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    /// How the Rust code calls a parsed function.
    fn rust_kind(p: &Pipe) -> builtins::Kind {
        use builtins::Kind;
        match p {
            Pipe::Pass(Pass::Term { alt: Some(_), .. }) => Kind::Alt,
            Pipe::Pass(Pass::Term { .. }) => Kind::Each,
            Pipe::Pass(Pass::Set(i)) => match crate::pipe::SET_PASSES[*i] {
                "prepass" | "reprint" => Kind::Main,
                "polish" => Kind::Each,
                _ => Kind::Group,
            },
            _ => Kind::Group,
        }
    }

    /// How `pipe::cond` and `Env::value` evaluate a parsed number function.
    fn rust_number_kind(e: &Expr) -> builtins::Kind {
        match e {
            Expr::Is(i) if ["minimal", "used_wide", "used_clustered", "moved", "cofactor"].contains(&CONDS[*i]) => builtins::Kind::GroupNum,
            Expr::Any(_) | Expr::All(_) => builtins::Kind::GroupNum,
            _ => builtins::Kind::TermNum,
        }
    }

    #[test]
    fn every_builtin_is_declared_and_implemented() {
        for s in builtins::all() {
            let call = builtins::sample(s);
            if s.is_number() {
                let Pipe::Filter(e) = parse(&format!("(filter {call})")).unwrap_or_else(|e| panic!("{call}: {e}")) else { panic!("{call}") };
                assert_eq!(rust_number_kind(&e), s.kind(), "{}", s.decl());
            } else {
                let p = parse(&call).unwrap_or_else(|e| panic!("{call}: {e}"));
                assert_eq!(rust_kind(&p), s.kind(), "{}", s.decl());
            }
        }
        let polish = crate::linear_mba::POLISH.iter().map(|(n, _)| format!("polish/{n}"));
        let term = crate::linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string());
        let named = [&crate::pipe::SET_PASSES[..], &FORMS, &NUMBER_FORMS, &CONDS, &FEATURES].concat();
        let mut rust: Vec<String> = named.iter().map(|n| n.to_string()).chain(term).chain(polish).collect();
        rust.sort();
        rust.dedup();
        for n in &rust {
            assert!(builtins::get(n).is_some(), "{n} has no extern in src/builtins.pipe");
        }
        assert_eq!(rust.len(), builtins::all().len(), "an extern names no Rust built-in");
    }

    #[test]
    fn calls_follow_signatures() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        let id = || Box::new(Pipe::Pass(Pass::id()));
        same("(egglog)", "egglog");
        assert_eq!(parse("(egglog later)").unwrap(), Pipe::Pass(Pass::Egglog("egglog/later".into())));
        same("(fix 3 lowbits | rewrite)", "(fix 3 (lowbits | rewrite))");
        same("(tag t lowbits | rewrite)", "(tag t (lowbits | rewrite))");
        same("(if (size) id)", "(if size id)");
        same("(relate = 0 | rewrite)", "relate = 0 | rewrite");
        same("(rewrite | relate)", "rewrite | relate");
        assert_eq!(parse("(if (size + 1) id)").unwrap(), Pipe::If(Expr::Bin('+', Box::new(Expr::Feature(0)), Box::new(Expr::Num(1))), id(), id()));
        assert_eq!(parse("(filter (size vars))").unwrap(), Pipe::Filter(Expr::Size("vars".into())));
        same("(filter (any mul > 1 && tiny))", "(filter (any (mul > 1 && tiny)))");
        assert_eq!(parse("(if lowbits id)").unwrap(), Pipe::If(Expr::Var(var_index("lowbits").unwrap()), id(), id()), "a switch in an expression");
        for (bad, msg) in [
            ("mixed", "mixed gives a number, not candidates: (mixed t:term) num"),
            ("(any 1)", "any gives a number"),
            ("(size t)", "size gives a number"),
            ("(if egglog id)", "egglog gives candidates, not a number: (egglog label:name? g:group) group"),
            ("(if (best 1 id) id)", "best gives candidates"),
            ("(if mixed)", "if takes an expression, a pipeline and an optional pipeline: (if c:num a:pipe b:pipe? g:group) group"),
            ("(if mixed id id id)", "if takes"),
            ("(retry mixed id)", "retry takes an expression and two pipelines"),
            ("(fix 3)", "fix takes an expression and a pipeline"),
            ("(fix)", "fix takes"),
            ("(seq)", "seq takes one or more pipelines"),
            ("(best 1)", "best takes"),
            ("(save t 1)", "save takes a group variable: (save r:group g:group) group"),
            ("(save)", "save takes a group variable"),
            ("(tag)", "tag takes a name and a pipeline"),
            ("(lowbits x)", "lowbits takes no arguments: (lowbits t:term) term"),
            ("(id 1)", "id takes no arguments"),
            ("fix", "fix needs parentheses: (fix ...); (fix n:num p:pipe g:group) group"),
            ("(if any id)", "any needs parentheses"),
            ("(if (same) id)", "same takes a group variable: (same r:group t:term) num"),
            ("(if (same t 1) id)", "same takes a group variable"),
            ("split_runs", "split_runs is a variable, not a step"),
            ("off", "off needs parentheses"),
            ("egglog/x", "write egglog/x as (egglog x)"),
            ("label/b", "write label/b as (label b)"),
            ("extern", NO_EXTERN),
            ("(extern (x g:group) group)", NO_EXTERN),
            ("rewrite = 1", "rewrite is a function and cannot be assigned: (rewrite t:term) term"),
            ("same = 1", "computed from the candidates"),
            ("nope", "unknown pass nope; known: id none prepass"),
            ("(if nope id)", "unknown name nope in an expression; known: size vars"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn let_names_are_not_variables_or_functions() {
        let def = |s: &str| parse_definition(s, &Defs::new(), &mut Vec::new()).map(|d| d.name);
        assert_eq!(def("(let g rewrite | relate)").unwrap(), "g");
        assert_eq!(def("(def (g) rewrite | relate)").unwrap(), "g");
        assert_eq!(def("(def @inline (g) rewrite | relate)").unwrap(), "g");
        for name in ["split_runs", "relate_parts", "time_limit", "mixed", "mul", "size", "same", "none", "pipeline", "sub/cluster", "rewrite", "fix", "on", "def", "extern"] {
            assert!(def(&format!("(let {name} id)")).is_err(), "{name}");
            assert!(def(&format!("(def @inline ({name}) id)")).is_err(), "{name}");
        }
        for name in ["split_runs", "mixed", "size", "none", "lowbits", "fix", "on", "def", "sub/nope", "id"] {
            assert!(def(&format!("(def ({name}) id)")).is_err(), "{name}");
        }
        for name in ["pipeline", "prepass", "polish", "rewrite", "simba", "sub/cluster"] {
            assert_eq!(def(&format!("(def ({name}) id)")).unwrap(), name, "a defined function of the Rust code is replaced");
        }
        for (bad, msg) in [("(def (f x) id)", "parameter x is never used"), ("(def @pure (f) id)", "unknown attribute @pure"), ("(def f id)", "expected (NAME)"), ("(def (f) id id)", "expected )")] {
            let e = def(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn group_assignments() {
        let bind = |n: &str, p: &str| Pipe::Bind(n.into(), Box::new(parse(p).unwrap()));
        assert_eq!(parse("t = (lowbits | unshift)").unwrap(), bind("t", "lowbits | unshift"));
        assert_eq!(parse("t = rewrite | relate").unwrap(), Pipe::Seq(vec![bind("t", "rewrite"), parse("relate").unwrap()]));
        assert_eq!(parse("t = (load u)").unwrap(), bind("t", "(load u)"));
        assert_eq!(parse("t = u | rewrite").unwrap(), Pipe::Seq(vec![Pipe::Bind("t".into(), Box::new(Pipe::Value("u".into()))), parse("rewrite").unwrap()]), "t = u binds u's group");
        assert_eq!(show(&parse("t = (load u)").unwrap()), "t = (load u)");
        assert_eq!(parse_definition("(def (f r:group) u = r | (load u))", &Defs::new(), &mut Vec::new()).unwrap().params[0].ty, Ty::Group);
        assert_eq!(parse("t = relate").unwrap(), bind("t", "relate"), "relate after a group variable is the pass");
        assert_eq!(parse("t = (relate = 0 | rewrite)").unwrap(), bind("t", "relate = 0 | rewrite"));
        assert_eq!(parse("t = (best 1 id rewrite)").unwrap(), bind("t", "(best 1 id rewrite)"));
        assert!(matches!(parse("keep = keep + 1").unwrap(), Pipe::Pass(Pass::Assign(..))), "a variable that holds a number takes an expression");
        assert!(matches!(parse("relate = (size > 3)").unwrap(), Pipe::Pass(Pass::Assign(..))));
        for s in ["t = (lowbits | unshift) | (load t)", "t = rewrite | relate", "(if mixed t = rewrite) | u = (v = t) | (filter (same u))", "(seq t = (x = u))", "t = u | rewrite"] {
            assert_eq!(show(&parse(s).unwrap()), s, "{s}");
            assert_eq!(parse(&show(&parse(s).unwrap())).unwrap(), parse(s).unwrap(), "{s}");
        }
        for (bad, msg) in [
            ("t = 1", "unknown variable t"),
            ("t = keep", "unknown variable t"),
            ("t = u + 1", "unknown variable t"),
            ("t = (u)", "unknown variable t"),
            ("keep = rewrite", "keep is a variable that holds a number, so it cannot be bound to candidates"),
            ("(save keep)", "keep is a variable that holds a number, so it cannot name a group variable"),
            ("(if (same relate) id)", "relate is a variable that holds a number"),
            ("rewrite = id", "rewrite is a function and cannot be assigned"),
            ("size = id", "cannot be assigned"),
            ("t = rewrite = 1", "rewrite is a function and cannot be assigned"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
        let lets = |item: &str| {
            let d = parse_definition(item, &Defs::new(), &mut Vec::new()).unwrap();
            let mut defs = Defs::new();
            defs.insert(d.name, Named { pipe: d.pipe, flat: d.flat, run: false, params: Vec::new(), def: None });
            defs
        };
        assert!(parse_with("g = id", &lets("(let g rewrite)"), &mut Vec::new()).unwrap_err().contains("defined by let"));
        assert_eq!(parse_with("t = g", &lets("(let g rewrite | relate)"), &mut Vec::new()).unwrap(), bind("t", "rewrite | relate"));
        let d = parse_definition("(def (f a p) p | (load a))", &Defs::new(), &mut Vec::new()).unwrap();
        assert_eq!(def_sig(&d.name, &d.params).to_string(), "(f a:group p:pipe g:group) group");
        let def_err = |s: &str| parse_definition(s, &Defs::new(), &mut Vec::new()).err().unwrap();
        assert!(def_err("(def (f n) n = 3)").contains("parameter n cannot be assigned"));
        assert!(def_err("(def (f n) (fix n id) | n = id)").contains("parameter n cannot be assigned"));
        assert!(parse_assign("t", "rewrite").unwrap_err().contains("unknown variable t"), "an entry assignment is to a variable that holds a number");
    }

    #[test]
    fn nested_assignments_parse_once() {
        let (mut group, mut number) = ("rewrite".to_string(), "keep = 1".to_string());
        for i in 0..24 {
            group = format!("t{i} = ({group} | relate)");
            number = format!("keep = (relate = 0 | ({number}) | size) + 1");
        }
        let start = std::time::Instant::now();
        for s in [&group, &number] {
            let p = parse(s).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{s}");
        }
        assert!(matches!(parse(&number).unwrap(), Pipe::Pass(Pass::Assign(..))));
        assert!(matches!(parse(&group).unwrap(), Pipe::Bind(..)));
        assert!(start.elapsed() < std::time::Duration::from_secs(2), "{:?}", start.elapsed());
        for (s, msg) in [("keep = ((lowbits | size) + 1)", ""), ("t = ((lowbits | unshift) | relate)", ""), ("t = ((lowbits | size) | relate)", "gives a number; relate takes candidates"), ("t = (u)", "the right side is not a step either: unknown name u"), ("t = (time-limit 3)", "write time_limit = N")] {
            match parse(s) {
                Ok(_) => assert!(msg.is_empty(), "{s}"),
                Err(e) => assert!(!msg.is_empty() && e.contains(msg), "{s}: {e}"),
            }
        }
    }

    /// The steps `(smallest ...)` in `p` expands to, its note registers named `s`, `t`, ... in
    /// the order they first appear.
    fn expansion(p: &Pipe) -> String {
        let Pipe::Smallest(m) = p else { panic!("{}", show(p)) };
        let mut out = show(&Pipe::Seq(m.steps.clone()));
        let mut names: Vec<String> = Vec::new();
        while let Some(i) = out.find("smallest#") {
            let end = out[i + 9..].find(|c: char| !c.is_ascii_digit()).map_or(out.len(), |k| i + 9 + k);
            let n = out[i..end].to_string();
            names.push(n.clone());
            out = out.replace(&n, ["s", "t", "u"][names.len() - 1]);
        }
        out
    }

    #[test]
    fn smallest_notes_each_step_that_computes() {
        let p = parse("(smallest rewrite | id | (save r) | (fix 2 tfunc) | (best 1 relate id (load r)) | (if mixed polish))").unwrap();
        assert_eq!(
            expansion(&p),
            "(clear s) | rewrite | (note s) | id | (save r) | (fix 2 tfunc | (note s)) | (best 1 (relate | (note s)) id (load r)) | (if mixed (polish | (note s))) | (take_min s)"
        );
        assert_eq!(show(&p), "(smallest rewrite | id | (save r) | (fix 2 tfunc) | (best 1 relate id (load r)) | (if mixed polish))", "shown as written");
        assert_eq!(p, parse(&show(&p)).unwrap(), "compared as written");
        let one = parse("(smallest (union prepass take_minimal))").unwrap();
        assert_eq!(expansion(&one), "(clear s) | (union (prepass | (note s)) (take_minimal | (note s))) | (take_min s)");
        let Pipe::Smallest(m) = &one else { unreachable!() };
        assert!(!m.scoped, "a single step runs in the enclosing sequence, as it would without smallest");
        let nested = parse("(smallest rewrite | (smallest tfunc | none) | relate)").unwrap();
        assert_eq!(
            expansion(&nested),
            "(clear s) | rewrite | (note s) | (smallest tfunc | none) | relate | (note s) | (take_min s)",
            "shown as written inside"
        );
        let Pipe::Smallest(m) = &nested else { unreachable!() };
        let inner = expansion(&m.steps[3]);
        assert_eq!(inner, "(clear s) | tfunc | (note t) | (note s) | none | (take_min s)", "the outer note (t) in the inner expansion");
        let names: Vec<String> = [&nested, &m.steps[3]].iter().map(|p| if let Pipe::Smallest(m) = p { show(&m.steps[0]) } else { unreachable!() }).collect();
        assert_ne!(names[0], names[1], "each smallest has a register of its own");
    }

    #[test]
    fn smallest_notes_arguments_but_not_bodies_of_calls() {
        let passes = |spec: &str| Passes::parse(spec).unwrap_or_else(|e| panic!("{spec}: {e}"));
        let p = passes("(def (f p) rewrite | p) prepass=(smallest (f tfunc) | relate)");
        assert_eq!(expansion(&p.prepass), "(clear s) | (f (tfunc | (note s))) | (note s) | relate | (note s) | (take_min s)");
        let Pipe::Smallest(m) = &p.prepass else { unreachable!() };
        let Pipe::Call(c) = &m.steps[1] else { unreachable!() };
        assert_eq!(show(&c.body), "rewrite | p", "the body of a def is a run of its own");
        let p = passes("(def @inline (g n p) (if (size > n) rewrite) | p) prepass=(smallest (g 1 tfunc))");
        assert_eq!(expansion(&p.prepass), "(clear s) | (g 1 (tfunc | (note s))) | (take_min s)");
        let Pipe::Smallest(m) = &p.prepass else { unreachable!() };
        let Pipe::Call(c) = &m.steps[1] else { unreachable!() };
        let body = show(&c.body).replace(|c: char| c.is_ascii_digit(), "");
        assert_eq!(body, "(if (size > n) (rewrite | (note smallest#))) | p", "an @inline body is noted; its argument has its notes");
        let p = passes("(def (w p) (smallest p | rewrite)) prepass=(w tfunc)");
        let Pipe::Call(c) = &p.prepass else { unreachable!() };
        assert_eq!(expansion(&c.body), "(clear s) | p | (note s) | rewrite | (note s) | (take_min s)", "in a def body a parameter gives what its argument returns");
        let p = passes("(let k rewrite | tfunc) prepass=(smallest id | k)");
        assert_eq!(expansion(&p.prepass), "(clear s) | id | rewrite | (note s) | tfunc | (note s) | (take_min s)", "a let is in the text");
        let p = passes("(def @inline (h p) (smallest p | none)) prepass=(h rewrite)");
        assert_eq!(expansion(&p.prepass), "(clear s) | rewrite | (note s) | none | (take_min s)", "an @inline argument put in place");
        assert_eq!(p.to_string(), passes(&p.to_string()).to_string());
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
