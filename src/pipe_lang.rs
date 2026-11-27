//! The pipeline language (`docs/pipe-language.md`): `a | b` runs `b` on the candidates of
//! `a`, `(FORM args...)` is a combinator or a pass with arguments, `NAME = VALUE` assigns a
//! variable, conditions are expressions (`(if (mul >= 4 && shift < 1) (off small_blocks))`).
//! Parsed into `sched::Pipe`.

use crate::builtins::{self, Rep, Sig, Ty};
use crate::pipe::{CONDS, FEATURES, resolve};
use crate::sched::{Cmp, Expr, INNER, NONE, NVARS, Pass, Pipe, is_switch, var, var_index};

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
pub(crate) const FORMS: [&str; 20] = [
    "seq", "union", "best", "first", "fix", "if", "retry", "smallest", "scope", "regions", "again", "tag", "cand", "smaller", "wins", "filter", "save", "load", "label",
    "egglog",
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
        "smallest" => Pipe::Smallest(a.pipe()),
        "scope" => Pipe::Scope(a.pipe()),
        "regions" => Pipe::Regions(a.pipe()),
        "again" => Pipe::Again(a.pipe()),
        "tag" => Pipe::Tag(a.name(), a.pipe()),
        "cand" => Pipe::Cand(a.name(), a.pipe()),
        "smaller" => Pipe::Smaller(a.name(), a.pipe()),
        "filter" => Pipe::Filter(a.num()),
        "save" | "load" | "label" => Pipe::Pass(resolve(&format!("{f}/{}", a.name()))?),
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

/// The pipelines `(let NAME p)` defined, by name.
/// Each with whether it is written as a sequence without parentheses, which joins the
/// sequence it is used in (`(let g a | b)`; `(let g (a | b))` stays one nested stage).
pub type Defs = std::collections::HashMap<String, (Pipe, bool)>;

struct Parser<'a> {
    toks: Vec<Tok>,
    at: usize,
    defs: &'a Defs,
    /// The names of `defs` expanded.
    used: Vec<String>,
}

impl Parser<'_> {
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

    fn pipe(&mut self) -> Result<Pipe, String> {
        let mut stages = self.stages_of_pipe()?;
        Ok(if stages.len() == 1 { stages.pop().unwrap() } else { Pipe::Seq(stages) })
    }

    /// The stages of a pipeline `a | b | ...`.
    fn stages_of_pipe(&mut self) -> Result<Vec<Pipe>, String> {
        let mut stages = Vec::new();
        loop {
            let flat = matches!(self.peek(), Some(Tok::Name(n)) if self.defs.get(n).is_some_and(|d| d.1));
            match self.stage()? {
                Pipe::Seq(ps) if flat => stages.extend(ps),
                p => stages.push(p),
            }
            if self.peek() != Some(&Tok::Bar) {
                break;
            }
            self.at += 1;
        }
        Ok(stages)
    }

    fn stage(&mut self) -> Result<Pipe, String> {
        if let (Some(Tok::Name(n)), Some(Tok::Assign)) = (self.peek().cloned(), self.peek_at(1)) {
            self.at += 2;
            return self.assign(&n);
        }
        let k = usize::from(self.peek() == Some(&Tok::Open));
        if let Some(e) = self.old_form(k) {
            return Err(e.into());
        }
        match self.next() {
            Some(Tok::Name(n)) if self.defs.contains_key(&n) => {
                let p = self.defs[&n].0.clone();
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
                    Some(Tok::Name(n)) => match builtins::get(&n) {
                        Some(s) if s.is_number() => return Err(not_a_step(s)),
                        Some(s) if !s.params.is_empty() => {
                            self.at += 1;
                            self.call(s)?
                        }
                        Some(s) if matches!(self.peek_at(1), Some(Tok::Name(_) | Tok::Num(_) | Tok::Open | Tok::Not)) => {
                            return Err(format!("{n} takes no arguments: {s}"));
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

    /// The right side of `n = ...`: an expression up to `|`, `)` or the end.
    fn assign(&mut self, n: &str) -> Result<Pipe, String> {
        let i = assignable(n)?;
        let e = self.or()?;
        self.no_assign()?;
        if let Expr::Num(k) = e {
            if is_switch(i) && k == NONE {
                return Err(format!("{n} is a switch: assign it 0 (off) or 1 (on)"));
            }
            crate::sched::check_cap(i, k)?;
        }
        Ok(Pipe::Pass(Pass::Assign(i, e)))
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
        let f = s.name.as_str();
        let arity = || format!("{f} takes {}: {s}", s.takes());
        let pipes = s.params.iter().filter(|p| p.ty == Ty::Pipe).count();
        let mut args = Vec::new();
        for (i, p) in s.params.iter().enumerate() {
            let whole = pipes == 1 && i + 1 == s.params.len() && p.rep == Rep::One;
            let named = matches!(self.peek(), Some(Tok::Name(_)));
            args.push(match (p.ty, p.rep) {
                (_, Rep::Opt) if self.at_close() => Arg::Absent,
                (Ty::Name | Ty::Reg, Rep::Opt) if !named => Arg::Absent,
                (_, Rep::One) if self.at_close() => return Err(arity()),
                (Ty::Num, _) => Arg::Num(self.arg()?),
                (Ty::Name | Ty::Reg, _) => Arg::Name(self.name(&format!("a name after {f}"))?),
                (Ty::Pipe, Rep::Many) => Arg::Pipes(self.stages(f, &arity)?),
                (Ty::Pipe, _) if whole => Arg::Pipe(self.pipe()?),
                (Ty::Pipe, _) => {
                    self.no_bar(f)?;
                    Arg::Pipe(self.stage()?)
                }
                _ => unreachable!("{s}"),
            });
        }
        if !self.at_close() {
            if pipes > 0 {
                self.no_bar(f)?;
            }
            return Err(arity());
        }
        construct(f, args).ok_or_else(|| unimplemented(s))
    }

    /// The macro `(off NAME ...)` or `(on NAME ...)` after its name: one pass for all the
    /// names, since a sequence of them would end their effect.
    fn switches(&mut self, f: &str) -> Result<Pipe, String> {
        let mut ns = Vec::new();
        while !self.at_close() {
            let n = self.name(&format!("a pass name after {f}"))?;
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
                Ty::Num => Arg::Num(self.or()?),
                _ => Arg::Name(self.name("a register")?),
            });
        }
        if !self.at_close() {
            return Err(format!("{f} takes {}: {s}", s.takes()));
        }
        number(f, args).ok_or_else(|| unimplemented(s))
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
        if self.peek() == Some(&Tok::Not) {
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

    /// A number, a name, `(size R)`, `(same R)`, `(any C)`, `(all C)` or `( expr )`.
    fn atom(&mut self) -> Result<Expr, String> {
        match self.next() {
            Some(Tok::Num(n)) => Ok(Expr::Num(n)),
            Some(Tok::Name(n)) => {
                self.no_assign()?;
                name_expr(&n)
            }
            Some(Tok::Open) => {
                // `(size)` and `(size + 1)` are parenthesized expressions, `(size r)` a call.
                let call = match self.peek() {
                    Some(Tok::Name(k)) => builtins::get(k).filter(|s| {
                        let named = matches!(self.peek_at(1), Some(Tok::Name(_))) && self.peek_at(2) == Some(&Tok::Close);
                        s.is_number() && !s.params.is_empty() && (s.required() || named)
                    }),
                    _ => None,
                };
                let e = match call {
                    Some(s) => {
                        self.at += 1;
                        self.number_call(s)?
                    }
                    None => self.or()?,
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
    let one_name = |h: &str| builtins::get(h).is_some_and(|s| matches!(s.params.as_slice(), [p] if matches!(p.ty, Ty::Reg | Ty::Name)));
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
        let mut p = Parser { toks: lex(val)?, at: 0, defs: &Defs::new(), used: Vec::new() };
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
        let mut p = Parser { toks: lex(s)?, at: 0, defs, used: Vec::new() };
        let pipe = p.pipe()?;
        p.end()?;
        Ok((pipe, p.used))
    };
    let (pipe, names) = go().map_err(|e| hyphen_hint(e, s))?;
    used.extend(names);
    Ok(pipe)
}

/// Parses the definition `(let NAME p)`: `NAME` then stands for `p`, which is expanded where
/// it is used; the names of `defs` it expands are added to `used`.
pub fn parse_let(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<(String, (Pipe, bool)), String> {
    let_def(s, defs, used).map_err(|e| hyphen_hint(e, s))
}

fn let_def(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<(String, (Pipe, bool)), String> {
    let mut p = Parser { toks: lex(s)?, at: 0, defs, used: Vec::new() };
    p.expect(Tok::Open, "(let")?;
    if p.name("let")? != "let" {
        return Err(format!("expected (let NAME pipeline): {s}"));
    }
    let name = p.name("a name after let")?;
    let function = builtins::get(&name);
    if function.is_some_and(|s| !s.is_number()) || resolve(&name).is_some() || builtins::MACROS.contains(&name.as_str()) || name == "extern" {
        return Err(format!("let {name}: the name of a pass, form or macro"));
    }
    let pipeline = ["pipeline", "prepass", "polish", "rewrite", "simba"].contains(&name.as_str()) || name.strip_prefix("sub/").is_some_and(|n| crate::sched::SUBS.iter().any(|(s, _)| *s == n));
    if var_index(&name).is_some() || function.is_some() || name == "none" || pipeline {
        return Err(format!("let {name}: the name of a variable or function"));
    }
    let mut stages = p.stages_of_pipe()?;
    p.expect(Tok::Close, ")")?;
    p.end()?;
    used.extend(p.used);
    let flat = stages.len() > 1;
    let pipe = if flat { Pipe::Seq(stages) } else { stages.pop().unwrap() };
    Ok((name, (pipe, flat)))
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

/// `e` as an argument of a form.
fn show_arg(e: &Expr) -> String {
    match e {
        Expr::Not(x) => format!("!{}", show_arg(x)),
        e => show_expr(e, 7),
    }
}

/// `p` written as a stage: a sequence in parentheses.
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
        Some((h @ ("save" | "load" | "label" | "off" | "on" | "egglog"), r)) => form(h, &[r.to_string()]),
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
        Pipe::Smallest(p) => form("smallest", &[show(p)]),
        Pipe::Scope(p) => form("scope", &[show(p)]),
        Pipe::Regions(p) => form("regions", &[show(p)]),
        Pipe::Again(p) => form("again", &[show(p)]),
        Pipe::Tag(n, p) => form("tag", &with(vec![n.clone()], p)),
        Pipe::Cand(n, p) => form("cand", &with(vec![n.clone()], p)),
        Pipe::Smaller(n, p) => form("smaller", &with(vec![n.clone()], p)),
        Pipe::Filter(c) => form("filter", &[show_arg(c)]),
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
        Pipe::Smallest(q) => nested("smallest", vec![], vec![(q, false)]),
        Pipe::Scope(q) => nested("scope", vec![], vec![(q, false)]),
        Pipe::Regions(q) => nested("regions", vec![], vec![(q, false)]),
        Pipe::Again(q) => nested("again", vec![], vec![(q, false)]),
        Pipe::Tag(n, q) => nested("tag", vec![n.clone()], vec![(q, false)]),
        Pipe::Cand(n, q) => nested("cand", vec![n.clone()], vec![(q, false)]),
        Pipe::Smaller(n, q) => nested("smaller", vec![n.clone()], vec![(q, false)]),
        Pipe::Pass(_) | Pipe::Filter(_) => one,
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
            ("(save t x)", "save takes a register name: (save r:reg g:group) group"),
            ("(save)", "save takes a register name"),
            ("(tag)", "tag takes a name and a pipeline"),
            ("(lowbits x)", "lowbits takes no arguments: (lowbits t:term) term"),
            ("(id 1)", "id takes no arguments"),
            ("fix", "fix needs parentheses: (fix ...); (fix n:num p:pipe g:group) group"),
            ("(if any id)", "any needs parentheses"),
            ("(if (same) id)", "same takes a register name: (same r:reg t:term) num"),
            ("(if (same t u) id)", "same takes a register name"),
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
        let def = |s: &str| parse_let(s, &Defs::new(), &mut Vec::new()).map(|(n, _)| n);
        assert_eq!(def("(let g rewrite | relate)").unwrap(), "g");
        for name in ["split_runs", "relate_parts", "time_limit", "mixed", "mul", "size", "same", "none", "pipeline", "sub/cluster", "rewrite", "fix"] {
            assert!(def(&format!("(let {name} id)")).is_err(), "{name}");
        }
    }
}
