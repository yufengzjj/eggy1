//! The pipeline language (`docs/pipe-language.md`): `a | b` runs `b` on the candidates of
//! `a`, `(FORM args...)` is a combinator or a pass with arguments, `NAME = VALUE` assigns a
//! variable, conditions are expressions (`(if (mul >= 4 && shift < 1) (off small_blocks))`).
//! Parsed into `sched::Pipe`.

use crate::pipe::{CONDS, COUNTS, FEATURES, resolve};
use crate::sched::{Cmp, Cond, INNER, NVARS, Pass, Pipe, Value, is_switch, var, var_index};

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
                (Tok::Num(n.parse().map_err(|_| format!("number too large: {n}"))?), len)
            }
            c if name_start(c) => {
                // `-` joins a name only before a letter or `_` (`time-limit`), so `restarts-1`
                // is still a subtraction.
                let mut len = 1;
                while cs.get(i + len).is_some_and(|c| name_char(*c) || *c == '-' && cs.get(i + len + 1).is_some_and(|d| name_start(*d))) {
                    len += 1;
                }
                (Tok::Name(cs[i..i + len].iter().collect()), len)
            }
            _ => return Err(format!("unexpected character {c:?} in pipeline")),
        };
        out.push(tok);
        i += len;
    }
    Ok(out)
}

const FORMS: [&str; 24] = [
    "seq", "union", "best", "first", "fix", "if", "retry", "smallest", "scope", "regions", "again", "tag", "cand", "smaller", "wins", "filter", "with", "save", "load",
    "label", "off", "on", "egglog", "time-limit",
];

/// An expression before it is read as a condition or a value.
#[derive(Debug)]
enum E {
    Name(String),
    Num(u64),
    Size(String),
    Same(String),
    Quant(bool, Box<E>),
    Not(Box<E>),
    And(Vec<E>),
    Or(Vec<E>),
    Cmp(Cmp, Box<E>, Box<E>),
    Bin(char, Box<E>, Box<E>),
}

fn to_cond(e: E) -> Result<Cond, String> {
    let all = |es: Vec<E>| es.into_iter().map(to_cond).collect::<Result<Vec<_>, _>>();
    Ok(match e {
        E::Name(n) => match CONDS.iter().position(|c| *c == n) {
            Some(i) => Cond::Is(i),
            None if FEATURES.contains(&n.as_str()) => return Err(format!("{n} is a number: compare it, as in ({n} >= 1)")),
            None => return Err(format!("unknown condition {n}; known: {}", CONDS.join(" "))),
        },
        E::Same(r) => Cond::Same(r),
        E::Quant(any, c) => {
            let c = Box::new(to_cond(*c)?);
            if any { Cond::Any(c) } else { Cond::All(c) }
        }
        E::Not(c) => Cond::Not(Box::new(to_cond(*c)?)),
        E::And(cs) => Cond::And(all(cs)?),
        E::Or(cs) => Cond::Or(all(cs)?),
        E::Cmp(op, a, b) => Cond::Cmp(op, to_value(*a)?, to_value(*b)?),
        e => return Err(format!("expected a condition, found the number {e:?}")),
    })
}

fn to_value(e: E) -> Result<Value, String> {
    Ok(match e {
        E::Num(n) => Value::Num(n),
        E::Name(n) => {
            if let Some(i) = FEATURES.iter().position(|f| *f == n) {
                Value::Feature(i)
            } else if let Some(i) = COUNTS.iter().position(|c| *c == n) {
                Value::Count(i)
            } else if let Some(i) = var_index(&n).filter(|i| !is_switch(*i)) {
                Value::Var(i)
            } else if n == "none" {
                return Err("none stands only alone on the right of =: NAME = none".into());
            } else {
                return Err(format!("unknown number {n}; known: {} {} and the variables", FEATURES.join(" "), COUNTS.join(" ")));
            }
        }
        E::Size(r) => Value::Size(r),
        E::Bin(op, a, b) => Value::Bin(op, Box::new(to_value(*a)?), Box::new(to_value(*b)?)),
        e => return Err(format!("expected a number, found the condition {e:?}")),
    })
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
        match self.next() {
            Some(Tok::Name(n)) if FORMS.contains(&n.as_str()) && n != "egglog" => Err(format!("{n} needs parentheses: ({n} ...)")),
            Some(Tok::Name(n)) if self.defs.contains_key(&n) => {
                let p = self.defs[&n].0.clone();
                self.used.push(n);
                Ok(p)
            }
            Some(Tok::Name(n)) if n.split_once('/').is_some_and(|(h, _)| crate::pipe::FORM_PASSES.contains(&h)) => {
                let (h, r) = n.split_once('/').unwrap();
                Err(format!("write {n} as ({h} {r})"))
            }
            Some(Tok::Name(n)) => resolve(&n).map(Pipe::Pass).ok_or_else(|| format!("unknown pass {n}; known: {}", crate::pipe::names().join(" "))),
            Some(Tok::Open) => {
                let p = match self.peek() {
                    Some(Tok::Name(n)) if FORMS.contains(&n.as_str()) && !(n == "egglog" && self.peek_at(1) == Some(&Tok::Close)) => {
                        let n = n.clone();
                        self.at += 1;
                        self.form(&n)?
                    }
                    _ => self.pipe()?,
                };
                self.expect(Tok::Close, ")")?;
                Ok(p)
            }
            x => Err(format!("expected a pass or (, found {}", show_tok(x.as_ref()))),
        }
    }

    /// The right side of `n = ...`: `none`, or an expression up to `|`, `)` or the end.
    fn assign(&mut self, n: &str) -> Result<Pipe, String> {
        let i = assignable(n)?;
        let alone = matches!(self.peek_at(1), Some(Tok::Bar | Tok::Close) | None);
        if alone && self.peek() == Some(&Tok::Name("none".into())) {
            if is_switch(i) {
                return Err(format!("{n} is a switch: assign it 0 (off) or 1 (on)"));
            }
            self.at += 1;
            return Ok(Pipe::Pass(Pass::Assign(i, None)));
        }
        let e = self.or()?;
        self.no_assign()?;
        Ok(Pipe::Pass(Pass::Assign(i, Some(to_value(e)?))))
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

    /// Stages up to the closing parenthesis.
    fn stages(&mut self, form: &str) -> Result<Vec<Pipe>, String> {
        let mut out = Vec::new();
        while !self.at_close() {
            if self.peek() == Some(&Tok::Bar) {
                return Err(format!("group a pipeline argument of {form} in parentheses: ({form} ... (a | b))"));
            }
            out.push(self.stage()?);
        }
        if out.is_empty() {
            return Err(format!("{form} needs a pipeline"));
        }
        Ok(out)
    }

    /// A count: a number, a name or a parenthesized expression.
    fn count(&mut self) -> Result<Value, String> {
        let e = self.atom()?;
        self.no_assign()?;
        to_value(e)
    }

    /// A condition argument: a name, `!` and a condition argument, or a parenthesized
    /// expression.
    fn cond(&mut self) -> Result<Cond, String> {
        let e = self.cond_arg()?;
        self.no_assign()?;
        to_cond(e)
    }

    fn cond_arg(&mut self) -> Result<E, String> {
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(E::Not(Box::new(self.cond_arg()?)));
        }
        self.atom()
    }

    fn form(&mut self, f: &str) -> Result<Pipe, String> {
        let b = Box::new;
        Ok(match f {
            "seq" => Pipe::Seq(self.stages(f)?),
            "union" => Pipe::Union(self.stages(f)?),
            "first" => Pipe::First(self.stages(f)?),
            "best" => {
                let k = self.count()?;
                Pipe::Best(k, self.stages(f)?)
            }
            "fix" => Pipe::Fix(self.count()?, b(self.pipe()?)),
            "wins" => Pipe::Wins(self.count()?, b(self.pipe()?)),
            "if" | "retry" => {
                let c = self.cond()?;
                let mut ps = self.stages(f)?;
                match (f, ps.len()) {
                    ("if", 1) => Pipe::If(c, b(ps.remove(0)), b(Pipe::Pass(Pass::id()))),
                    ("if", 2) => Pipe::If(c, b(ps.remove(0)), b(ps.remove(0))),
                    ("retry", 2) => Pipe::Retry(c, b(ps.remove(0)), b(ps.remove(0))),
                    _ => return Err(format!("{f} takes a condition and {} pipelines", if f == "if" { "one or two" } else { "two" })),
                }
            }
            "smallest" => Pipe::Smallest(b(self.pipe()?)),
            "scope" => Pipe::Scope(b(self.pipe()?)),
            "regions" => Pipe::Regions(b(self.pipe()?)),
            "again" => Pipe::Again(b(self.pipe()?)),
            "tag" | "cand" | "smaller" => {
                let n = self.name(&format!("a name after {f}"))?;
                let p = b(self.pipe()?);
                match f {
                    "tag" => Pipe::Tag(n, p),
                    "cand" => Pipe::Cand(n, p),
                    _ => Pipe::Smaller(n, p),
                }
            }
            "filter" => Pipe::Filter(self.cond()?),
            "with" => {
                // The old form of `(K = V | ... | p)`; `bit_splits` was the budget there.
                let mut steps = Vec::new();
                while let (Some(Tok::Name(k)), Some(Tok::Assign)) = (self.peek().cloned(), self.peek_at(1)) {
                    self.at += 2;
                    if k == "off" {
                        let v = self.name("a pass name after off=")?;
                        return Err(format!("write (off {v}) in the body: (with ... (off {v}) | p)"));
                    }
                    let known = ["rewrites", "semi_leaves", "relate_leaves", "bit_splits"];
                    if !known.contains(&k.as_str()) {
                        return Err(format!("unknown setting {k}; known: {}", known.join(" ")));
                    }
                    let k = if k == "bit_splits" { "bit_split_budget" } else { k.as_str() };
                    steps.push(Pipe::Pass(Pass::Assign(var_index(k).unwrap(), Some(self.count()?))));
                }
                if steps.is_empty() {
                    return Err("with needs KEY=VALUE settings".into());
                }
                match self.pipe()? {
                    Pipe::Seq(ps) if ps.len() > 1 => steps.extend(ps),
                    p => steps.push(p),
                }
                Pipe::Seq(steps)
            }
            "time-limit" => {
                let i = var_index("time_limit").unwrap();
                Pipe::Pass(Pass::Assign(i, Some(self.count()?).filter(|v| *v != Value::Num(0))))
            }
            "save" | "load" | "label" | "egglog" => {
                let n = format!("{f}/{}", self.name(&format!("a name after {f}"))?);
                Pipe::Pass(resolve(&n).unwrap())
            }
            "off" | "on" => {
                // One pass for all the names: a sequence of them would end their effect.
                let mut ns = Vec::new();
                while !self.at_close() {
                    let n = self.name(&format!("a pass name after {f}"))?;
                    let known = || INNER.iter().chain(&crate::sched::FLAGS).copied().collect::<Vec<_>>().join(",");
                    ns.push(crate::sched::switch(&n).ok_or_else(|| format!("unknown {f} name {n}; known: {}", known()))?);
                }
                if ns.is_empty() {
                    return Err(format!("{f} needs a pass name"));
                }
                Pipe::Pass(if f == "off" { Pass::Off(ns) } else { Pass::On(ns) })
            }
            _ => unreachable!(),
        })
    }

    fn or(&mut self) -> Result<E, String> {
        let mut es = vec![self.and()?];
        while self.peek() == Some(&Tok::Or) {
            self.at += 1;
            es.push(self.and()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { E::Or(es) })
    }

    fn and(&mut self) -> Result<E, String> {
        let mut es = vec![self.not()?];
        while self.peek() == Some(&Tok::And) {
            self.at += 1;
            es.push(self.not()?);
        }
        Ok(if es.len() == 1 { es.pop().unwrap() } else { E::And(es) })
    }

    fn not(&mut self) -> Result<E, String> {
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(E::Not(Box::new(self.not()?)));
        }
        let a = self.sum()?;
        self.no_assign()?;
        let Some(Tok::Cmp(op)) = self.peek() else { return Ok(a) };
        let op = Cmp::ALL.iter().find(|(_, s)| s == op).unwrap().0;
        self.at += 1;
        Ok(E::Cmp(op, Box::new(a), Box::new(self.sum()?)))
    }

    fn sum(&mut self) -> Result<E, String> {
        let mut a = self.product()?;
        while let Some(Tok::Arith(op @ ('+' | '-'))) = self.peek().cloned() {
            self.at += 1;
            a = E::Bin(op, Box::new(a), Box::new(self.product()?));
        }
        Ok(a)
    }

    fn product(&mut self) -> Result<E, String> {
        let mut a = self.atom()?;
        while let Some(Tok::Arith(op @ ('*' | '/'))) = self.peek().cloned() {
            self.at += 1;
            a = E::Bin(op, Box::new(a), Box::new(self.atom()?));
        }
        Ok(a)
    }

    /// A number, a name, `(size R)`, `(same R)`, `(any C)`, `(all C)` or `( expr )`.
    fn atom(&mut self) -> Result<E, String> {
        match self.next() {
            Some(Tok::Num(n)) => Ok(E::Num(n)),
            Some(Tok::Name(n)) => Ok(E::Name(n)),
            Some(Tok::Open) => {
                let reg = matches!(self.peek_at(1), Some(Tok::Name(_))) && self.peek_at(2) == Some(&Tok::Close);
                let e = match self.peek() {
                    Some(Tok::Name(k)) if reg && (k == "size" || k == "same") => {
                        let k = k.clone();
                        self.at += 1;
                        let r = self.name("a register")?;
                        if k == "size" { E::Size(r) } else { E::Same(r) }
                    }
                    Some(Tok::Name(k)) if k == "any" || k == "all" => {
                        let any = k == "any";
                        self.at += 1;
                        E::Quant(any, Box::new(self.or()?))
                    }
                    _ => self.or()?,
                };
                self.expect(Tok::Close, ")")?;
                Ok(e)
            }
            x => Err(format!("expected a condition or a number, found {}", show_tok(x.as_ref()))),
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
    Err(if FEATURES.contains(&n) || CONDS.contains(&n) {
        format!("{n} is computed from the candidates and cannot be assigned")
    } else if n == "restarts" {
        "restarts cannot be assigned in a pipeline; set it with -m N".into()
    } else if COUNTS.contains(&n) {
        format!("{n} cannot be assigned in a pipeline; set it with --passes {n}=N")
    } else {
        format!("unknown variable {n}; known: {}", (0..NVARS).map(|i| var(i).name).collect::<Vec<_>>().join(" "))
    })
}

/// Parses `s` in the pipeline language.
pub fn parse(s: &str) -> Result<Pipe, String> {
    parse_with(s, &Defs::new(), &mut Vec::new())
}

/// Parses `s`, where the names of `defs` stand for their pipelines; the names expanded are
/// added to `used`.
pub fn parse_with(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<Pipe, String> {
    let mut p = Parser { toks: lex(s)?, at: 0, defs, used: Vec::new() };
    let pipe = p.pipe()?;
    p.end()?;
    used.extend(p.used);
    Ok(pipe)
}

/// Parses the definition `(let NAME p)`: `NAME` then stands for `p`, which is expanded where
/// it is used; the names of `defs` it expands are added to `used`.
pub fn parse_let(s: &str, defs: &Defs, used: &mut Vec<String>) -> Result<(String, (Pipe, bool)), String> {
    let mut p = Parser { toks: lex(s)?, at: 0, defs, used: Vec::new() };
    p.expect(Tok::Open, "(let")?;
    if p.name("let")? != "let" {
        return Err(format!("expected (let NAME pipeline): {s}"));
    }
    let name = p.name("a name after let")?;
    if FORMS.contains(&name.as_str()) || resolve(&name).is_some() || name == "let" {
        return Err(format!("let {name}: the name of a pass or form"));
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

/// `v` where an operand of precedence `need` stands: `+ -` are 1, `* /` 2, the rest 3.
fn show_value(v: &Value, need: u8) -> String {
    match v {
        Value::Num(n) => n.to_string(),
        Value::Count(i) => COUNTS[*i].to_string(),
        Value::Feature(i) => FEATURES[*i].to_string(),
        Value::Size(r) => format!("(size {r})"),
        Value::Var(i) => var(*i).name.to_string(),
        Value::Bin(op, a, b) => {
            let prec = if matches!(op, '+' | '-') { 1 } else { 2 };
            let s = format!("{} {op} {}", show_value(a, prec), show_value(b, prec + 1));
            if prec < need { format!("({s})") } else { s }
        }
    }
}

/// `c` where an operand of precedence `need` stands: `||` is 1, `&&` 2, `!` 3, a comparison
/// 4, the rest 5.
fn show_expr(c: &Cond, need: u8) -> String {
    let (s, prec) = match c {
        Cond::Is(i) => (CONDS[*i].to_string(), 5),
        Cond::Same(r) => (format!("(same {r})"), 5),
        Cond::Any(c) => (format!("(any {})", show_expr(c, 1)), 5),
        Cond::All(c) => (format!("(all {})", show_expr(c, 1)), 5),
        Cond::Not(c) => (format!("!{}", show_expr(c, 5)), 3),
        Cond::And(cs) => (cs.iter().map(|c| show_expr(c, 3)).collect::<Vec<_>>().join(" && "), 2),
        Cond::Or(cs) => (cs.iter().map(|c| show_expr(c, 2)).collect::<Vec<_>>().join(" || "), 1),
        Cond::Cmp(op, a, b) => (format!("{} {} {}", show_value(a, 1), op.symbol(), show_value(b, 1)), 4),
    };
    if prec < need { format!("({s})") } else { s }
}

/// `c` as a condition argument.
pub fn show_cond(c: &Cond) -> String {
    match c {
        Cond::Not(x) => format!("!{}", show_cond(x)),
        c => show_expr(c, 5),
    }
}

/// `v` as a count argument.
fn show_count(v: &Value) -> String {
    show_value(v, 3)
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
        return format!("{} = {}", var(*i).name, v.as_ref().map_or("none".into(), |v| show_value(v, 1)));
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
        Pipe::Best(k, ps) => form("best", &[vec![show_count(k)], stages(ps)].concat()),
        Pipe::Fix(n, p) => form("fix", &with(vec![show_count(n)], p)),
        Pipe::Wins(n, p) => form("wins", &with(vec![show_count(n)], p)),
        Pipe::If(c, a, b) if is_id(b) => form("if", &[show_cond(c), stage(a)]),
        Pipe::If(c, a, b) => form("if", &[show_cond(c), stage(a), stage(b)]),
        Pipe::Retry(c, a, b) => form("retry", &[show_cond(c), stage(a), stage(b)]),
        Pipe::Smallest(p) => form("smallest", &[show(p)]),
        Pipe::Scope(p) => form("scope", &[show(p)]),
        Pipe::Regions(p) => form("regions", &[show(p)]),
        Pipe::Again(p) => form("again", &[show(p)]),
        Pipe::Tag(n, p) => form("tag", &with(vec![n.clone()], p)),
        Pipe::Cand(n, p) => form("cand", &with(vec![n.clone()], p)),
        Pipe::Smaller(n, p) => form("smaller", &with(vec![n.clone()], p)),
        Pipe::Filter(c) => form("filter", &[show_cond(c)]),
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
        Pipe::Best(k, ps) => nested("best", vec![show_count(k)], many(ps)),
        Pipe::Fix(n, q) => nested("fix", vec![show_count(n)], vec![(q, false)]),
        Pipe::Wins(n, q) => nested("wins", vec![show_count(n)], vec![(q, false)]),
        Pipe::If(c, a, b) if is_id(b) => nested("if", vec![show_cond(c)], vec![(a, true)]),
        Pipe::If(c, a, b) => nested("if", vec![show_cond(c)], vec![(a, true), (b, true)]),
        Pipe::Retry(c, a, b) => nested("retry", vec![show_cond(c)], vec![(a, true), (b, true)]),
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
        same("(with rewrites=8 semi_leaves=2 rewrite)", "(with rewrites=8 semi_leaves=2 (rewrite))");
        same("(with rewrites=8 rewrite | relate)", "(with rewrites=8 (rewrite | relate))");
        assert!(parse("(with off=relate rewrite)").unwrap_err().contains("(off relate)"));
        assert_eq!(parse("(off lowbits relate)").unwrap(), Pipe::Pass(Pass::Off(vec!["lowbits", "relate"])));
        same("(fix restarts prepass | egglog)", "(fix restarts (prepass | egglog))");
        same("# comment
(best 2 rewrite (scope relate)) # more", "(best 2 rewrite (scope relate))");
        let p = parse("(filter (size > (size f) * 3/4 || (same r)))").unwrap();
        let Pipe::Filter(Cond::Or(cs)) = &p else { panic!("{p:?}") };
        assert_eq!(cs[1], Cond::Same("r".into()));
        let three_quarters = Value::Bin('/', Box::new(Value::Bin('*', Box::new(Value::Size("f".into())), Box::new(Value::Num(3)))), Box::new(Value::Num(4)));
        assert_eq!(cs[0], Cond::Cmp(Cmp::Gt, Value::Feature(0), three_quarters));
        for ok in [
            "(if !(minimal && tiny) id)",
            "(filter (any (mul >= 2)))",
            "(filter (all !tiny && size * 2 + 1 <= (size t) - vars))",
            "(fix (restarts - 1) prepass)",
            "(best (keep + 1) id)",
            "(if (size < split_size) id)",
            "(wins (2 * 4) id)",
            "(filter !(same r))",
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
            "(if mul id)",
            "(filter (mul + tiny))",
            "(fix mixed id)",
            "(with nope=1 id)",
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
    fn assignments() {
        let same = |a: &str, b: &str| assert_eq!(parse(a).unwrap(), parse(b).unwrap(), "{a}");
        let at = |n: &str| var_index(n).unwrap();
        let assign = |n: &str, v: Option<Value>| Pipe::Pass(Pass::Assign(at(n), v));
        assert_eq!(parse("split_runs = 4").unwrap(), assign("split_runs", Some(Value::Num(4))));
        same("split_runs=4 | rewrite", "split_runs = 4 | rewrite");
        same("(split_runs=4)", "split_runs   =   4");
        let p = parse("split_runs = vars * 2 + 1 | split_bits").unwrap();
        let rhs = Value::Bin('+', Box::new(Value::Bin('*', Box::new(Value::Feature(1)), Box::new(Value::Num(2)))), Box::new(Value::Num(1)));
        assert_eq!(p, Pipe::Seq(vec![assign("split_runs", Some(rhs)), parse("split_bits").unwrap()]));
        assert_eq!(parse("rewrites = none").unwrap(), assign("rewrites", None));
        assert_eq!(parse("relate = 0").unwrap(), assign("relate", Some(Value::Num(0))));
        assert_eq!(parse("cut = 1").unwrap(), assign("cut", Some(Value::Num(1))));
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
        ] {
            let p = parse(ok).unwrap();
            assert_eq!(parse(&show(&p)).unwrap(), p, "{ok}: {}", show(&p));
            assert_eq!(parse(&pretty(&p)).unwrap(), p, "{ok}: {}", pretty(&p));
        }
        assert_eq!(show(&parse("split_runs=vars*2|rewrite").unwrap()), "split_runs = vars * 2 | rewrite");
        same("(with rewrites=8 semi_leaves=2 rewrite)", "(rewrites = 8 | semi_leaves = 2 | rewrite)");
        same("(with rewrites=polish_rewrites (wins 8 id))", "(rewrites = polish_rewrites | (wins 8 id))");
        same("(with relate_leaves=10 (off clustered) | rewrite | tfunc)", "(relate_leaves = 10 | (off clustered) | rewrite | tfunc)");
        same("(with bit_splits=2 rewrite)", "(bit_split_budget = 2 | rewrite)");
        same("(time-limit 500) | rewrite", "time_limit = 500 | rewrite");
        same("(time-limit 0) | rewrite", "time_limit = none | rewrite");
        same("(time-limit (size * 10)) | rewrite", "time_limit = size * 10 | rewrite");
        for (bad, msg) in [
            ("(if (size = 3) id)", "compare with =="),
            ("(filter (vars = 2 || mul > 1))", "compare with =="),
            ("(if size = 3 id)", "compare with =="),
            ("(fix n = 3 id)", "compare with =="),
            ("nope = 1", "unknown variable nope"),
            ("size = 1", "cannot be assigned"),
            ("mixed = 1", "cannot be assigned"),
            ("keep = 1", "--passes keep=N"),
            ("restarts = 1", "-m N"),
            ("relate = none", "switch"),
            ("split_runs = none + 1", "none stands only alone"),
            ("split_runs = on", "unknown number on"),
            ("split_runs = mixed", "unknown number mixed"),
            ("split_runs =", "found the end"),
        ] {
            let e = parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }
}
