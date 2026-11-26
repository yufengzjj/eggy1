//! The pipeline language (`docs/pipe-language.md`): `a | b` runs `b` on the candidates of
//! `a`, `(FORM args...)` is a combinator or a pass with arguments, conditions are
//! expressions (`(if (mul >= 4 && shift < 1) (off small_blocks))`). Parsed into `sched::Pipe`.

use crate::pipe::{COUNTS, FEATURES, is_cond, is_pass};
use crate::sched::{Cond, INNER, LIMITS, Pipe};

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
    KeyVal(String, String),
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
            '+' | '-' | '*' | '/' => (Tok::Arith(c), 1),
            c if c.is_ascii_digit() => {
                let n: String = cs[i..].iter().take_while(|c| c.is_ascii_digit()).collect();
                let len = n.len();
                (Tok::Num(n.parse().map_err(|_| format!("number too large: {n}"))?), len)
            }
            c if name_start(c) => {
                let n: String = cs[i..].iter().take_while(|c| name_char(**c)).collect();
                let len = n.len();
                if cs.get(i + len) == Some(&'=') && cs.get(i + len + 1) != Some(&'=') {
                    let v: String = cs[i + len + 1..].iter().take_while(|c| !c.is_whitespace() && **c != '(' && **c != ')').collect();
                    let vl = v.len();
                    (Tok::KeyVal(n, v), len + 1 + vl)
                } else {
                    (Tok::Name(n), len)
                }
            }
            _ => return Err(format!("unexpected character {c:?} in pipeline")),
        };
        out.push(tok);
        i += len;
    }
    Ok(out)
}

const FORMS: [&str; 22] = [
    "seq", "union", "best", "first", "fix", "if", "retry", "smallest", "scope", "regions", "again", "tag", "cand", "smaller", "wins", "filter", "with", "save", "load",
    "label", "off", "egglog",
];

/// A literal of a condition in disjunctive normal form: negated, and a `Cond` name.
type Lit = (bool, String);
type Dnf = Vec<Vec<Lit>>;

fn and(a: Dnf, b: Dnf) -> Dnf {
    a.iter().flat_map(|x| b.iter().map(move |y| x.iter().chain(y).cloned().collect())).collect()
}

fn not(a: Dnf) -> Dnf {
    a.into_iter().fold(vec![vec![]], |acc, clause| and(acc, clause.into_iter().map(|(n, l)| vec![(!n, l)]).collect()))
}

/// One side of a comparison: a number, a feature, the main candidate's size, or a
/// register's size times `P/Q`.
#[derive(Debug)]
enum Side {
    Num(u64),
    Feature(String),
    Reg(String, u64, u64),
}

struct Parser {
    toks: Vec<Tok>,
    at: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn peek2(&self) -> Option<&Tok> {
        self.toks.get(self.at + 1)
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
        let mut stages = vec![self.stage()?];
        while self.peek() == Some(&Tok::Bar) {
            self.at += 1;
            stages.push(self.stage()?);
        }
        Ok(if stages.len() == 1 { stages.pop().unwrap() } else { Pipe::Seq(stages) })
    }

    fn stage(&mut self) -> Result<Pipe, String> {
        match self.next() {
            Some(Tok::Name(n)) if FORMS.contains(&n.as_str()) && n != "egglog" => Err(format!("{n} needs parentheses: ({n} ...)")),
            Some(Tok::Name(n)) if is_pass(&n) => Ok(Pipe::Pass(n)),
            Some(Tok::Name(n)) => Err(format!("unknown pass {n}; known: {}", crate::pipe::names().join(" "))),
            Some(Tok::Open) => {
                let p = match self.peek() {
                    Some(Tok::Name(n)) if FORMS.contains(&n.as_str()) && !(n == "egglog" && self.peek2() == Some(&Tok::Close)) => {
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

    fn count(&mut self) -> Result<String, String> {
        match self.next() {
            Some(Tok::Num(n)) => Ok(n.to_string()),
            Some(Tok::Name(n)) if COUNTS.contains(&n.as_str()) => Ok(n),
            x => Err(format!("expected a number or one of {}, found {}", COUNTS.join(" "), show_tok(x.as_ref()))),
        }
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
                    ("if", 1) => Pipe::If(c, b(ps.remove(0)), b(Pipe::Pass("id".into()))),
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
                let (mut off, mut set) = (Vec::new(), Vec::new());
                while let Some(Tok::KeyVal(k, v)) = self.peek().cloned() {
                    self.at += 1;
                    if k == "off" {
                        for n in v.split(',') {
                            off.push(INNER.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown off name {n}; known: {}", INNER.join(",")))?);
                        }
                        continue;
                    }
                    let known = ["rewrites", "semi_leaves", "relate_leaves", "bit_splits"];
                    if !known.contains(&k.as_str()) {
                        return Err(format!("unknown setting {k}; known: off {}", known.join(" ")));
                    }
                    if !(v.parse::<usize>().is_ok() || LIMITS.iter().any(|(n, _)| *n == v)) {
                        return Err(format!("bad value {v} for {k}"));
                    }
                    set.push((k, v));
                }
                if off.is_empty() && set.is_empty() {
                    return Err("with needs KEY=VALUE settings".into());
                }
                let p = self.pipe()?;
                let p = if set.is_empty() { p } else { Pipe::With(set, b(p)) };
                if off.is_empty() { p } else { Pipe::Off(off, b(p)) }
            }
            "save" | "load" | "label" | "egglog" => Pipe::Pass(format!("{f}/{}", self.name(&format!("a name after {f}"))?)),
            "off" => {
                let mut ps = Vec::new();
                while !self.at_close() {
                    let n = self.name("a pass name after off")?;
                    if !INNER.contains(&n.as_str()) {
                        return Err(format!("unknown off name {n}; known: {}", INNER.join(",")));
                    }
                    ps.push(Pipe::Pass(format!("off/{n}")));
                }
                match ps.len() {
                    0 => return Err("off needs a pass name".into()),
                    1 => ps.pop().unwrap(),
                    _ => Pipe::Seq(ps),
                }
            }
            _ => unreachable!(),
        })
    }

    /// A condition argument: a name, `!` and a name, or a parenthesized expression.
    fn cond(&mut self) -> Result<Cond, String> {
        let d = match self.peek() {
            Some(Tok::Open) => self.primary()?,
            Some(Tok::Not) => {
                self.at += 1;
                not(if self.peek() == Some(&Tok::Open) { self.primary()? } else { self.cond_name()? })
            }
            _ => self.cond_name()?,
        };
        Ok(Cond(d))
    }

    fn cond_name(&mut self) -> Result<Dnf, String> {
        let n = self.name("a condition")?;
        if FEATURES.contains(&n.as_str()) || !is_cond(&n) {
            return Err(format!("unknown condition {n}; known: {} or a comparison such as (mul >= 4)", crate::pipe::CONDS.join(" ")));
        }
        Ok(vec![vec![(false, n)]])
    }

    fn or(&mut self) -> Result<Dnf, String> {
        let mut d = self.and()?;
        while self.peek() == Some(&Tok::Or) {
            self.at += 1;
            d.extend(self.and()?);
        }
        Ok(d)
    }

    fn and(&mut self) -> Result<Dnf, String> {
        let mut d = self.unary()?;
        while self.peek() == Some(&Tok::And) {
            self.at += 1;
            d = and(d, self.unary()?);
        }
        Ok(d)
    }

    fn unary(&mut self) -> Result<Dnf, String> {
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            return Ok(not(self.unary()?));
        }
        let comparison = match (self.peek(), self.peek2()) {
            (Some(Tok::Num(_)), _) => true,
            (Some(Tok::Name(_)), Some(Tok::Cmp(_) | Tok::Arith(_))) => true,
            (Some(Tok::Open), Some(Tok::Name(n))) => n == "size" && matches!(self.toks.get(self.at + 2), Some(Tok::Name(_))),
            _ => false,
        };
        if comparison {
            return self.comparison();
        }
        match self.peek() {
            Some(Tok::Open) => self.primary(),
            _ => self.cond_name(),
        }
    }

    /// `( expr )` or a quantifier.
    fn primary(&mut self) -> Result<Dnf, String> {
        self.expect(Tok::Open, "(")?;
        if let Some(Tok::Name(n)) = self.peek()
            && (n == "any" || n == "all")
        {
            return Err(format!("({n} ...) is not supported yet"));
        }
        let d = self.or()?;
        self.expect(Tok::Close, ")")?;
        Ok(d)
    }

    fn side(&mut self) -> Result<Side, String> {
        let s = match self.next() {
            Some(Tok::Num(n)) => Side::Num(n),
            Some(Tok::Name(n)) if FEATURES.contains(&n.as_str()) => Side::Feature(n),
            Some(Tok::Open) => {
                let k = self.name("size")?;
                if k != "size" {
                    return Err(format!("expected (size R), found ({k}"));
                }
                let r = self.name("a register")?;
                self.expect(Tok::Close, ")")?;
                Side::Reg(r, 1, 1)
            }
            x => return Err(format!("expected a number, a feature ({}) or (size R), found {}", FEATURES.join(" "), show_tok(x.as_ref()))),
        };
        let Side::Reg(r, 1, 1) = s else { return Ok(s) };
        if self.peek() != Some(&Tok::Arith('*')) {
            return Ok(Side::Reg(r, 1, 1));
        }
        self.at += 1;
        let (Some(Tok::Num(p)), Some(Tok::Arith('/')), Some(Tok::Num(q))) = (self.next(), self.next(), self.next()) else {
            return Err("expected (size R) * P/Q".into());
        };
        Ok(Side::Reg(r, p, q))
    }

    /// The comparisons that are `Cond` literals: a feature against a number, `size` against
    /// `(size R)` or `(size R) * P/Q`.
    fn comparison(&mut self) -> Result<Dnf, String> {
        let a = self.side()?;
        let op = match self.next() {
            Some(Tok::Cmp(op)) => op,
            x => return Err(format!("expected a comparison, found {}", show_tok(x.as_ref()))),
        };
        let b = self.side()?;
        let lit = |neg: bool, l: String| vec![vec![(neg, l)]];
        Ok(match (a, op, b) {
            (Side::Feature(f), op, Side::Num(n)) => {
                let at = |n: u64| format!("{f}:{n}");
                match op {
                    ">=" => lit(false, at(n)),
                    ">" => lit(false, at(n + 1)),
                    "<" => lit(true, at(n)),
                    "<=" => lit(true, at(n + 1)),
                    "==" => and(lit(false, at(n)), lit(true, at(n + 1))),
                    _ => not(and(lit(false, at(n)), lit(true, at(n + 1)))),
                }
            }
            (Side::Feature(f), op, Side::Reg(r, 1, 1)) if f == "size" => match op {
                "<" => lit(false, format!("lt:{r}")),
                ">=" => lit(true, format!("lt:{r}")),
                ">" => lit(false, format!("gt:{r}")),
                "<=" => lit(true, format!("gt:{r}")),
                "==" => lit(false, format!("eq:{r}")),
                _ => lit(true, format!("eq:{r}")),
            },
            (Side::Feature(f), op @ ("<=" | ">"), Side::Reg(r, p, q)) if f == "size" => lit(op == ">", format!("le:{p}/{q}:{r}")),
            (a, op, b) => return Err(format!("comparison {a:?} {op} {b:?} is not supported yet")),
        })
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
            Tok::KeyVal(k, v) => format!("{k}={v}"),
        },
    }
}

/// Parses `s` in the pipeline language.
pub fn parse(s: &str) -> Result<Pipe, String> {
    let mut p = Parser { toks: lex(s)?, at: 0 };
    let pipe = p.pipe()?;
    if p.at < p.toks.len() {
        return Err(format!("unexpected {} after the pipeline", show_tok(p.peek())));
    }
    Ok(pipe)
}

/// Whether `s` is written in the old `seq(a,b)` syntax: a name directly followed by `(`.
pub fn is_old_syntax(s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    cs.windows(2).any(|w| name_char(w[0]) && w[1] == '(')
}

/// Parses `s` in either syntax.
pub fn parse_any(s: &str) -> Result<Pipe, String> {
    if is_old_syntax(s) { Pipe::parse(s) } else { parse(s) }
}

fn show_lit((neg, l): &Lit) -> String {
    if let Some((f, n)) = l.split_once(':')
        && FEATURES.contains(&f)
    {
        return format!("{f} {} {n}", if *neg { "<" } else { ">=" });
    }
    let reg = |op: &str, r: &str| format!("size {op} (size {r})");
    match l.split_once(':') {
        Some(("lt", r)) => reg(if *neg { ">=" } else { "<" }, r),
        Some(("gt", r)) => reg(if *neg { "<=" } else { ">" }, r),
        Some(("eq", r)) => reg(if *neg { "!=" } else { "==" }, r),
        Some(("le", pr)) => {
            let (pq, r) = pr.rsplit_once(':').unwrap();
            format!("size {} (size {r}) * {pq}", if *neg { ">" } else { "<=" })
        }
        _ => format!("{}{l}", if *neg { "!" } else { "" }),
    }
}

/// `c` as a condition argument.
pub fn show_cond(c: &Cond) -> String {
    if let [clause] = c.0.as_slice()
        && let [(neg, l)] = clause.as_slice()
        && !l.contains(':')
    {
        return format!("{}{l}", if *neg { "!" } else { "" });
    }
    let clause = |c: &Vec<Lit>| c.iter().map(show_lit).collect::<Vec<_>>().join(" && ");
    format!("({})", c.0.iter().map(clause).collect::<Vec<_>>().join(" || "))
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

/// `p` in the pipeline language, on one line.
pub fn show(p: &Pipe) -> String {
    let stages = |ps: &[Pipe]| ps.iter().map(stage).collect::<Vec<_>>();
    let with = |head: Vec<String>, p: &Pipe| {
        let mut a = head;
        a.push(show(p));
        a
    };
    match p {
        Pipe::Pass(n) => match n.split_once('/') {
            Some((h @ ("save" | "load" | "label" | "off" | "egglog"), r)) => form(h, &[r.to_string()]),
            _ => n.clone(),
        },
        Pipe::Seq(ps) if ps.len() > 1 => stages(ps).join(" | "),
        Pipe::Seq(ps) => form("seq", &stages(ps)),
        Pipe::Union(ps) => form("union", &stages(ps)),
        Pipe::First(ps) => form("first", &stages(ps)),
        Pipe::Best(k, ps) => form("best", &[vec![k.clone()], stages(ps)].concat()),
        Pipe::Fix(n, p) => form("fix", &with(vec![n.clone()], p)),
        Pipe::Wins(n, p) => form("wins", &with(vec![n.clone()], p)),
        Pipe::If(c, a, b) if **b == Pipe::Pass("id".into()) => form("if", &[show_cond(c), stage(a)]),
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
        Pipe::Off(ns, p) => {
            let off = format!("off={}", ns.join(","));
            match &**p {
                Pipe::With(kv, q) => form("with", &with([vec![off], kv.iter().map(|(k, v)| format!("{k}={v}")).collect()].concat(), q)),
                q => form("with", &with(vec![off], q)),
            }
        }
        Pipe::With(kv, p) => form("with", &with(kv.iter().map(|(k, v)| format!("{k}={v}")).collect(), p)),
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
        Pipe::Best(k, ps) => nested("best", vec![k.clone()], many(ps)),
        Pipe::Fix(n, q) => nested("fix", vec![n.clone()], vec![(q, false)]),
        Pipe::Wins(n, q) => nested("wins", vec![n.clone()], vec![(q, false)]),
        Pipe::If(c, a, b) if **b == Pipe::Pass("id".into()) => nested("if", vec![show_cond(c)], vec![(a, true)]),
        Pipe::If(c, a, b) => nested("if", vec![show_cond(c)], vec![(a, true), (b, true)]),
        Pipe::Retry(c, a, b) => nested("retry", vec![show_cond(c)], vec![(a, true), (b, true)]),
        Pipe::Smallest(q) => nested("smallest", vec![], vec![(q, false)]),
        Pipe::Scope(q) => nested("scope", vec![], vec![(q, false)]),
        Pipe::Regions(q) => nested("regions", vec![], vec![(q, false)]),
        Pipe::Again(q) => nested("again", vec![], vec![(q, false)]),
        Pipe::Tag(n, q) => nested("tag", vec![n.clone()], vec![(q, false)]),
        Pipe::Cand(n, q) => nested("cand", vec![n.clone()], vec![(q, false)]),
        Pipe::Smaller(n, q) => nested("smaller", vec![n.clone()], vec![(q, false)]),
        Pipe::Off(ns, q) => {
            let mut fixed = vec![format!("off={}", ns.join(","))];
            let q = match &**q {
                Pipe::With(kv, r) => {
                    fixed.extend(kv.iter().map(|(k, v)| format!("{k}={v}")));
                    &**r
                }
                q => q,
            };
            nested("with", fixed, vec![(q, false)])
        }
        Pipe::With(kv, q) => nested("with", kv.iter().map(|(k, v)| format!("{k}={v}")).collect(), vec![(q, false)]),
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

    /// The default pipelines as written in the old syntax before they were rewritten.
    const OLD_PIPELINE: &str = "seq(smallest(seq(fix(1,if(opaque,seq(union(id,prepass),if(minimal,take_minimal,egglog/first)),retry(rerun_input+mixed+!minimal,seq(prepass,if(minimal,take_minimal,egglog/first)),seq(union(id,prepass),egglog/rerun_input)))),if(moved,fix(restarts,seq(prepass,if(minimal,take_minimal,egglog/later)))),if(moved,fix(extra,if(rebuilds,seq(prepass,if(minimal,take_minimal,egglog/later))))),polish)),if(printed+!input,tag(rerun_printed,best(1,id,seq(reprint,smallest(seq(fix(1,if(opaque,seq(union(id,prepass),if(minimal,take_minimal,egglog/first)),retry(rerun_input+mixed+!minimal,seq(prepass,if(minimal,take_minimal,egglog/first)),seq(union(id,prepass),egglog/rerun_input)))),if(moved,fix(printed,seq(prepass,if(minimal,take_minimal,egglog/later)))),polish)))))))";
    const OLD_PREPASS: &str = "scope(seq(save/t0,if(!mul:1,off/poly_mba),if(!mul:1+!shift:1+!bitconst:1,off/lowbits),if(mul:4+!shift:1,off/small_blocks),lowbits,unshift,save/t,cand(first,first(tfunc_whole,seq(rewrite_top,cluster_top,relate,tfunc))),best(1,id,cand(unified,seq(load/t,unify_operands,filter(!eq:t),with(rewrites=unified_rewrites,first(tfunc_whole,seq(rewrite,within,cluster_regions,relate,within,tfunc)))))),save/r,union(id,cand(no_wide,if(used_wide,seq(load/t,off(wide_blocks,first(tfunc_whole,seq(rewrite_top,cluster_top,relate,tfunc))),save/n,filter(lt:r)),none)),cand(no_wide_abstracted,seq(load/n,off(wide_blocks,union(over_const_bitwise,over_shared_bitwise)),filter(lt:r+le:3/4:n))),cand(split_bits,if(fits_split,seq(split_bits,filter(!eq:r)),none)),cand(halve_first,seq(halve,filter(!eq:r),first(tfunc_whole,seq(rewrite_top,cluster_top,tfunc)))),cand(over_products,seq(over_products,filter(!eq:r))),cand(over_const_bitwise,seq(over_const_bitwise,filter(!eq:r))),cand(over_shared_bitwise,seq(over_shared_bitwise,filter(!eq:r))),cand(halve_input,with(semi_leaves=2,if(tiny,none,seq(load/t,halve,filter(!eq:t),first(tfunc_whole,seq(rewrite_top,cluster_top,tfunc))))))),finish,save/f,filter(!abstracted|le:3/4:f),save/b,label/b,cand(unclustered,if(used_clustered+few_rewrites,seq(load/t,if(!replaceable,off(clustered,with(relate_leaves=unclustered_relate_leaves+rewrites=unclustered_rewrites,seq(rewrite,within,relate,within,tfunc,finish,drop_identities))),none)),none)),label/b,save/u,load/b,best(keep,id),save/m,union(seq(load/u,filter(lt:m)),load/m,seq(load/u,filter(gt:m+lt:t0))),pre_done))";
    const OLD_POLISH: &str = "scope(with(rewrites=polish_rewrites,wins(8,seq(smaller(polish/push_not,seq(polish/push_not,drop_identities)),smaller(polish/join_constants,seq(polish/join_constants,drop_identities)),smaller(polish/join_linear,with(semi_leaves=2,seq(polish/join_linear,drop_identities))),smaller(polish/over_const_bitwise,seq(polish/over_const_bitwise,drop_identities)),smaller(polish/over_shared_bitwise,seq(polish/over_shared_bitwise,drop_identities)),smaller(polish/over_products,seq(polish/over_products,drop_identities)),smaller(polish/recombine,seq(polish/recombine,drop_identities)),smaller(polish/shift_cases,seq(polish/shift_cases,drop_identities)),smaller(polish/decompose,seq(polish/decompose,drop_identities)),smaller(polish/factor,seq(polish/factor,drop_identities))))))";
    const OLD_REWRITE: &str = "again(best(1,regions(best(1,simba,small_blocks,wide_blocks)),poly_mba))";
    const OLD_SIMBA: &str = "if(no_leaves,none,if(wide,seq(save/in,best(1,seq(drop_unused,save/d),seq(clustered,save/c),seq(load/d,if(true,none,seq(load/in,first(peel,seq(load/c,peel_clustered)),filter(!eq:in)))))),seq(save/in,if(const_bitwise,best(1,semi_linear),best(1,rebuild_values,common_multiple,related_leaves,if(!cofactor,one_wide_term,none))),filter(lt:in))))";

    #[test]
    fn defaults_match_old_syntax() {
        let d = Passes::default();
        for (old, p) in [(OLD_PIPELINE, &d.pipeline), (OLD_PREPASS, &d.prepass), (OLD_POLISH, &d.polish), (OLD_REWRITE, &d.rewrite), (OLD_SIMBA, &d.simba)] {
            assert_eq!(&Pipe::parse(old).unwrap(), p);
            assert_eq!(&parse(&show(p)).unwrap(), p, "{}", show(p));
            assert_eq!(&parse(&pretty(p)).unwrap(), p, "{}", pretty(p));
            assert_eq!(&parse_any(old).unwrap(), p);
        }
    }

    #[test]
    fn forms_and_conditions() {
        let same = |new: &str, old: &str| assert_eq!(parse(new).unwrap(), Pipe::parse(old).unwrap(), "{new}");
        same("lowbits | rewrite | polish", "seq(lowbits,rewrite,polish)");
        same("(seq rewrite)", "seq(rewrite)");
        same("(if mixed rewrite)", "if(mixed,rewrite,id)");
        same("(if (!minimal || tiny) (rewrite | polish) id)", "if(!minimal|tiny,seq(rewrite,polish),id)");
        same("(if !(minimal && tiny) id)", "if(!minimal|!tiny,id)");
        same("(filter (mul > 3 && vars <= 2))", "filter(mul:4+!vars:3)");
        same("(filter (mul == 2))", "filter(mul:2+!mul:3)");
        same("(filter (size >= (size t) || size == (size r)))", "filter(!lt:t|eq:r)");
        same("(filter (size > (size f) * 3/4))", "filter(!le:3/4:f)");
        same("(with off=relate,tfunc rewrites=8 rewrite)", "off(relate+tfunc,with(rewrites=8,rewrite))");
        same("(with rewrites=8 (with off=relate rewrite))", "with(rewrites=8,off(relate,rewrite))");
        same("(off lowbits relate) | (save t) | (egglog first) | egglog", "seq(seq(off/lowbits,off/relate),save/t,egglog/first,egglog)");
        same("(fix restarts prepass | egglog)", "fix(restarts,seq(prepass,egglog))");
        same("# comment
(best 2 rewrite (scope relate)) # more", "best(2,rewrite,scope(relate))");
        for bad in [
            "nope",
            "(if mixed a | b)",
            "(union rewrite | relate)",
            "(fix many id)",
            "(if nope id)",
            "(filter (any minimal))",
            "(filter (vars < size))",
            "(with nope=1 id)",
            "(off nope)",
            "seq",
            "(retry mixed id)",
            "rewrite)",
        ] {
            assert!(parse(bad).is_err(), "{bad}");
        }
        assert!(is_old_syntax("seq(a,b)") && !is_old_syntax("(seq a b)"));
    }
}
