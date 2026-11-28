//! The types of the pipeline language and the signatures of functions: `Ty`, `Param`, `Sig`
//! and the calling kinds `Kind`.

use std::fmt;

/// A parameter or result type; `pipe` is `group->group`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    Num,
    Term,
    /// `term?`: one candidate or none, only as a result.
    MaybeTerm,
    Group,
    Name,
    /// A string literal `"..."`.
    Text,
    /// A value only formatted (`print`): a number, a text, a name, candidates or a function.
    Any,
    /// `A->B`, `A->B->C` being `A->(B->C)`.
    Fn(Box<Ty>, Box<Ty>),
}

impl Ty {
    const WORDS: [(&'static str, Ty); 7] = [("num", Ty::Num), ("term", Ty::Term), ("term?", Ty::MaybeTerm), ("group", Ty::Group), ("name", Ty::Name), ("text", Ty::Text), ("any", Ty::Any)];

    pub fn pipe() -> Ty {
        Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Group))
    }

    pub fn is_pipe(&self) -> bool {
        matches!(self, Ty::Fn(a, b) if **a == Ty::Group && **b == Ty::Group)
    }

    /// Whether an argument of this type is written as an expression: `num`, evaluated once at
    /// the call, or `term->num` and `group->num`, evaluated on the input they are given.
    pub fn is_expr(&self) -> bool {
        match self {
            Ty::Num => true,
            Ty::Fn(a, b) => matches!(**a, Ty::Term | Ty::Group) && **b == Ty::Num,
            _ => false,
        }
    }

    /// Whether an argument of this type is written as a step: a function that gives
    /// candidates (`pipe`, `term->term`, `term->group`, ...).
    pub fn is_step(&self) -> bool {
        matches!(self, Ty::Fn(_, b) if **b != Ty::Num)
    }

    /// Whether this is a function value's type: one input, term or group, to num, term,
    /// term? or group.
    pub fn is_function(&self) -> bool {
        matches!(self, Ty::Fn(a, b) if matches!(**a, Ty::Term | Ty::Group) && matches!(**b, Ty::Num | Ty::Term | Ty::MaybeTerm | Ty::Group))
    }

    /// Whether a value of this type can be given where `want` is wanted, converted as the
    /// calling kinds convert at a joint: a function over terms runs on each candidate (or the
    /// main one, for a group or a number), a `group->num` one on the one candidate it is given,
    /// and a function giving a number, where a number is wanted, on the input of the step.
    pub fn fits(&self, want: &Ty) -> bool {
        if self == want {
            return true;
        }
        match (self, want) {
            (Ty::Fn(a, b), Ty::Fn(c, d)) => matches!(
                (&**a, &**b, &**c, &**d),
                (Ty::Term, Ty::Term | Ty::MaybeTerm | Ty::Group, Ty::Group, Ty::Group) | (Ty::Term, Ty::Num, Ty::Group, Ty::Num) | (Ty::Group, Ty::Num, Ty::Term, Ty::Num) | (Ty::Term, Ty::Term, Ty::Term, Ty::MaybeTerm)
            ),
            (Ty::Fn(_, b), Ty::Num) => **b == Ty::Num,
            _ => false,
        }
    }

    /// Reads `num`, `pipe`, `term->num`, `term->group->num`, ...
    pub fn parse(s: &str) -> Result<Ty, String> {
        let unknown = |w: &str| format!("unknown type {w}; known: num term term? group name text any pipe, and A->B");
        let mut parts: Vec<&str> = s.split("->").collect();
        let atom = |w: &str| if w == "pipe" { Some(Ty::pipe()) } else { Ty::WORDS.iter().find(|(n, _)| *n == w).map(|(_, t)| t.clone()) };
        let mut ty = atom(parts.pop().unwrap()).ok_or_else(|| unknown(s))?;
        while let Some(w) = parts.pop() {
            let a = atom(w).ok_or_else(|| unknown(if w.is_empty() { s } else { w }))?;
            if a == Ty::MaybeTerm {
                return Err(format!("term? is only a result, in {s}"));
            }
            ty = Ty::Fn(Box::new(a), Box::new(ty));
        }
        Ok(ty)
    }

    /// What an argument of this type is, for messages.
    pub(crate) fn what(&self) -> &'static str {
        match self {
            _ if self.is_expr() => "an expression",
            _ if self.is_pipe() => "a pipeline",
            Ty::Fn(..) => "a function",
            Ty::Group => "a group variable",
            Ty::Name => "a name",
            Ty::Text => "a text",
            Ty::Any => "a value",
            _ => "a candidate",
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            _ if self.is_pipe() => write!(f, "pipe"),
            Ty::Fn(a, b) if matches!(**a, Ty::Fn(..)) && !a.is_pipe() => write!(f, "({a})->{b}"),
            Ty::Fn(a, b) => write!(f, "{a}->{b}"),
            t => write!(f, "{}", Ty::WORDS.iter().find(|(_, w)| w == t).unwrap().0),
        }
    }
}

fn noun(t: &Ty) -> &'static str {
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
        write!(f, "{}:{}{suffix}", self.name, self.ty)
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
    /// `group -> term?`: on the whole list, the candidate picked or none replacing it.
    Pick,
    /// `text -> group`: the candidates read from a text.
    FromText,
    /// `term -> text`: a text of the main candidate.
    TermText,
    /// An operator: no input, every operand written.
    Op,
}

impl Kind {
    pub const ALL: [(Kind, &'static str); 10] = [
        (Kind::Group, "on the whole list (group -> group)"),
        (Kind::Each, "on each candidate (term -> term)"),
        (Kind::Alt, "alternatives, on each candidate, none when no form is found (term -> term?)"),
        (Kind::Main, "on the main candidate, the result replacing the list (term -> group)"),
        (Kind::TermNum, "numbers of the main candidate (term -> num)"),
        (Kind::GroupNum, "numbers of the whole list (group -> num)"),
        (Kind::Pick, "one candidate of the list, or none (group -> term?)"),
        (Kind::FromText, "candidates read from a text (text -> group)"),
        (Kind::TermText, "texts of the main candidate (term -> text)"),
        (Kind::Op, "operators, written between their operands (! before its one)"),
    ];

    pub(crate) fn of(input: &Ty, result: &Ty) -> Option<Kind> {
        Some(match (input, result) {
            (Ty::Group, Ty::Group) => Kind::Group,
            (Ty::Term, Ty::Term) => Kind::Each,
            (Ty::Term, Ty::MaybeTerm) => Kind::Alt,
            (Ty::Term, Ty::Group) => Kind::Main,
            (Ty::Term | Ty::MaybeTerm, Ty::Num) => Kind::TermNum,
            (Ty::Group, Ty::Num) => Kind::GroupNum,
            (Ty::Group, Ty::MaybeTerm) => Kind::Pick,
            (Ty::Text, Ty::Group) => Kind::FromText,
            (Ty::Term | Ty::MaybeTerm, Ty::Text) => Kind::TermText,
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
    /// The implicit input, `term` or `group`; `None` for an operator.
    pub input: Option<Param>,
    pub result: Ty,
    /// `@pipe`: `|` fills in the input, so it can be a step.
    pub pipe: bool,
    /// `@timed`: a call past the time limit is skipped, giving its input.
    pub timed: bool,
    /// `@simplify_only`: only in `pipeline`.
    pub simplify_only: bool,
    /// `@uncounted` (with `@timed`): its skip makes no cut and no `time_limit/skipped`.
    pub uncounted: bool,
    /// `@switch`: a pass with a switch of its name (`rust_vars::INNER`), on until turned off.
    pub switch: bool,
    /// The comment line before the declaration.
    pub doc: String,
}

impl Sig {
    pub fn kind(&self) -> Kind {
        self.input.as_ref().map_or(Kind::Op, |i| Kind::of(&i.ty, &self.result).unwrap())
    }

    /// Whether it is an operator, written infix (`a + b`) or prefix (`!a`), not by name.
    pub fn is_op(&self) -> bool {
        self.input.is_none()
    }

    /// Whether it gives a number, so belongs in expressions, not steps.
    pub fn is_number(&self) -> bool {
        self.result == Ty::Num
    }

    /// Whether it gives a text, so ends a top-level statement or is the input of `parse`.
    pub fn is_text(&self) -> bool {
        self.result == Ty::Text
    }

    /// The parameter an argument at position `i` of a call is for: the last one for the
    /// arguments of a `TYPE...` parameter.
    pub fn param(&self, i: usize) -> &Param {
        self.params.get(i).unwrap_or_else(|| self.params.last().unwrap())
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
                Rep::Many => format!("one or more {}s", noun(&p.ty)),
                Rep::Opt => format!("an optional {}", noun(&p.ty)),
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
        if self.pipe {
            attrs += "@pipe ";
        }
        if self.switch {
            attrs += "@switch ";
        }
        if self.timed {
            attrs += "@timed ";
        }
        if self.simplify_only {
            attrs += "@simplify_only ";
        }
        if self.uncounted {
            attrs += "@uncounted ";
        }
        format!("(extern {attrs}{self})")
    }
}

/// `(NAME PARAM:TYPE ... INPUT:TYPE) RESULT`.
impl fmt::Display for Sig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for p in self.params.iter().chain(&self.input) {
            write!(f, " {p}")?;
        }
        write!(f, ") {}", self.result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn types() {
        for (s, shown) in [
            ("num", "num"),
            ("term?", "term?"),
            ("pipe", "pipe"),
            ("group->group", "pipe"),
            ("term->num", "term->num"),
            ("term->group->num", "term->group->num"),
            ("pipe->num", "pipe->num"),
            ("term->term?", "term->term?"),
            ("group->group->group", "group->pipe"),
        ] {
            let t = Ty::parse(s).unwrap();
            assert_eq!(t.to_string(), shown, "{s}");
            assert_eq!(Ty::parse(shown).unwrap(), t, "{s}");
        }
        let curried = Ty::parse("term->group->num").unwrap();
        assert_eq!(curried, Ty::Fn(Box::new(Ty::Term), Box::new(Ty::Fn(Box::new(Ty::Group), Box::new(Ty::Num)))));
        assert_eq!(Ty::Fn(Box::new(Ty::parse("term->num").unwrap()), Box::new(Ty::Num)).to_string(), "(term->num)->num");
        assert!(Ty::parse("pipe").unwrap().is_pipe() && Ty::parse("term->num").unwrap().is_expr() && !Ty::parse("term->term").unwrap().is_expr());
        for (bad, msg) in [("int", "unknown type int"), ("term->", "unknown type term->"), ("->num", "unknown type ->num"), ("term?->num", "term? is only a result")] {
            let e = Ty::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }
}
