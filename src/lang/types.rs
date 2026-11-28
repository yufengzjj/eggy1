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
    /// The result of a function declared without one (`print`, `assert`): a step that gives it
    /// passes its input on.
    Nothing,
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

    /// Whether a value of this type can be given where `want` is wanted, converted as a joint
    /// converts: a function over terms giving candidates runs on each candidate of a group, a
    /// `group->num` one on the one candidate it is given, and a function giving a number, where
    /// a number is wanted, on the input of the step.
    pub fn fits(&self, want: &Ty) -> bool {
        if self == want {
            return true;
        }
        match (self, want) {
            (Ty::Fn(a, b), Ty::Fn(c, d)) => matches!(
                (&**a, &**b, &**c, &**d),
                (Ty::Term, Ty::Term | Ty::MaybeTerm | Ty::Group, Ty::Group, Ty::Group) | (Ty::Group, Ty::Num, Ty::Term, Ty::Num) | (Ty::Term, Ty::Term, Ty::Term, Ty::MaybeTerm)
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
            _ => "a term",
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            _ if self.is_pipe() => write!(f, "pipe"),
            Ty::Fn(a, b) if matches!(**a, Ty::Fn(..)) && !a.is_pipe() => write!(f, "({a})->{b}"),
            Ty::Fn(a, b) => write!(f, "{a}->{b}"),
            Ty::Nothing => Ok(()),
            t => write!(f, "{}", Ty::WORDS.iter().find(|(_, w)| w == t).unwrap().0),
        }
    }
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
    /// `term -> group`: on each candidate, the results joined.
    Join,
    /// `term -> num`: on one candidate, 0 for none.
    TermNum,
    /// `group -> num`: on the whole list, 0 without candidates.
    GroupNum,
    /// `group -> term?`: on the whole list, the candidate picked or none replacing it.
    Pick,
    /// `text -> group`: the candidates read from a text.
    FromText,
    /// `term -> text`: a text of one candidate.
    TermText,
    /// An operator: no input, every operand written.
    Op,
    /// No input and no result (`print`, `assert`): run for what it does, the input passing on.
    Effect,
}

impl Kind {
    pub const ALL: [(Kind, &'static str); 11] = [
        (Kind::Group, "on the whole group (group -> group)"),
        (Kind::Each, "on each element (term -> term)"),
        (Kind::Alt, "alternatives, on each element, none when no form is found (term -> term?)"),
        (Kind::Join, "on each element, the result groups joined (term -> group)"),
        (Kind::TermNum, "numbers of one term (term -> num)"),
        (Kind::GroupNum, "numbers of the whole group (group -> num)"),
        (Kind::Pick, "one element of the group, or none (group -> term?)"),
        (Kind::FromText, "a group read from a text (text -> group)"),
        (Kind::TermText, "texts of one term (term -> text)"),
        (Kind::Op, "operators, written between their operands (! before its one)"),
        (Kind::Effect, "no result: run for what they do, the input passing on"),
    ];

    pub(crate) fn of(input: &Ty, result: &Ty) -> Option<Kind> {
        Some(match (input, result) {
            (Ty::Group, Ty::Group) => Kind::Group,
            (Ty::Term, Ty::Term) => Kind::Each,
            (Ty::Term, Ty::MaybeTerm) => Kind::Alt,
            (Ty::Term, Ty::Group) => Kind::Join,
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
    /// The last parameter, which a call may leave out to take the step's input; `None` for an
    /// operator and a function without a result.
    pub input: Option<Param>,
    /// `Ty::Nothing` for a function declared without a result.
    pub result: Ty,
    /// `@timed`: a call past the time limit is skipped, giving its input.
    pub timed: bool,
    /// `@uncounted` (with `@timed`): its skip makes no cut and no `time_limit/skipped`.
    pub uncounted: bool,
    /// `@switch`: a pass with a switch of its name (`rust_vars::INNER`), on until turned off.
    pub switch: bool,
    /// The comment line before the declaration.
    pub doc: String,
}

impl Sig {
    /// Whether a call written for `self` fits `o`: the same parameter and input types and
    /// result, the names aside.
    pub fn same_shape(&self, o: &Sig) -> bool {
        let shape = |p: &Param| (p.ty.clone(), p.rep);
        self.params.iter().map(shape).eq(o.params.iter().map(shape)) && self.input.as_ref().map(shape) == o.input.as_ref().map(shape) && self.result == o.result
    }

    pub fn kind(&self) -> Kind {
        match &self.input {
            Some(i) => Kind::of(&i.ty, &self.result).unwrap(),
            None if self.result == Ty::Nothing => Kind::Effect,
            None => Kind::Op,
        }
    }

    /// Whether it is an operator, written infix (`a + b`) or prefix (`!a`), not by name.
    pub fn is_op(&self) -> bool {
        self.input.is_none() && self.result != Ty::Nothing
    }

    /// Whether it gives no value, so a step of it passes its input on.
    pub fn gives_nothing(&self) -> bool {
        self.result == Ty::Nothing
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

    /// How many arguments a call takes, the input among them: `3 arguments; | gives the last`.
    pub fn arity(&self) -> String {
        let input = usize::from(self.input.is_some());
        let least = self.params.iter().filter(|p| p.rep != Rep::Opt).count() + input;
        let opt = self.params.iter().filter(|p| p.rep == Rep::Opt).count();
        let n = match (self.params.iter().any(|p| p.rep == Rep::Many), opt) {
            (true, _) => format!("{least} or more arguments"),
            (false, 0) if least == 1 => "1 argument".into(),
            (false, 0) => format!("{least} arguments"),
            (false, 1) => format!("{least} or {} arguments", least + 1),
            (false, k) => format!("{least} to {} arguments", least + k),
        };
        match &self.input {
            Some(i) if matches!(i.ty, Ty::Term | Ty::MaybeTerm | Ty::Group) => format!("{n}; | gives the last"),
            _ => n,
        }
    }

    /// The declaration as `src/builtins.pipe` writes it.
    pub fn decl(&self) -> String {
        let mut attrs = String::new();
        if self.switch {
            attrs += "@switch ";
        }
        if self.timed {
            attrs += "@timed ";
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
        match self.result {
            Ty::Nothing => write!(f, ")"),
            ref r => write!(f, ") {r}"),
        }
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
