//! Reads tokens into the syntax tree (`syntax`): `a | b` separates steps, items written side by
//! side in parentheses are a call, `,` separates the positions of a tuple, `NAME = VALUE`
//! assigns, and expressions bind tighter than the side by side items (`(any mul > 1)`).

use super::defs::DefKind;
use super::lexer::{Tok, show_tok};
use super::syntax::{DefItem, Head, Lhs, Node, Pipeline, Stage, Syn};
use super::types::Ty;

pub(crate) const NO_ASSIGN: &str = "an assignment is a step; compare with ==";

struct Reader<'t> {
    toks: &'t [Tok],
    at: usize,
}

/// The pipeline `toks` hold, a top-level statement or the text of a pipeline.
pub(crate) fn statement(toks: &[Tok]) -> Result<Pipeline<'_>, String> {
    let mut r = Reader { toks, at: 0 };
    let p = r.pipeline()?;
    r.end()?;
    Ok(p)
}

/// The right side of an assignment `toks` hold.
pub(crate) fn value(toks: &[Tok]) -> Result<Syn<'_>, String> {
    let mut r = Reader { toks, at: 0 };
    let e = r.rhs()?;
    r.end()?;
    Ok(e)
}

/// The definition item `toks` hold, `s` its text.
pub(crate) fn definition<'t>(toks: &'t [Tok], s: &str) -> Result<DefItem<'t>, String> {
    let mut r = Reader { toks, at: 0 };
    let head = r.head(s)?;
    let body = r.pipeline()?;
    r.expect(Tok::Close, ")")?;
    r.end()?;
    Ok(DefItem { head, body })
}

/// The head of the definition item `item` lexed as `toks`, when it is one.
pub(crate) fn head_of(toks: &[Tok], item: &str) -> Option<Head> {
    Reader { toks, at: 0 }.head(item).ok()
}

fn starts_item(t: Option<&Tok>) -> bool {
    matches!(t, Some(Tok::Num(_) | Tok::Str(_) | Tok::Name(_) | Tok::Not | Tok::Open))
}

fn arith(c: char) -> &'static str {
    match c {
        '+' => "+",
        '-' => "-",
        '*' => "*",
        _ => "/",
    }
}

impl<'t> Reader<'t> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    fn found(&self) -> String {
        show_tok(self.peek())
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

    fn end(&self) -> Result<(), String> {
        match self.peek() {
            None => Ok(()),
            t => Err(format!("unexpected {} after the pipeline", show_tok(t))),
        }
    }

    fn pipeline(&mut self) -> Result<Pipeline<'t>, String> {
        let mut stages = vec![self.stage()?];
        while self.peek() == Some(&Tok::Bar) {
            self.at += 1;
            stages.push(self.stage()?);
        }
        Ok(Pipeline { stages })
    }

    fn stage(&mut self) -> Result<Stage<'t>, String> {
        if !starts_item(self.peek()) {
            return Err(format!("expected a pass or (, found {}", self.found()));
        }
        let mut items = Vec::new();
        while starts_item(self.peek()) {
            items.push(self.item()?);
        }
        Ok(Stage { items, end: self.at })
    }

    fn item(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let toks = self.toks;
        if let (Some(Tok::Name(n)), Some(Tok::Colon)) = (toks.get(self.at), toks.get(self.at + 1)) {
            self.at += 2;
            let t = self.type_text()?;
            self.expect(Tok::Assign, &format!("= after {n}:{t}"))?;
            let rhs = self.rhs()?;
            return Ok(Syn { node: Node::Assign(Lhs::Typed(n, t), Box::new(rhs)), at, end: self.at });
        }
        let e = self.or()?;
        if self.peek() != Some(&Tok::Assign) {
            return Ok(e);
        }
        let lhs = match &e.node {
            Node::Name(n) => Lhs::Name(n),
            Node::Tuple(ps) => Lhs::Names(self.names(ps)?),
            _ => return Err(NO_ASSIGN.into()),
        };
        self.at += 1;
        let rhs = self.rhs()?;
        Ok(Syn { node: Node::Assign(lhs, Box::new(rhs)), at, end: self.at })
    }

    /// The names of `(a, b, ...) = ...`.
    fn names(&self, ps: &[Pipeline<'t>]) -> Result<Vec<&'t str>, String> {
        let mut names = Vec::new();
        for p in ps {
            match p.single() {
                Some(Syn { node: Node::Name(n), .. }) => names.push(*n),
                _ => {
                    let at = p.stages[0].items[0].at;
                    return Err(format!("expected a name in (a, b, ...) = ..., found {}", show_tok(self.toks.get(at))));
                }
            }
        }
        Ok(names)
    }

    fn rhs(&mut self) -> Result<Syn<'t>, String> {
        if !starts_item(self.peek()) {
            return Err(format!("expected an expression, found {}", self.found()));
        }
        self.item()
    }

    fn or(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let first = self.and()?;
        if self.peek() != Some(&Tok::Or) {
            return Ok(first);
        }
        let mut es = vec![first];
        while self.peek() == Some(&Tok::Or) {
            self.at += 1;
            es.push(self.and()?);
        }
        Ok(Syn { node: Node::Or(es), at, end: self.at })
    }

    fn and(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let first = self.not()?;
        if self.peek() != Some(&Tok::And) {
            return Ok(first);
        }
        let mut es = vec![first];
        while self.peek() == Some(&Tok::And) {
            self.at += 1;
            es.push(self.not()?);
        }
        Ok(Syn { node: Node::And(es), at, end: self.at })
    }

    fn not(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        if self.peek() == Some(&Tok::Not) {
            self.at += 1;
            let e = self.not()?;
            return Ok(Syn { node: Node::Not(Box::new(e)), at, end: self.at });
        }
        let a = self.sum()?;
        let Some(&Tok::Cmp(cmp)) = self.peek() else { return Ok(a) };
        self.at += 1;
        let b = self.sum()?;
        Ok(Syn { node: Node::Op(cmp, Box::new(a), Box::new(b)), at, end: self.at })
    }

    fn sum(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let mut a = self.product()?;
        while let Some(&Tok::Arith(o @ ('+' | '-'))) = self.peek() {
            self.at += 1;
            let b = self.product()?;
            a = Syn { node: Node::Op(arith(o), Box::new(a), Box::new(b)), at, end: self.at };
        }
        Ok(a)
    }

    fn product(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let mut a = self.atom()?;
        while let Some(&Tok::Arith(o @ ('*' | '/'))) = self.peek() {
            self.at += 1;
            let b = self.atom()?;
            a = Syn { node: Node::Op(arith(o), Box::new(a), Box::new(b)), at, end: self.at };
        }
        Ok(a)
    }

    fn atom(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        let node = match self.toks.get(self.at) {
            Some(Tok::Num(n)) => Node::Num(*n),
            Some(Tok::Str(s)) => Node::Str(s),
            Some(Tok::Name(n)) => Node::Name(n),
            Some(Tok::Open) => return self.paren(),
            _ => return Err(format!("expected an expression, found {}", self.found())),
        };
        self.at += 1;
        Ok(Syn { node, at, end: self.at })
    }

    fn paren(&mut self) -> Result<Syn<'t>, String> {
        let at = self.at;
        self.at += 1;
        if matches!(self.peek(), Some(Tok::Name(n)) if n == "extern") {
            return Err(super::lexer::NO_EXTERN.into());
        }
        let first = self.pipeline()?;
        let node = match self.peek() {
            Some(Tok::Comma) => {
                let mut ps = vec![first];
                while self.peek() == Some(&Tok::Comma) {
                    self.at += 1;
                    ps.push(self.pipeline()?);
                }
                if self.peek() != Some(&Tok::Close) {
                    return Err(format!("expected , or ) in a tuple, found {}", self.found()));
                }
                Node::Tuple(ps)
            }
            Some(Tok::Close) => Node::Paren(first),
            t => return Err(format!("expected ), found {}", show_tok(t))),
        };
        self.at += 1;
        Ok(Syn { node, at, end: self.at })
    }

    /// A type written after `:`: a name, a tuple type `(A, B, ...)`, or `A->B`.
    fn type_text(&mut self) -> Result<String, String> {
        let mut t = self.type_atom("a type after :")?;
        while self.peek() == Some(&Tok::Arrow) {
            self.at += 1;
            t = format!("{t}->{}", self.type_atom("a type after ->")?);
        }
        Ok(t)
    }

    fn type_atom(&mut self, what: &str) -> Result<String, String> {
        if self.peek() != Some(&Tok::Open) {
            return self.name(what);
        }
        self.at += 1;
        let mut ts = vec![self.type_text()?];
        while self.peek() == Some(&Tok::Comma) {
            self.at += 1;
            ts.push(self.type_text()?);
        }
        self.expect(Tok::Close, ") after a tuple type")?;
        Ok(format!("({})", ts.join(", ")))
    }

    fn head(&mut self, s: &str) -> Result<Head, String> {
        self.expect(Tok::Open, "(let or (def")?;
        let head = self.name("let or def")?;
        let mut params: Vec<String> = Vec::new();
        let mut types: Vec<Option<Ty>> = Vec::new();
        let mut timed = false;
        let (kind, name) = match head.as_str() {
            "let" => (DefKind::Let, self.name("a name after let")?),
            "def" => {
                let mut kind = DefKind::Run;
                while self.peek() == Some(&Tok::At) {
                    self.at += 1;
                    match self.name("an attribute after @")?.as_str() {
                        "inline" => kind = DefKind::Inline,
                        "timed" => timed = true,
                        a => return Err(format!("unknown attribute @{a} of def; known: @inline @timed")),
                    }
                }
                self.expect(Tok::Open, "(NAME) after def")?;
                let name = self.name("a name after (def (")?;
                while self.peek() != Some(&Tok::Close) {
                    let n = self.name(&format!("a parameter name or ) in (def ({name} ...)"))?;
                    let ty = if self.peek() == Some(&Tok::Colon) {
                        self.at += 1;
                        let t = self.type_text()?;
                        match Ty::parse(&t) {
                            Ok(ty) if matches!(ty, Ty::Fn(..)) && !ty.is_function() => return Err(format!("type {t} of parameter {n}: a function takes one input, term or group, and gives num, term, term? or group")),
                            Ok(ty) if !matches!(ty, Ty::MaybeTerm | Ty::Text | Ty::Any) => Some(ty),
                            Err(e) if t.contains('(') => return Err(format!("type {t} of parameter {n}: {e}")),
                            _ => return Err(format!("unknown type {t} of parameter {n}; known: pipe group term num name, and A->B as in term->num")),
                        }
                    } else {
                        None
                    };
                    params.push(n);
                    types.push(ty);
                }
                self.at += 1;
                (kind, name)
            }
            _ => return Err(format!("expected (let NAME pipeline) or (def (NAME) pipeline): {s}")),
        };
        Ok(Head { kind, name, params, types, timed })
    }
}
