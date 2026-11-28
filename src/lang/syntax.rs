//! The syntax tree of the pipeline language, as `reader` reads it from the tokens: calls,
//! pipelines, tuples, literals, names, operators and assignments, each with the tokens it
//! spans. What a node means (a number, a group, a tuple, a function value) is decided by
//! `elab` from the names it holds.

use super::defs::DefKind;
use super::types::Ty;

/// A node and the tokens `at..end` it is read from.
#[derive(Clone, Debug)]
pub(crate) struct Syn<'t> {
    pub(crate) node: Node<'t>,
    pub(crate) at: usize,
    pub(crate) end: usize,
}

#[derive(Clone, Debug)]
pub(crate) enum Node<'t> {
    Num(u64),
    Str(&'t str),
    Name(&'t str),
    Not(Box<Syn<'t>>),
    /// `a op b` for `+ - * /` and the comparisons.
    Op(&'static str, Box<Syn<'t>>, Box<Syn<'t>>),
    And(Vec<Syn<'t>>),
    Or(Vec<Syn<'t>>),
    /// `( ... )` holding a pipeline.
    Paren(Pipeline<'t>),
    /// `(a, b, ...)`: the positions of a tuple.
    Tuple(Vec<Pipeline<'t>>),
    Assign(Lhs<'t>, Box<Syn<'t>>),
}

/// The left side of an assignment.
#[derive(Clone, Debug)]
pub(crate) enum Lhs<'t> {
    Name(&'t str),
    /// `NAME:TYPE`, the type as written.
    Typed(&'t str, String),
    /// `(a, b, ...)`.
    Names(Vec<&'t str>),
}

/// The items of a step written side by side (`fix 3 p` in `(fix 3 p)`), and the token that
/// ends them: a `|`, `)`, `,` or the end.
#[derive(Clone, Debug)]
pub(crate) struct Stage<'t> {
    pub(crate) items: Vec<Syn<'t>>,
    pub(crate) end: usize,
}

/// The steps of `a | b | ...`.
#[derive(Clone, Debug)]
pub(crate) struct Pipeline<'t> {
    pub(crate) stages: Vec<Stage<'t>>,
}

/// The head of a definition item: how it defines its name, the name, the parameters and the
/// types written for them, `@timed`.
#[derive(Clone, Debug)]
pub(crate) struct Head {
    pub(crate) kind: DefKind,
    pub(crate) name: String,
    pub(crate) params: Vec<String>,
    pub(crate) types: Vec<Option<Ty>>,
    pub(crate) timed: bool,
}

/// A definition item `(let NAME p)` or `(def ... (NAME ...) body)`.
#[derive(Clone, Debug)]
pub(crate) struct DefItem<'t> {
    pub(crate) head: Head,
    pub(crate) body: Pipeline<'t>,
}

impl<'t> Syn<'t> {
    pub(crate) fn name(&self) -> Option<&'t str> {
        match self.node {
            Node::Name(n) => Some(n),
            _ => None,
        }
    }

    /// The pipeline inside parentheses that hold no tuple.
    pub(crate) fn paren(&self) -> Option<&Pipeline<'t>> {
        match &self.node {
            Node::Paren(p) => Some(p),
            _ => None,
        }
    }

    /// The positions of a tuple written out.
    pub(crate) fn tuple(&self) -> Option<&[Pipeline<'t>]> {
        match &self.node {
            Node::Tuple(ps) => Some(ps),
            _ => None,
        }
    }

    /// The first stage of the pipeline inside parentheses, and the stages after it.
    pub(crate) fn head_stage(&self) -> Option<(&Stage<'t>, &[Stage<'t>])> {
        self.paren().map(|p| (&p.stages[0], &p.stages[1..]))
    }

    /// The name the parentheses start with, `(NAME ...)`.
    pub(crate) fn head_name(&self) -> Option<&'t str> {
        self.head_stage().and_then(|(s, _)| s.items[0].name())
    }

    /// The node itself where it is no parentheses; inside parentheses that hold one item, that
    /// item.
    pub(crate) fn single(&self) -> Option<&Syn<'t>> {
        match self.head_stage() {
            Some((s, [])) if s.items.len() == 1 => Some(&s.items[0]),
            _ => None,
        }
    }
}

impl<'t> Pipeline<'t> {
    /// The one item of a pipeline of one step.
    pub(crate) fn single(&self) -> Option<&Syn<'t>> {
        match &self.stages[..] {
            [s] if s.items.len() == 1 => Some(&s.items[0]),
            _ => None,
        }
    }
}
