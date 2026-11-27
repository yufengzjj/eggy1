//! The candidate terms the pipelines run on.

use crate::eval::{Term, parse, show, size};
use std::cell::OnceCell;
use std::rc::Rc;

/// A candidate term and the pass it came from, for `stats` (`final/ORIGIN`). The egglog
/// text, the tree and the size are each made once, when first needed: large inputs spend
/// more time printing and parsing than in the passes.
#[derive(Clone, Debug)]
pub struct Cand {
    pub(crate) forms: Rc<Forms>,
    pub origin: String,
    /// Which of `clustered` and `wide_blocks` gave a kept form in the passes that made it.
    pub(crate) used: u8,
    /// The uncached `rewrite` calls of the passes that made it.
    pub(crate) rewrites: usize,
}

#[derive(Debug, Default)]
pub(crate) struct Forms {
    text: OnceCell<String>,
    tree: OnceCell<Term>,
    size: OnceCell<usize>,
}

impl Cand {
    pub fn new(text: &str, origin: &str) -> Cand {
        Cand { forms: Rc::new(Forms { text: OnceCell::from(text.to_string()), ..Default::default() }), origin: origin.to_string(), used: 0, rewrites: 0 }
    }

    /// `tree` made from `from` by a pass with these `used` bits and `rewrites` calls.
    pub(crate) fn of(tree: Term, from: &Cand, used: u8, rewrites: usize) -> Cand {
        let forms = Rc::new(Forms { tree: OnceCell::from(tree), ..Default::default() });
        Cand { forms, origin: from.origin.clone(), used: from.used | used, rewrites: from.rewrites + rewrites }
    }

    /// The egglog text.
    pub fn term(&self) -> &str {
        self.forms.text.get_or_init(|| show(self.tree()))
    }

    pub(crate) fn tree(&self) -> &Term {
        self.forms.tree.get_or_init(|| parse(self.forms.text.get().unwrap()))
    }

    pub(crate) fn size(&self) -> usize {
        *self.forms.size.get_or_init(|| size(self.tree()))
    }

    pub(crate) fn into_tree(self) -> Term {
        match Rc::try_unwrap(self.forms) {
            Ok(f) => f.tree.into_inner().unwrap_or_else(|| parse(f.text.get().unwrap())),
            Err(f) => f.tree.get_or_init(|| parse(f.text.get().unwrap())).clone(),
        }
    }

    pub(crate) fn same(&self, o: &Cand) -> bool {
        if Rc::ptr_eq(&self.forms, &o.forms) {
            return true;
        }
        if let (Some(a), Some(b)) = (self.forms.text.get(), o.forms.text.get())
            && a == b
        {
            return true;
        }
        self.size() == o.size() && self.tree() == o.tree()
    }
}

impl PartialEq for Cand {
    fn eq(&self, o: &Cand) -> bool {
        self.origin == o.origin && self.same(o)
    }
}
