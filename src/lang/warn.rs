//! Warnings about parts of the pipelines that do nothing.

use super::ast::{Pipe, Slot, show};
use super::defs::show_def;
use super::host::{Passes, RUST_VARS};
use super::vars::{var, var_names};

impl Passes {
    /// Parts of the pipelines that do nothing: a `(save R)` never read in its pipeline or
    /// saved over before any read on every path, an assignment (also `(on NAME)`, `(off
    /// NAME)`) that ends its sequence, and one assigned again in its sequence before any
    /// read of it or any other step.
    pub fn warnings(&self) -> Vec<String> {
        let mut out = Vec::new();
        let globals = var_names();
        for (name, uses) in self.uses() {
            let mut unread: Vec<&String> = uses.saved.iter().filter(|r| !uses.reads.contains(r)).collect();
            unread.dedup();
            out.extend(unread.into_iter().map(|r| format!("{name}: {} {r} is bound and never read", uses.kind(r))));
            let mut dead = uses.dead.clone();
            dead.dedup();
            out.extend(dead.iter().map(|r| format!("{name}: {} {r} is bound again before its value is read", uses.kind(r))));
            out.extend(uses.idle_assign.iter().map(|t| format!("{name}: {t} ends its sequence and changes nothing")));
            out.extend(uses.reassigned.iter().map(|v| format!("{name}: {v} is assigned again before anything reads it")));
            out.extend(uses.dropping.iter().map(|v| format!("{name}: {v} does not take the input; its value is dropped — write ({v} | ...) to start from it")));
            let params = self.defs.iter().find(|d| d.name == name).map_or_else(Vec::new, |d| d.bound());
            let mut locals: Vec<&String> = uses.saved.iter().filter(|r| !params.contains(r)).collect();
            locals.sort();
            locals.dedup();
            for r in locals {
                if let Some(g) = globals.iter().find(|g| near(r, g)) {
                    out.push(format!("{name}: {} {r} is a new local variable; did you mean {g}?", uses.kind(r)));
                }
            }
        }
        out.extend(self.unread_globals().into_iter().map(|n| format!("{n} is defined and never read")));
        out
    }

    /// The variables the program defines past `default` that neither the Rust code nor any
    /// pipeline or top-level step reads.
    pub(crate) fn unread_globals(&self) -> Vec<&'static str> {
        let defined: Vec<usize> = self.globals[self.default_globals..].iter().copied().filter(|i| *i >= RUST_VARS).collect();
        if defined.is_empty() {
            return Vec::new();
        }
        let mut text: Vec<String> = self.program.iter().map(|t| if let Pipe::Bind(Slot::Global(_), v) = &t.pipe { show(v) } else { show(&t.pipe) }).collect();
        text.extend(self.defs.iter().map(|d| show_def(d)));
        let words: std::collections::HashSet<&str> = text.iter().flat_map(|t| t.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))).collect();
        defined.into_iter().map(|i| var(i).name).filter(|n| !words.contains(n)).collect()
    }
}

/// Whether the new local variable `r` is close enough to the variable `g` to be a typo of it:
/// an edit distance of 1 for names of 3 or 4 characters, 1 or 2 for longer ones.
fn near(r: &str, g: &str) -> bool {
    let most = match r.len() {
        0..=2 => return false,
        3 | 4 => 1,
        _ => 2,
    };
    if r.contains('#') || r.len().abs_diff(g.len()) > most {
        return false;
    }
    let (a, b): (Vec<char>, Vec<char>) = (r.chars().collect(), g.chars().collect());
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.iter().enumerate() {
        let mut prev = row[0];
        row[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cur = row[j + 1];
            row[j + 1] = (prev + usize::from(ca != cb)).min(row[j] + 1).min(cur + 1);
            prev = cur;
        }
    }
    (1..=most).contains(&row[b.len()])
}
