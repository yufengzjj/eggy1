//! What the command line turns into language code: the `--passes` items, `-m` and `-i`, and
//! the listings of `--show-passes` and `--show-builtins`.

use crate::lang::builtins::all;
use crate::lang::types::Kind;

pub mod passes;

/// Every declaration with its description, grouped by calling kind (`--show-builtins`).
pub fn listing() -> String {
    let mut out = String::from("# The built-in functions (src/builtins.pipe), by how they are called.\n");
    for (kind, title) in Kind::ALL {
        out += &format!("\n# --- {title}\n");
        for s in all().iter().filter(|s| s.kind() == kind) {
            out += &format!("# {}\n{}\n", s.doc, s.decl());
        }
    }
    out
}
