//! The pipeline language (`docs/pipe-language.md`): its tree, types, parser, definitions,
//! macros, checks, warnings, global variables and evaluator, and the built-in functions that
//! do not depend on the simplification. `host` is all it reads of the rest of the crate.

pub mod ast;
pub mod builtins;
pub mod check;
pub mod defs;
pub mod eval;
pub(crate) mod host;
pub mod lexer;
pub mod macros;
pub mod parser;
pub mod source;
pub mod types;
pub mod vars;
pub mod warn;
