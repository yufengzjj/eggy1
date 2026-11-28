//! The pipeline language (`docs/pipe-language.md`): its tree, types, parser, definitions,
//! macros, checks, warnings, global variables and evaluator, and the built-in functions that
//! do not depend on the simplification. `host` is all it reads of the rest of the crate.

pub mod ast;
pub mod builtins;
pub mod check;
pub mod defs;
pub mod eval;
pub(crate) mod flow;
pub(crate) mod host;
pub(crate) mod infer;
pub mod lexer;
pub mod macros;
pub mod parser;
pub mod run;
pub mod source;
pub mod types;
pub mod vars;
pub mod warn;

pub use eval::Value;
pub use run::{Outcome, execute, run};
pub use source::Program;
