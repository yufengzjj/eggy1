//! What the language reads of the simplification, which embeds it: the candidate terms, the
//! passes and their variables, the built-in functions it implements. Every use of it in
//! `lang` goes through here.

pub(crate) use crate::{Cli, Error, stats, width_of};
pub(crate) use crate::builtin_passes::{FEATURES, Won, count_won, implementation, skipped, step_name, term_pass};
pub(crate) use crate::cand::Cand;
pub(crate) use crate::eval::Term;
pub(crate) use crate::linear_mba::Ctx;
pub(crate) use crate::passes::{DEFAULT, Passes, SUBS, defined_builtin, set_current};
pub(crate) use crate::rust_vars::{DEADLINE, FLAG0, FLAGS, INNER, KEEP, LIMIT0, RUST_VARS, SETTING0, is_extern_switch, is_unread, rust_var, switch, switch_index};
