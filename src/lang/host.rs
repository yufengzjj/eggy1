//! What the language reads of the simplification, which embeds it: the candidate terms, the
//! passes and their variables, the built-in functions it implements, the sources it
//! registers. Every use of it in `lang` goes through here.

pub(crate) use crate::{Error, stats, width_of};
pub(crate) use crate::builtin_passes::{FEATURES, Won, count_won, implementation, skipped, start, step_name, term_pass};
pub(crate) use crate::cand::Cand;
pub(crate) use crate::eval::{NumType, Term};
pub(crate) use crate::linear_mba::Ctx;
pub(crate) use crate::passes::{DEFAULT, Passes, SUBS, defined_builtin, set_current};
pub(crate) use crate::rust_vars::{DEADLINE, FLAG0, FLAGS, INNER, KEEP, LIMIT0, NUM_TYPE, NUM_TYPES, RUST_VARS, SETTING0, TRACE, is_extern_switch, is_unread, num_type, rust_var, switch, switch_index};

/// The text of the source the host registers as `name` for `(import "name")`.
pub(crate) fn source(name: &str) -> Option<&'static str> {
    (name == "default").then_some(include_str!("../default.pipe"))
}
