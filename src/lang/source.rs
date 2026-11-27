//! Reading source files (`default.pipe`, `file=PATH`): their top-level forms `(let ...)`,
//! `(def ...)` and `NAME = VALUE` lines.

use super::ast::Pipe;
use super::defs::{Call, Def, DefKind, Defs, Named, has_steps, parse_definition};
use super::host::{FLAG0, INNER, Passes, RUST_VARS, defined_builtin, is_extern_switch};
use super::lexer::{NO_EXTERN, code_part, depth_of, slash_name};
use super::parser::{free_name, parse_assign};
use super::vars::{PARSED, global_slot, parsed_defines, var_index};

impl Passes {
    /// A form of `--passes` or a source file: `(let ...)` or `(def ...)`.
    pub(crate) fn form(&mut self, item: &str, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        if item.starts_with("(extern") {
            return Err(NO_EXTERN.into());
        }
        if !(item.starts_with("(let") || item.starts_with("(def")) {
            return Err(format!("expected (let ...), (def ...) or NAME = VALUE: {item}"));
        }
        let d = parse_definition(item, defs, &mut lets.used)?;
        lets.notes.extend(d.notes.iter().cloned());
        if d.kind == DefKind::Run && defined_builtin(&d.name) {
            self.define(&d.name, d.pipe)?;
            return Ok(());
        }
        let numeric = d.params.iter().any(|p| p.ty.is_expr());
        let head = std::iter::once(d.name.as_str()).chain(d.params.iter().map(|p| p.name.as_str())).collect::<Vec<_>>().join(" ");
        let inline = d.kind == DefKind::Inline && (numeric || d.input.is_some());
        let (pipe, def) = if d.kind == DefKind::Run || inline {
            let body = std::sync::Arc::new(d.value.clone().map_or(d.pipe, |v| Pipe::app("filter", vec![v])));
            let def = std::sync::Arc::new(Def { name: d.name.clone(), params: d.params.clone(), body, inline, flat: inline && d.flat, input: d.input.clone(), step: d.step, steps: d.value.as_ref().is_some_and(has_steps), value: d.value.clone(), implicit: d.implicit.clone() });
            self.defs.push(def.clone());
            (Call::bare(&def), Some(def))
        } else {
            (d.pipe, None)
        };
        defs.insert(d.name.clone(), Named { pipe, flat: d.flat, run: d.kind == DefKind::Run, params: d.params, def });
        lets.defined.push((head, d.kind));
        Ok(())
    }

    /// The items of a source file (`default.pipe`, `file=PATH`) applied in turn: forms
    /// `(let ...)` and `(def ...)`, which may span lines, and `NAME = VALUE` lines
    /// (`assign_top`); `#` starts a comment to the end of the line.
    pub(crate) fn apply_source(&mut self, text: &str, defs: &mut Defs, lets: &mut Lets, default: bool) -> Result<(), String> {
        let (mut form, mut depth, mut start) = (String::new(), 0i32, 0);
        for (n, line) in text.lines().enumerate() {
            let code = code_part(line).trim_end();
            if depth == 0 && code.trim().is_empty() {
                continue;
            }
            if depth == 0 {
                start = n + 1;
            }
            let at = |e: String| format!("line {start}: {e}");
            depth += depth_of(code);
            if form.is_empty() {
                form.push_str(code.trim());
            } else {
                form.push('\n');
                form.push_str(code);
            }
            if depth > 0 && form.starts_with('(') {
                continue;
            }
            let item = std::mem::take(&mut form);
            depth = 0;
            if item.starts_with('(') {
                self.form(&item, defs, lets).map_err(at)?;
            } else {
                let (name, val) = top_assignment(&item).ok_or_else(|| at(format!("expected (let ...), (def ...) or NAME = VALUE: {item}")))?;
                self.assign_top(name, val, default, defs).map_err(|e| at(format!("{item}: {e}")))?;
            }
        }
        if !form.is_empty() {
            return Err(format!("line {start}: unclosed form: {form}"));
        }
        Ok(())
    }

    /// `name = val` as an item of a source file, or of `--passes` with spaces around `=`: the
    /// definition of the variable `name` when it is none yet, else an entry assignment to it.
    /// Every variable is `none` until assigned, so a definition of `default.pipe` as `none`
    /// adds no entry assignment.
    pub(crate) fn assign_top(&mut self, name: &str, val: &str, default: bool, defs: &Defs) -> Result<(), String> {
        if let Some(e) = slash_name(name) {
            return Err(e);
        }
        let defined = parsed_defines(name);
        let new = match var_index(name) {
            _ if defined => false,
            Some(i) if i < FLAG0 && is_extern_switch(INNER[i]) => false,
            Some(i) if i < RUST_VARS => {
                PARSED.with(|p| p.borrow_mut().get_or_insert_with(Vec::new).push(i));
                true
            }
            Some(_) => false,
            None => {
                if defined_builtin(name) || name.starts_with("sub_") {
                    return Err(format!("{name} is a function: a source file defines it as (def ({name}) ...)"));
                }
                if !free_name(name) || defs.contains_key(name) {
                    return Err(format!("{name} names a function or a definition, not a variable"));
                }
                global_slot(name);
                true
            }
        };
        if new && default && val.trim() == "none" {
            return Ok(());
        }
        if new && !default {
            self.defines.push(self.entry.len());
        }
        self.entry.push(parse_assign(name, val)?);
        Ok(())
    }
}

/// `NAME = VALUE` split into its name and value.
pub(crate) fn top_assignment(item: &str) -> Option<(&str, &str)> {
    let (name, val) = item.split_once('=')?;
    let name = name.trim_end();
    (is_name(name) && !val.starts_with('=')).then_some((name, val.trim()))
}

/// Whether `s` is a name a variable can have.
pub(crate) fn is_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '/')
}

/// The `let` and `def` names a spec defines and those its items use, for
/// `Passes::parse_noting`.
#[derive(Default)]
pub(crate) struct Lets {
    pub(crate) defined: Vec<(String, DefKind)>,
    pub(crate) used: Vec<String>,
    /// The warnings of reading the definitions.
    pub(crate) notes: Vec<String>,
}
