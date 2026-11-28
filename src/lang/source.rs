//! Reading programs: the caller's source text and the files it imports, their top-level items
//! `(let ...)`, `(def ...)`, `(import "PATH")`, `NAME = VALUE` and statements, in order.

use super::ast::{Holds, Pipe, Slot};
use super::defs::{Call, Def, DefKind, Defs, Named, has_steps, parse_definition};
use super::host::{self, DEFAULT, FLAG0, INNER, Passes, RUST_VARS, defined_builtin, is_extern_switch};
use super::lexer::{NO_EXTERN, Tok, code_part, depth_of, lex, slash_name};
use super::parser::{TopNames, free_name, parse_assign, parse_statement};
use super::run::{Gives, Top};
use super::vars::{PARSED, global_slot, parsed_defines, parsing, var_index};

/// A program being read: the passes and steps its items define, the names `let` and `def`
/// define, and what the parse keeps between items.
pub struct Program {
    pub passes: Passes,
    defs: Defs,
    state: Lets,
}

impl Default for Program {
    fn default() -> Program {
        Program::new()
    }
}

impl Program {
    /// A program with no items yet.
    pub fn new() -> Program {
        Program { passes: Passes::base(), defs: Defs::new(), state: Lets::default() }
    }

    /// The top-level items of `text` added in order; it imports files relative to the current
    /// directory.
    pub fn read(&mut self, text: &str) -> Result<(), String> {
        self.parsing(|p, defs, state| p.apply_source(text, defs, state, false))
    }

    /// `(import "name")` of a source the host registers, read whole even where a copy of it
    /// read before could stand for it.
    pub(crate) fn read_registered(&mut self, name: &str) -> Result<(), String> {
        self.parsing(|p, defs, state| p.import(name, defs, state, false))
    }

    fn parsing(&mut self, f: impl FnOnce(&mut Passes, &mut Defs, &mut Lets) -> Result<(), String>) -> Result<(), String> {
        let Program { passes, defs, state } = self;
        let mut globals = std::mem::take(&mut passes.globals);
        let r = parsing(&mut globals, || f(passes, defs, state));
        passes.globals = globals;
        r
    }

    /// The names `let` and `def` defined so far.
    pub(crate) fn defs(&self) -> &Defs {
        &self.defs
    }

    /// The program checked (`Passes::check`), and warnings about parts of it that do
    /// nothing: a `let` or `def` defined after the import of `default` and never used, and
    /// what `Passes::warnings` finds.
    pub fn finish(self) -> Result<(Passes, Vec<String>), String> {
        let Program { passes, state: lets, .. } = self;
        passes.check()?;
        let unused = lets.defined.iter().filter(|(head, _)| !lets.used.iter().any(|n| head.split(' ').next() == Some(n)));
        let mut notes: Vec<String> = unused
            .map(|(n, k)| match k {
                DefKind::Let => format!("(let {n} ...) is never used: a name is expanded only where a later item writes it"),
                DefKind::Inline => format!("(def @inline ({n}) ...) is never used: it is expanded only where a later item calls it"),
                DefKind::Run => format!("(def ({n}) ...) is never used: it runs only where a later item calls it"),
            })
            .collect();
        notes.extend(lets.notes);
        notes.extend(passes.warnings());
        notes.dedup();
        Ok((passes, notes))
    }
}

impl Passes {
    /// A form of a program: `(let ...)` or `(def ...)`.
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
        let inline = d.kind == DefKind::Inline && (numeric || d.input.is_some() || d.timed);
        let (pipe, def) = if d.kind == DefKind::Run || inline {
            let body = std::sync::Arc::new(d.value.clone().map_or(d.pipe, |v| Pipe::app("filter", vec![v])));
            let def = std::sync::Arc::new(Def { name: d.name.clone(), params: d.params.clone(), body, inline, flat: inline && d.flat, input: d.input.clone(), step: d.step, steps: d.value.as_ref().is_some_and(has_steps), value: d.value.clone(), implicit: d.implicit.clone(), timed: d.timed });
            self.defs.push(def.clone());
            (Call::bare(&def), Some(def))
        } else {
            (d.pipe, None)
        };
        defs.insert(d.name.clone(), Named { pipe, flat: d.flat, run: d.kind == DefKind::Run, params: d.params, def });
        if !lets.in_default() {
            lets.defined.push((head, d.kind));
        }
        Ok(())
    }

    /// The items of a program's text applied in turn: forms `(let ...)`, `(def ...)` and
    /// `(import "PATH")`, `NAME = VALUE` items (`assign_top`) and statements, each ending at the
    /// end of a line outside parentheses that does not end in `|`; `#` starts a comment to
    /// the end of the line. `lines` puts the line number before an error.
    pub(crate) fn apply_source(&mut self, text: &str, defs: &mut Defs, lets: &mut Lets, lines: bool) -> Result<(), String> {
        let (mut form, mut depth, mut start) = (String::new(), 0i32, 0);
        for (n, line) in text.lines().enumerate() {
            let code = code_part(line).trim_end();
            if depth == 0 && code.trim().is_empty() && form.is_empty() {
                continue;
            }
            if depth == 0 && form.is_empty() {
                start = n + 1;
            }
            let at = |e: String| if lines { format!("line {start}: {e}") } else { e };
            depth += depth_of(code);
            if form.is_empty() {
                form.push_str(code.trim());
            } else {
                form.push('\n');
                form.push_str(code);
            }
            if depth > 0 || form.ends_with('|') {
                continue;
            }
            let item = std::mem::take(&mut form);
            depth = 0;
            self.item(&item, defs, lets).map_err(at)?;
        }
        if !form.is_empty() {
            lex(&form)?;
            return Err(format!("line {start}: unclosed form: {form}"));
        }
        Ok(())
    }

    /// One top-level item.
    fn item(&mut self, item: &str, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        let head = item.strip_prefix('(').map(|r| r.split(|c: char| c.is_whitespace() || c == '(' || c == ')').next().unwrap_or(""));
        match head {
            Some("import") => return self.import_item(item, defs, lets),
            Some("let" | "def" | "extern") => return self.form(item, defs, lets),
            _ => {}
        }
        let default = lets.in_default();
        let Some((name, val)) = top_assignment(item) else { return self.statement(item, defs, lets) };
        if var_index(name).is_some() || slash_name(name).is_some() {
            return self.assign_top(name, val, default, defs).map_err(|e| format!("{item}: {e}"));
        }
        let mut top = lets.top.clone();
        let mut used = Vec::new();
        match parse_statement(item, defs, &mut top, &mut used) {
            Ok(tops) if !matches!(tops.as_slice(), [Top { pipe: Pipe::Bind(Slot::Local(_, Holds::Num), _), .. }]) => {
                lets.top = top;
                lets.used.extend(used);
                self.program.extend(tops);
                Ok(())
            }
            _ => self.assign_top(name, val, default, defs).map_err(|e| format!("{item}: {e}")),
        }
    }

    /// A statement: its steps join the program's.
    fn statement(&mut self, item: &str, defs: &Defs, lets: &mut Lets) -> Result<(), String> {
        let tops = parse_statement(item, defs, &mut lets.top, &mut lets.used)?;
        self.program.extend(tops);
        Ok(())
    }

    /// `(import "PATH")`.
    fn import_item(&mut self, item: &str, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        let toks = lex(item)?;
        let [Tok::Open, Tok::Name(_), Tok::Str(path), Tok::Close] = toks.as_slice() else {
            return Err(format!("expected (import \"PATH\"): {item}"));
        };
        self.import(path, defs, lets, true)
    }

    /// The items of the file `path` (relative to the directory of the file importing it, or
    /// of the current one), else of the source the host registers by that name, in place;
    /// nothing when this program imported it before. `copy` lets a copy of `default` read
    /// once per process stand for it at the start of a program.
    pub(crate) fn import(&mut self, path: &str, defs: &mut Defs, lets: &mut Lets, copy: bool) -> Result<(), String> {
        let dir = lets.importing.last().and_then(|(_, d)| d.clone());
        let file = dir.map_or_else(|| std::path::PathBuf::from(path), |d| d.join(path));
        let (key, text, dir) = if file.is_file() {
            let text = std::fs::read_to_string(&file).map_err(|e| format!("import \"{path}\": {e}"))?;
            let key = std::fs::canonicalize(&file).map_or_else(|_| file.display().to_string(), |f| f.display().to_string());
            (key, std::borrow::Cow::Owned(text), file.parent().map(std::path::Path::to_path_buf))
        } else if let Some(text) = host::source(path) {
            (path.to_string(), std::borrow::Cow::Borrowed(text), None)
        } else {
            return Err(format!("import \"{path}\": no file {} and no source named {path}", file.display()));
        };
        if let Some(i) = lets.importing.iter().position(|(k, _)| *k == key) {
            let cycle: Vec<&str> = lets.importing[i..].iter().map(|(k, _)| k.as_str()).chain([key.as_str()]).collect();
            return Err(format!("import cycle: {}", cycle.join(" -> ")));
        }
        if lets.imported.contains(&key) {
            return Ok(());
        }
        lets.imported.push(key.clone());
        let fresh = self.program.is_empty() && self.defs.is_empty() && defs.is_empty() && self.globals.is_empty();
        if copy && key == "default" && fresh {
            let (p, d) = &*DEFAULT;
            *self = p.clone();
            *defs = d.clone();
            PARSED.with(|g| *g.borrow_mut() = Some(p.globals.clone()));
            return Ok(());
        }
        lets.importing.push((key.clone(), dir));
        let r = self.apply_source(&text, defs, lets, true).map_err(|e| format!("{path}: {e}"));
        lets.importing.pop();
        r?;
        if key == "default" {
            self.defaults = self.program.len();
            self.shown_from = self.program.len();
            self.default_defs = self.defs.len();
            self.default_globals = PARSED.with(|g| g.borrow().as_ref().map_or(0, Vec::len));
        }
        Ok(())
    }

    /// `name = val` as a top-level item: the definition of the variable `name` when it is
    /// none yet, else an assignment to it. Every variable is `none` until assigned, so a
    /// definition of `default` as `none` adds no step.
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
            self.defines.push(self.program.len());
        }
        self.program.push(Top { pipe: parse_assign(name, val)?, gives: Gives::Nothing });
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

/// What the parse of a program keeps between its items: the `let` and `def` names defined
/// after the import of `default` and the names used, for the warnings; the local variables
/// the statements bound; the files being imported and those imported.
#[derive(Default)]
pub(crate) struct Lets {
    pub(crate) defined: Vec<(String, DefKind)>,
    pub(crate) used: Vec<String>,
    /// The warnings of reading the definitions.
    pub(crate) notes: Vec<String>,
    pub(crate) top: TopNames,
    /// The files being imported, innermost last, by key (a path, or the name of a source the
    /// host registers), with the directory their imports are relative to.
    pub(crate) importing: Vec<(String, Option<std::path::PathBuf>)>,
    pub(crate) imported: Vec<String>,
}

impl Lets {
    /// Whether the item read is in `default`.
    pub(crate) fn in_default(&self) -> bool {
        self.importing.iter().any(|(k, _)| k == "default")
    }
}
