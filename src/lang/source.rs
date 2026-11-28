//! Reading programs: the caller's source text and the files it imports, their top-level items
//! `(let ...)`, `(def ...)`, `(import "PATH")`, `NAME = VALUE` and statements, in order.

use super::ast::{Holds, Pipe, Slot};
use super::defs::{Call, Def, DefKind, Defs, Head, Named, declared, has_steps, head_of, parse_definition_lexed, sig_of};
use super::host::{self, DEFAULT, FLAG0, INNER, Passes, RUST_VARS, is_extern_switch};
use super::lexer::{NO_EXTERN, Tok, code_part, depth_of, lex, may_join_names, slash_name};
use super::parser::{TopNames, free_name, parse_assign_on, parse_statement};
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
    /// A program with no items yet but those of the prelude.
    pub fn new() -> Program {
        Program { passes: Passes::base(), defs: prelude(), state: Lets::default() }
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
    pub(crate) fn form(&mut self, item: &str, toks: Option<Vec<Tok>>, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        if item.starts_with("(extern") {
            return Err(NO_EXTERN.into());
        }
        if !(item.starts_with("(let") || item.starts_with("(def")) {
            return Err(format!("expected (let ...), (def ...) or NAME = VALUE: {item}"));
        }
        let d = parse_definition_lexed(item, toks, defs, &mut lets.used)?;
        lets.notes.extend(d.notes.iter().cloned());
        let numeric = d.params.iter().any(|p| p.ty.is_expr());
        let head = std::iter::once(d.name.as_str()).chain(d.params.iter().map(|p| p.name.as_str())).collect::<Vec<_>>().join(" ");
        // An `@inline` function whose body starts from its input and reads it nowhere else is put
        // in place where it is called, as one without an input is.
        let placed = match (&d.input, &d.pipe) {
            (Some(g), Pipe::Seq(ps)) if d.kind == DefKind::Inline && !numeric && !d.timed && d.implicit.is_none() && matches!(&ps[0], Pipe::Var(Slot::Local(r, Holds::Group)) if r == g) => {
                let (mut names, mut params) = (Vec::new(), Vec::new());
                ps[1..].iter().for_each(|q| super::eval::reads(q, &mut names, &mut params));
                !names.contains(g)
            }
            _ => false,
        };
        let inline = d.kind == DefKind::Inline && !placed && (numeric || d.input.is_some() || d.timed);
        let earlier = defs.get(&d.name).filter(|n| n.run).and_then(|n| n.def.clone());
        let ahead = lets.ahead.declared.iter().position(|n| *n == d.name).map(|i| lets.ahead.declared.remove(i)).is_some();
        let (pipe, def) = if d.kind == DefKind::Run || inline {
            let body = std::sync::Arc::new(d.value.clone().map_or(d.pipe, |v| Pipe::app("filter", vec![v])));
            let slot = earlier.as_ref().and_then(|e| e.slot);
            let def = std::sync::Arc::new(Def { name: d.name.clone(), params: d.params.clone(), body, inline, flat: inline && d.flat, input: d.input.clone(), step: d.step, steps: d.value.as_ref().is_some_and(has_steps), value: d.value.clone(), implicit: d.implicit.clone(), timed: d.timed, slot: Some(slot.unwrap_or(self.defs.len())) });
            if let Some(e) = &earlier {
                let (was, now) = (sig_of(e), sig_of(&def));
                if !was.same_shape(&now) {
                    match ahead && !lets.ahead.second {
                        true => lets.ahead.retry = true,
                        false if ahead => return Err(format!("{} is called before its definition as {was}, but defined as {now}", d.name)),
                        false => return Err(format!("{} is defined before as {was}; a later definition replaces it only with the same signature, not {now}", d.name)),
                    }
                }
            }
            match slot {
                Some(i) => self.defs[i] = def.clone(),
                None => self.defs.push(def.clone()),
            }
            lets.ahead.found.push(def.clone());
            (Call::bare(&def), Some(def))
        } else {
            (d.pipe, None)
        };
        let input = if placed { d.input.clone() } else { None };
        defs.insert(d.name.clone(), Named { pipe, flat: d.flat && !placed, run: d.kind == DefKind::Run, params: d.params, def, input });
        if !lets.in_default() && (ahead || earlier.is_none()) {
            lets.defined.push((head, d.kind));
        }
        Ok(())
    }

    /// The `def` items of `items` that an earlier item or their own body calls, with names
    /// nothing else defines, each with the item before which it is declared. The items it
    /// lexes are kept in `lexed`.
    fn called_ahead(items: &[(usize, String)], lexed: &mut [Option<Lexed>], defs: &Defs) -> Vec<(usize, Head)> {
        // Only an item starting with `(` lexes to one starting with `Tok::Open`.
        let mut heads: Vec<Option<Head>> = (0..items.len()).map(|k| if items[k].1.starts_with('(') { head_of(tokens(items, lexed, k), &items[k].1) } else { None }).collect();
        let mut out = Vec::new();
        for k in 0..heads.len() {
            let Some(n) = heads[k].as_ref().filter(|h| h.kind == DefKind::Run).map(|h| h.name.clone()) else { continue };
            let free = !defs.contains_key(&n) && super::builtins::get(&n).is_none() && var_index(&n).is_none() && free_name(&n) && heads[..k].iter().all(|j| j.as_ref().is_none_or(|j| j.name != n));
            if !free {
                continue;
            }
            // A name token is a part of the item's text, which rules out most items unlexed.
            let mut uses = |j: usize| tokens(items, lexed, j).iter().filter(|t| matches!(t, Tok::Name(m) if *m == n)).count();
            let own = items[k].1.matches(n.as_str()).count() > 1 && uses(k) > 1;
            let Some(first) = (0..k).find(|j| items[*j].1.contains(n.as_str()) && uses(*j) > 0).or(own.then_some(k)) else { continue };
            // After the imports before that item, which must not see it.
            let at = items[..first].iter().rposition(|(_, s)| s.starts_with("(import")).map_or(0, |i| i + 1);
            out.push((at, heads[k].take().unwrap()));
        }
        out
    }

    /// Makes the functions `ahead` callable before their definitions: each has its place in
    /// `defs` until its definition takes it over, with the signature `found` gives it, else
    /// the one its head declares.
    fn declare<'h>(&mut self, ahead: impl Iterator<Item = &'h Head>, found: &[std::sync::Arc<Def>], defs: &mut Defs, lets: &mut Lets) {
        for h in ahead {
            if defs.contains_key(&h.name) {
                continue;
            }
            let slot = self.defs.len();
            let def = match found.iter().find(|d| d.name == h.name) {
                Some(d) => Def { name: d.name.clone(), params: d.params.clone(), body: std::sync::Arc::new(Pipe::id()), inline: false, flat: false, input: d.input.clone(), step: d.step, steps: d.steps, value: d.value.clone(), implicit: d.implicit.clone(), timed: d.timed, slot: Some(slot) },
                None => match declared(h, slot) {
                    Some(d) => d,
                    None => continue,
                },
            };
            let def = std::sync::Arc::new(def);
            self.defs.push(def.clone());
            defs.insert(h.name.clone(), Named { pipe: Call::bare(&def), flat: false, run: true, params: def.params.clone(), def: Some(def), input: None });
            lets.ahead.declared.push(h.name.clone());
        }
    }

    /// The items of a program's text applied in turn: forms `(let ...)`, `(def ...)` and
    /// `(import "PATH")`, `NAME = VALUE` items (`assign_top`) and statements, each ending at the
    /// end of a line outside parentheses that does not end in `|`; `#` starts a comment to
    /// the end of the line. `lines` puts the line number before an error.
    pub(crate) fn apply_source(&mut self, text: &str, defs: &mut Defs, lets: &mut Lets, lines: bool) -> Result<(), String> {
        let (mut form, mut depth, mut start) = (String::new(), 0i32, 0);
        let mut items: Vec<(usize, String)> = Vec::new();
        for (n, line) in text.lines().enumerate() {
            let code = code_part(line).trim_end();
            if depth == 0 && code.trim().is_empty() && form.is_empty() {
                continue;
            }
            if depth == 0 && form.is_empty() {
                start = n + 1;
            }
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
            items.push((start, std::mem::take(&mut form)));
            depth = 0;
        }
        if !form.is_empty() {
            lex(&form)?;
            return Err(format!("line {start}: unclosed form: {form}"));
        }
        let mut lexed = vec![None; items.len()];
        let ahead = Passes::called_ahead(&items, &mut lexed, defs);
        if ahead.is_empty() {
            return self.items(&items, lexed, &[], &[], defs, lets, lines, false);
        }
        // Read twice when a call before a definition took another signature than the
        // definition gives, the second time with the signatures the first found.
        let outer = std::mem::take(&mut lets.ahead);
        let saved = (self.clone(), defs.clone(), lets.clone(), PARSED.with(|g| g.borrow().clone()));
        let first = self.items(&items, lexed, &ahead, &[], defs, lets, lines, true);
        let r = if first.is_ok() && !lets.ahead.retry {
            first
        } else {
            let found = std::mem::take(&mut lets.ahead.found);
            (*self, *defs, *lets) = (saved.0, saved.1, saved.2);
            PARSED.with(|g| *g.borrow_mut() = saved.3);
            lets.ahead.second = true;
            self.items(&items, vec![None; items.len()], &ahead, &found, defs, lets, lines, false).map_err(|e| match ahead.iter().map(|(_, h)| h).find(|h| !found.iter().any(|d| d.name == h.name) && e.contains(&h.name)) {
                Some(h) => format!("{e}; {} is called before its definition, where a call reads it by its head: a function that gives a group, its parameters of the types written", h.name),
                None => e,
            })
        };
        lets.ahead = outer;
        r
    }

    /// The functions `ahead` are declared before their items (`declare`); `lexed` holds the
    /// tokens of the items lexed before;
    /// `all`: past an error too, which the result gives, to find the later definitions.
    #[allow(clippy::too_many_arguments)]
    fn items(&mut self, items: &[(usize, String)], lexed: Vec<Option<Lexed>>, ahead: &[(usize, Head)], found: &[std::sync::Arc<Def>], defs: &mut Defs, lets: &mut Lets, lines: bool, all: bool) -> Result<(), String> {
        let mut first = Ok(());
        for (k, ((start, item), toks)) in items.iter().zip(lexed).enumerate() {
            self.declare(ahead.iter().filter(|(at, _)| *at == k).map(|(_, h)| h), found, defs, lets);
            let toks = toks.and_then(Result::ok).filter(|_| !may_join_names(item));
            if let Err(e) = self.item(item, toks, defs, lets) {
                first = first.and(Err(if lines { format!("line {start}: {e}") } else { e }));
                if !all {
                    break;
                }
            }
        }
        first
    }

    /// One top-level item.
    fn item(&mut self, item: &str, toks: Option<Vec<Tok>>, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        let head = item.strip_prefix('(').map(|r| r.split(|c: char| c.is_whitespace() || c == '(' || c == ')').next().unwrap_or(""));
        match head {
            Some("import") => return self.import_item(item, defs, lets),
            Some("let" | "def" | "extern") => return self.form(item, toks, defs, lets),
            _ => {}
        }
        let default = lets.in_default();
        let Some((name, val)) = top_assignment(item) else { return self.statement(item, toks, defs, lets) };
        if var_index(name).is_some() || slash_name(name).is_some() {
            return self.assign_top(name, val, default, lets.top.value, defs).map_err(|e| format!("{item}: {e}"));
        }
        let mut top = lets.top.clone();
        let mut used = Vec::new();
        match parse_statement(item, toks, defs, &mut top, &mut used) {
            Ok(tops) if !matches!(tops.as_slice(), [Top { pipe: Pipe::Bind(Slot::Local(_, Holds::Num), _), .. }]) => {
                lets.top = top;
                lets.used.extend(used);
                self.program.extend(tops);
                Ok(())
            }
            _ => self.assign_top(name, val, default, lets.top.value, defs).map_err(|e| format!("{item}: {e}")),
        }
    }

    /// A statement: its steps join the program's.
    fn statement(&mut self, item: &str, toks: Option<Vec<Tok>>, defs: &Defs, lets: &mut Lets) -> Result<(), String> {
        let tops = parse_statement(item, toks, defs, &mut lets.top, &mut lets.used)?;
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
        let fresh = self.program.is_empty() && self.defs.is_empty() && defs.len() == PRELUDE.len() && self.globals.is_empty();
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
    /// definition of `default` as `none` adds no step. `input`: a statement before gave a value.
    pub(crate) fn assign_top(&mut self, name: &str, val: &str, default: bool, input: bool, defs: &Defs) -> Result<(), String> {
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
                if defs.get(name).is_some_and(|d| d.run && d.params.is_empty()) {
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
        self.program.push(Top { pipe: parse_assign_on(name, val, input)?, gives: Gives::Nothing });
        Ok(())
    }
}

/// The names the prelude (`src/lang/prelude.pipe`) defines, which every program starts with.
static PRELUDE: std::sync::LazyLock<Defs> = std::sync::LazyLock::new(|| {
    let (mut passes, mut defs, mut lets) = (Passes::base(), Defs::new(), Lets::default());
    lets.importing.push(("prelude".into(), None));
    let mut globals = Vec::new();
    parsing(&mut globals, || passes.apply_source(include_str!("prelude.pipe"), &mut defs, &mut lets, true)).unwrap_or_else(|e| panic!("src/lang/prelude.pipe: {e}"));
    assert!(passes.defs.is_empty() && passes.program.is_empty(), "the prelude only puts functions in place");
    defs
});

/// The names the prelude defines.
pub fn prelude() -> Defs {
    PRELUDE.clone()
}

/// `NAME = VALUE` split into its name and value.
pub(crate) fn top_assignment(item: &str) -> Option<(&str, &str)> {
    let (name, val) = item.split_once('=')?;
    let name = name.trim_end();
    (is_name(name) && !val.starts_with('=')).then_some((name, val.trim()))
}

/// An item lexed.
type Lexed = Result<Vec<Tok>, String>;

/// The tokens of item `k`, lexed on first use into `lexed`; none where it does not lex.
fn tokens<'l>(items: &[(usize, String)], lexed: &'l mut [Option<Lexed>], k: usize) -> &'l [Tok] {
    lexed[k].get_or_insert_with(|| lex(&items[k].1)).as_deref().unwrap_or(&[])
}

/// Whether `s` is a name a variable can have.
pub(crate) fn is_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '/')
}

/// What the parse of a program keeps between its items: the `let` and `def` names defined
/// after the import of `default` and the names used, for the warnings; the local variables
/// the statements bound; the files being imported and those imported.
#[derive(Clone, Default)]
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
    /// The functions the source read calls before their definitions.
    pub(crate) ahead: Ahead,
}

/// The functions a source text calls before their definitions (`Passes::declare`).
#[derive(Clone, Default)]
pub(crate) struct Ahead {
    /// Those whose definitions are still to come.
    pub(crate) declared: Vec<String>,
    /// The functions the text defined.
    pub(crate) found: Vec<std::sync::Arc<Def>>,
    /// A definition gave another signature than its calls before it took.
    pub(crate) retry: bool,
    /// The second reading, with the signatures of the first.
    pub(crate) second: bool,
}

impl Lets {
    /// Whether the item read is in `default` or the prelude.
    pub(crate) fn in_default(&self) -> bool {
        self.importing.iter().any(|(k, _)| k == "default" || k == "prelude")
    }
}
