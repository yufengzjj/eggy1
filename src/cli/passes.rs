//! The `--passes` spec: its items (`key=value`, `off=`, `pre=`, `polish=a,b`, `pipeline=P`,
//! `sub_NAME=P`, `file=PATH`, definitions), read into `Passes`, and written back.

use crate::lang::ast::{Expanded, Pipe, Slot, pretty, show, show_assigned};
use crate::lang::defs::{DefKind, Defs, pretty_def, show_def, sig_of};
use crate::lang::lexer::{code_part, is_old_syntax, slash_name};
use crate::lang::parser::{parse_assign, parse_with};
use crate::lang::source::{Lets, is_name, top_assignment};
use crate::lang::vars::{parsing, var, var_names};
use crate::passes::{DEFAULT, Passes, RULESETS, STEPS, SUBS, check_of, defined_builtin};
use crate::rust_vars::{INNER, ITER_LIMIT, RESTARTS};
use std::fmt;

impl Passes {
    /// The assignments a run starts with: those of `default.pipe`, then `restarts = m` and
    /// `iter_limit = i` of the command line (`cli`), then those of `--passes`.
    pub fn entry_steps(&self, cli: Option<(usize, usize)>) -> Vec<Pipe> {
        let (base, spec) = self.entry.split_at(self.defaults);
        let num = |i: usize, n: usize| Pipe::assign(i, Pipe::Num(n as u64));
        let cli = cli.map(|(m, i)| [num(RESTARTS, m), num(ITER_LIMIT, i)]);
        base.iter().cloned().chain(cli.into_iter().flatten()).chain(spec.iter().cloned()).collect()
    }

    /// `{:#}` after a comment line with the run it describes: `entry_steps` for `-m m -i i`,
    /// `check_limits`, then `pipeline` (`--show-passes`).
    pub fn show_run(&self, m: usize, i: usize) -> String {
        let steps: Vec<String> = self.entry_steps(Some((m, i))).iter().map(show).collect();
        format!("# A run: {} | check_limits | pipeline
{self:#}", steps.join(" | "))
    }

    /// The default pipeline changed by `spec`: items `key=value`, and for the lists `pre`,
    /// `off` and `schedule` also `key+=names` and `key-=names` (names separated by `,`;
    /// schedule steps written `run:`, `once:` or `sat:` and a ruleset). `pipeline`,
    /// `prepass`, `polish`, `rewrite`, `simba` and `sub_NAME` (`SUBS`) take a pipeline
    /// (`crate::lang`), and `polish` also a list of polish pass names, run as
    /// `polish(names)`. Any other key is a variable that exists: the item is an entry
    /// assignment (`entry`), as are the `off` and `pre` items (`pre` lists the switches
    /// `pre_NAME` by `NAME`).
    /// `(let NAME p)` and `(def ...)` define a name for the items after it (those of
    /// `default.pipe` come first); `pipeline=p` and the like are `(def (pipeline) p)`.
    /// `NAME = VALUE` with spaces around `=` is the item of a source file (`assign_top`), and
    /// `file=PATH` reads a source file there (`apply_source`). Items are separated by `;`, or
    /// by white space before a `key=`, `NAME =`, `(let` or `(def` outside parentheses that does
    /// not follow a `|` (so `prepass=a | split_runs=4 | b` is one item); `#` starts a comment
    /// to the end of the line.
    pub fn parse(spec: &str) -> Result<Passes, String> {
        Passes::parse_noting(spec).map(|(p, _)| p)
    }

    /// `parse`, and warnings about parts of `spec` that do nothing: a `let` or `def` it defines and
    /// never uses, and what `Passes::warnings` finds.
    pub fn parse_noting(spec: &str) -> Result<(Passes, Vec<String>), String> {
        let (mut p, mut defs) = DEFAULT.clone();
        let mut lets = Lets::default();
        let mut globals = std::mem::take(&mut p.globals);
        let r = parsing(&mut globals, || p.apply(spec, &mut defs, &mut lets));
        p.globals = globals;
        r?;
        p.check = check_of(&defs);
        p.check()?;
        // The Rust code runs `check_limits` (`Passes::check`).
        let unused = lets.defined.iter().filter(|(head, _)| head != "check_limits" && !lets.used.iter().any(|n| head.split(' ').next() == Some(n)));
        let mut notes: Vec<String> = unused
            .map(|(n, k)| match k {
                DefKind::Let => format!("(let {n} ...) is never used: a name is expanded only where a later item writes it"),
                DefKind::Inline => format!("(def @inline ({n}) ...) is never used: it is expanded only where a later item calls it"),
                DefKind::Run => format!("(def ({n}) ...) is never used: it runs only where a later item calls it"),
            })
            .collect();
        notes.extend(lets.notes);
        notes.extend(p.warnings());
        notes.dedup();
        Ok((p, notes))
    }

    /// The items of `spec` applied in turn.
    pub(crate) fn apply(&mut self, spec: &str, defs: &mut Defs, lets: &mut Lets) -> Result<(), String> {
        let p = self;
        let read = |val: &str, defs: &Defs, used: &mut Vec<String>| {
            parse_with(val, defs, used).map_err(|e| match is_old_syntax(val) {
                true => format!("{e} (the old seq(a,b) syntax is no longer read: write a | b, (best 1 a b), (if c a))"),
                false => e,
            })
        };
        let spec: String = spec.lines().map(code_part).collect::<Vec<_>>().join("\n");
        let mut items: Vec<String> = Vec::new();
        let (mut depth, mut cur, mut fresh, mut after_bar) = (0i32, String::new(), true, false);
        let (mut in_str, mut esc) = (false, false);
        let mut chunks = Vec::new();
        for c in spec.chars() {
            match c {
                _ if esc => esc = false,
                '\\' if in_str => esc = true,
                '"' => in_str = !in_str,
                '(' if !in_str => depth += 1,
                ')' if !in_str => depth -= 1,
                _ => {}
            }
            if depth == 0 && !in_str && (c.is_whitespace() || c == ';') {
                chunks.push((std::mem::take(&mut cur), c == ';'));
            } else {
                cur.push(c);
            }
        }
        chunks.push((cur, false));
        chunks.retain(|(c, ends)| !c.is_empty() || *ends);
        let spaced: Vec<bool> = (0..chunks.len()).map(|k| is_name(&chunks[k].0) && chunks.get(k + 1).is_some_and(|(c, _)| c == "=")).collect();
        for (k, (chunk, ends)) in chunks.into_iter().enumerate() {
            if !chunk.is_empty() {
                let key: String = chunk.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '/').collect();
                let def = ["(let", "(def", "(extern"].iter().any(|s| chunk.starts_with(s));
                let starts = def || spaced[k] || !key.is_empty() && ["=", "+=", "-="].iter().any(|op| chunk[key.len()..].starts_with(op));
                let bar = chunk.ends_with('|');
                match items.last_mut() {
                    Some(last) if !fresh && (!starts || after_bar) => *last = format!("{last} {chunk}"),
                    _ => items.push(chunk),
                }
                fresh = def;
                after_bar = bar;
            }
            fresh |= ends;
            after_bar &= !ends;
        }
        for item in items.iter().map(String::as_str) {
            if item.starts_with('(') {
                p.form(item, defs, lets)?;
                continue;
            }
            if let Some((name, val)) = top_assignment(item).filter(|(n, _)| item[n.len()..].starts_with(char::is_whitespace)) {
                p.assign_top(name, val, false, defs).map_err(|e| format!("{item}: {e}"))?;
                continue;
            }
            if let Some(path) = item.strip_prefix("file=") {
                let text = std::fs::read_to_string(path).map_err(|e| format!("file={path}: {e}"))?;
                p.apply_source(&text, defs, lets, false).map_err(|e| format!("{path}: {e}"))?;
                continue;
            }
            if let Some(e) = item.split(['=', '+']).next().and_then(slash_name) {
                return Err(format!("{item}: {e}"));
            }
            if let Some(val) = item.strip_prefix("polish=") {
                let names: Vec<&str> = val.split(',').filter(|s| !s.is_empty()).collect();
                let all_polish = names.iter().all(|n| crate::linear_mba::POLISH.iter().any(|(m, _)| m == n));
                p.polish = if all_polish { read(&polish(&names), defs, &mut lets.used)? } else { read(val, defs, &mut lets.used)? };
                continue;
            }
            if let Some((name, val)) = item.split_once('=').filter(|(k, _)| defined_builtin(k) || k.starts_with("sub_")) {
                p.define(name, read(val, defs, &mut lets.used)?)?;
                continue;
            }
            let (key, op, val) = ["+=", "-=", "="]
                .iter()
                .find_map(|op| item.split_once(op).map(|(k, v)| (k, *op, v)))
                .ok_or_else(|| format!("expected key=value: {item}"))?;
            let names = |known: &[&'static str]| -> Result<Vec<&'static str>, String> {
                let unknown = |n: &str| slash_name(n).unwrap_or_else(|| format!("unknown {key} name {n}; known: {}", known.join(",")));
                val.split(',').filter(|s| !s.is_empty()).map(|n| known.iter().find(|k| **k == n).copied().ok_or_else(|| unknown(n))).collect()
            };
            // `pre=a,b` sets the switches `pre_a`, `pre_b` to 1 and the other `pre_*` to 0.
            if key == "pre" {
                let all: Vec<&'static str> = var_names().into_iter().filter_map(|n| n.strip_prefix("pre_")).collect();
                let ns = names(&all)?;
                let set: Vec<(&str, bool)> = match op {
                    "=" => all.iter().map(|n| (*n, ns.contains(n))).collect(),
                    _ => ns.iter().map(|n| (*n, op == "+=")).collect(),
                };
                for (n, on) in set {
                    p.entry.push(parse_assign(&format!("pre_{n}"), if on { "1" } else { "0" })?);
                }
                continue;
            }
            // `off=a,b` turns every `INNER` pass on and then `a`, `b` off.
            if key == "off" {
                let ns = names(&INNER)?;
                if op == "=" {
                    p.entry.push(Expanded::switches(true, &INNER));
                }
                if !ns.is_empty() {
                    p.entry.push(Expanded::switches(op == "-=", &ns));
                }
                continue;
            }
            if key == "schedule" {
                let steps = val
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| {
                        let (kind, rs) = s.split_once(':').ok_or_else(|| format!("expected run:, once: or sat: and a ruleset: {s}"))?;
                        let step = STEPS.iter().find(|(_, k)| *k == kind).ok_or_else(|| format!("unknown step kind {kind}; known: run once sat"))?.0;
                        let rs = RULESETS.iter().find(|r| **r == rs).ok_or_else(|| format!("unknown ruleset {rs}; known: {}", RULESETS.join(",")))?;
                        Ok((step, *rs))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                match op {
                    "=" => p.schedule = steps,
                    "+=" => p.schedule.extend(steps),
                    _ => p.schedule.retain(|s| !steps.contains(s)),
                }
                continue;
            }
            if op != "=" {
                return Err(format!("{key} is not a list: {item}"));
            }
            p.entry.push(parse_assign(key, val).map_err(|e| format!("{item}: {e}"))?);
        }
        Ok(())
    }
}

/// The polish `polish=a,b,...` writes: the polish passes `names` in turn, each kept when
/// smaller, repeated while one is, until `polish_wins` are, as the default in `default.pipe`.
pub fn polish(names: &[&str]) -> String {
    let step = |n: &&str| {
        let run = format!("polish_{n} | drop_identities");
        let run = if *n == "join_linear" { format!("(semi_leaves = 2 | {run})") } else { run };
        format!("(smaller polish_{n} {run})")
    };
    let steps: Vec<String> = names.iter().map(step).collect();
    let steps = if steps.len() == 1 { format!("(seq {})", steps[0]) } else { steps.join("\n  | ") };
    format!("(scope rewrites = polish_rewrites\n  | (wins polish_wins\n  {steps}))")
}

/// The spec `Passes::parse` reads back to these passes; `{:#}` puts each pipeline on its own
/// lines.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(f, "schedule={}", steps.join(","))?;
        let spec = &self.entry[self.defaults..];
        let mut i = 0;
        while i < spec.len() {
            let names = |ns: &[&str]| ns.join(",");
            fn switches(p: Option<&Pipe>) -> Option<(bool, Vec<&str>)> {
                match p {
                    Some(Pipe::Expanded(m)) => m.switch_names(),
                    _ => None,
                }
            }
            match (&spec[i], switches(spec.get(i))) {
                (_, Some((true, ns))) if ns == INNER => match switches(spec.get(i + 1)) {
                    Some((false, off)) if off.iter().all(|n| INNER.contains(n)) => {
                        write!(f, " off={}", names(&off))?;
                        i += 1;
                    }
                    _ => write!(f, " off=")?,
                },
                (_, Some((false, ns))) => write!(f, " off+={}", names(&ns))?,
                (_, Some((true, ns))) => write!(f, " off-={}", names(&ns))?,
                (Pipe::Bind(Slot::Global(_), _), _) if self.defines.contains(&(self.defaults + i)) => write!(f, " {}", show(&spec[i]))?,
                (Pipe::Bind(Slot::Global(v), val), _) => write!(f, " {}={}", var(*v).name, show_assigned(val))?,
                (p, _) => unreachable!("entry step {p:?}"),
            }
            i += 1;
        }
        let show = if f.alternate() { pretty } else { show };
        let sep = if f.alternate() { "\n" } else { " " };
        for d in &self.defs[self.default_defs..] {
            if f.alternate() {
                write!(f, "\n# {}\n{}", sig_of(d), pretty_def(d))?;
            } else {
                write!(f, " {}", show_def(d))?;
            }
        }
        for (name, p) in [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)] {
            write!(f, "{sep}{name}={}", show(p))?;
        }
        for ((name, default), p) in SUBS.iter().zip(&self.subs) {
            if Some(p) != crate::lang::builtins::resolve(default).as_ref() {
                write!(f, "{sep}sub_{name}={}", show(p))?;
            }
        }
        Ok(())
    }
}
