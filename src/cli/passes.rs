//! The `--passes` spec: its items (`key=value`, `off=`, `pre=`, `polish=a,b`, `pipeline=P`,
//! `file=PATH`, definitions), written as the program source they stand for, and the
//! `--passes` form of a program read back.

use crate::lang::Program;
use crate::lang::ast::{Pipe, Slot, pretty, show, show_assigned};
use crate::lang::defs::{pretty_def, show_def, sig_of};
use crate::lang::lexer::{code_part, is_old_syntax, quoted, slash_name};
use crate::lang::parser::{parse, parse_assign};
use crate::lang::source::{is_name, top_assignment};
use crate::lang::vars::{var, var_index, var_names};
use crate::passes::{DEFAULT, Passes, RULESETS, STEPS, Step};
use crate::rust_vars::INNER;
use std::fmt;

/// The items `NAME=P` that define a function of `default.pipe` without parameters, `(def (DEF)
/// P)`, by `NAME` and `DEF`.
pub const PIPELINES: [(&str, &str); 5] = [("pipeline", "pipeline"), ("prepass", "prepass_steps"), ("polish", "polish_steps"), ("rewrite", "rewrite"), ("simba", "simba_steps")];

/// A change of the egglog schedule a `schedule` item makes.
pub type ScheduleEdit = Box<dyn Fn(&mut Vec<(Step, &'static str)>)>;

/// The items of `spec`: separated by `;`, or by white space before a `key=`, `NAME =`, `(let`
/// or `(def` outside parentheses that does not follow a `|` (so `prepass=a | split_runs=4 | b`
/// is one item); `#` starts a comment to the end of the line.
fn items(spec: &str) -> Vec<String> {
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
    items
}

/// The program source the items of `spec` stand for, one item a line or form, and the changes
/// its `schedule` items make. The names of `PIPELINES` take a pipeline, `(def (DEF) P)`, and
/// `polish` also a list of polish pass names (`polish`); `file=PATH` is `(import "PATH")`; `off`, `pre` and `schedule` take lists of
/// names separated by `,`, also as `key+=names` and `key-=names` (`pre` the switches `pre_NAME`
/// by `NAME`, `schedule` the steps `run:`, `once:` or `sat:` and a ruleset); any other key is a
/// variable that exists, assigned. Definitions and `NAME = VALUE` with spaces around `=` are
/// items of the source as they are.
pub fn translate(spec: &str) -> Result<(String, Vec<ScheduleEdit>), String> {
    let mut out = String::new();
    let mut edits: Vec<ScheduleEdit> = Vec::new();
    // Variables an earlier item may define, which `NAME=VALUE` cannot check before the program is read.
    let mut defining = false;
    let mut line = |s: &str| {
        out.push_str(s);
        out.push('\n');
    };
    let read = |val: &str| match is_old_syntax(val) {
        true => parse(val).map(|_| ()).map_err(|e| format!("{e} (the old seq(a,b) syntax is no longer read: write a | b, (best 1 a b), (if c a))")),
        false => Ok(()),
    };
    for item in items(spec) {
        let item = item.as_str();
        if item.starts_with('(') {
            line(item);
            continue;
        }
        if top_assignment(item).is_some_and(|(n, _)| item[n.len()..].starts_with(char::is_whitespace)) {
            defining = true;
            line(&item.replace(['\n', '\r'], " "));
            continue;
        }
        if let Some(path) = item.strip_prefix("file=") {
            defining = true;
            line(&format!("(import {})", quoted(path)));
            continue;
        }
        if let Some(e) = item.split(['=', '+']).next().and_then(slash_name) {
            return Err(format!("{item}: {e}"));
        }
        if let Some(val) = item.strip_prefix("polish=") {
            let names: Vec<&str> = val.split(',').filter(|s| !s.is_empty()).collect();
            let all_polish = names.iter().all(|n| crate::linear_mba::POLISH.iter().any(|(m, _)| m == n));
            match all_polish {
                true => line(&format!("(def (polish_steps) {})", polish(&names))),
                false => {
                    read(val)?;
                    line(&format!("(def (polish_steps) {val})"));
                }
            }
            continue;
        }
        if let Some((name, val)) = item.split_once('=') {
            if let Some((_, def)) = PIPELINES.iter().find(|(n, _)| *n == name) {
                read(val)?;
                line(&format!("(def ({def}) {val})"));
                continue;
            }
            if name.starts_with("sub_") {
                return Err(format!("{name}=P is no longer read: a pass takes the function it runs on parts of its term as an argument, as in (relate rewrite)"));
            }
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
                line(&format!("pre_{n} = {}", u8::from(on)));
            }
            continue;
        }
        // `off=a,b` turns every `INNER` pass on and then `a`, `b` off.
        if key == "off" {
            let ns = names(&INNER)?;
            if op == "=" {
                line(&format!("(on {})", INNER.join(" ")));
            }
            if !ns.is_empty() {
                line(&format!("({} {})", if op == "-=" { "on" } else { "off" }, ns.join(" ")));
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
            edits.push(match op {
                "=" => Box::new(move |s: &mut Vec<_>| *s = steps.clone()),
                "+=" => Box::new(move |s: &mut Vec<_>| s.extend(steps.iter().copied())),
                _ => Box::new(move |s: &mut Vec<_>| s.retain(|x| !steps.contains(x))),
            });
            continue;
        }
        if op != "=" {
            return Err(format!("{key} is not a list: {item}"));
        }
        if !defining || var_index(key).is_some() {
            parse_assign(key, val).map_err(|e| format!("{item}: {e}"))?;
        }
        line(&format!("{key} = {}", val.replace(['\n', '\r'], " ")));
    }
    Ok((out, edits))
}

impl Passes {
    /// The program `(import "default")` changed by the `--passes` items of `spec` (`translate`).
    pub fn parse(spec: &str) -> Result<Passes, String> {
        Passes::parse_noting(spec).map(|(p, _)| p)
    }

    /// `parse`, and the warnings of reading it (`Program::finish`).
    pub fn parse_noting(spec: &str) -> Result<(Passes, Vec<String>), String> {
        if spec.trim().is_empty() {
            return Ok((DEFAULT.0.clone(), Vec::new()));
        }
        let (source, schedule) = translate(spec)?;
        let mut prog = Program::new();
        prog.read("(import \"default\")")?;
        prog.read(&source)?;
        schedule.into_iter().for_each(|edit| edit(&mut prog.passes.schedule));
        prog.finish()
    }
}

/// The polish `polish=a,b,...` writes: the polish passes `names` in turn, each kept when
/// smaller, repeated while one is, until `polish_wins` are, as the default in `default.pipe`,
/// with the functions it gives them.
pub fn polish(names: &[&str]) -> String {
    let step = |n: &&str| {
        let call = match *n {
            "join_constants" | "join_linear" | "recombine" => format!("(polish_{n} rewrite)"),
            "over_const_bitwise" | "over_shared_bitwise" | "over_products" | "shift_cases" => format!("(polish_{n} (rebuild rewrite))"),
            _ => format!("polish_{n}"),
        };
        let run = format!("{call} | drop_identities");
        let run = if *n == "join_linear" { format!("(semi_leaves = 2 | {run})") } else { run };
        format!("(smaller polish_{n} {run})")
    };
    let steps: Vec<String> = names.iter().map(step).collect();
    let steps = if steps.len() == 1 { format!("(seq {})", steps[0]) } else { steps.join("\n  | ") };
    format!("(scope rewrites = polish_rewrites\n  | (wins polish_wins\n  {steps}))")
}

/// The spec `Passes::parse` reads back to these passes: the top-level steps from `shown_from`
/// on as `--passes` items, the functions defined past `default`, the pipelines; `{:#}` puts
/// each pipeline on its own lines.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(f, "schedule={}", steps.join(","))?;
        let spec: Vec<&Pipe> = self.program[self.shown_from..].iter().map(|t| &t.pipe).collect();
        let mut i = 0;
        while i < spec.len() {
            let names = |ns: &[&str]| ns.join(",");
            fn switches<'a>(p: Option<&&'a Pipe>) -> Option<(bool, Vec<&'a str>)> {
                match p {
                    Some(Pipe::Expanded(m)) => m.switch_names(),
                    _ => None,
                }
            }
            match (spec[i], switches(spec.get(i))) {
                (_, Some((true, ns))) if ns == INNER => match switches(spec.get(i + 1)) {
                    Some((false, off)) if off.iter().all(|n| INNER.contains(n)) => {
                        write!(f, " off={}", names(&off))?;
                        i += 1;
                    }
                    _ => write!(f, " off=")?,
                },
                (_, Some((false, ns))) => write!(f, " off+={}", names(&ns))?,
                (_, Some((true, ns))) => write!(f, " off-={}", names(&ns))?,
                (Pipe::Bind(Slot::Global(_), _), _) if self.defines.contains(&(self.shown_from + i)) => write!(f, " {}", show(spec[i]))?,
                (Pipe::Bind(Slot::Global(v), val), _) => write!(f, " {}={}", var(*v).name, show_assigned(val))?,
                (p, _) => write!(f, " {}", show(p))?,
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
        for (name, def) in PIPELINES {
            if let Some(p) = self.body(def) {
                write!(f, "{sep}{name}={}", show(p))?;
            }
        }
        Ok(())
    }
}
