//! The command line as a program of the language: `-n`, `-m`, `-i` and `--trace` as
//! assignments after `(import "default")`, the `--passes` items as the source they stand for
//! (`passes::translate`), then the statement that simplifies the expression; and the listing of
//! `--show-builtins`.

use crate::Cli;
use crate::lang::Program;
use crate::lang::builtins::all;
use crate::lang::lexer::quoted;
use crate::lang::types::Kind;
use crate::passes::Passes;

pub mod passes;

/// Every declaration with its description, grouped by calling kind (`--show-builtins`).
pub fn listing() -> String {
    let mut out = String::from("# The built-in functions (src/builtins.pipe), by how they are called.\n");
    for (kind, title) in Kind::ALL {
        let sigs: Vec<_> = all().iter().filter(|s| s.kind() == kind).collect();
        if sigs.is_empty() {
            continue;
        }
        out += &format!("\n# --- {title}\n");
        for s in sigs {
            out += &format!("# {}\n{}\n", s.doc, s.decl());
        }
    }
    out
}

/// The items the program starts with: the import of `default`, then the numeric type, the
/// rounds, the iteration limit and the trace of `cli`.
pub fn preamble(cli: &Cli) -> String {
    let mut out = format!("(import \"default\")\nnum_type = {}\nrestarts = {}\niter_limit = {}\n", cli.num_type, cli.max_restarts, cli.iter_limit);
    if cli.trace {
        out += "trace = 1\n";
    }
    out
}

/// The statement that simplifies `expr` (infix or an egglog term) and gives the infix of the
/// result; with `cut_note`, writing to stderr when the time limit cut the run short.
pub fn statement(expr: &str, cut_note: bool) -> String {
    let input = format!("(parse {})", quoted(&expr.replace(['\n', '\r'], " ")));
    match cut_note {
        true => format!("{input} | simplify | time_limit = none | (if was_cut (print \"time limit reached: the result is the smallest form found by then\")) | main | show\n"),
        false => format!("{input} | simplify | main | show\n"),
    }
}

/// The program `cli` stands for, read and checked: `preamble`, the `--passes` items, then
/// `statement` when given; its warnings; its source text.
pub fn parse(cli: &Cli, statement: Option<&str>) -> Result<(Passes, Vec<String>, String), String> {
    let (spec, schedule) = passes::translate(&cli.passes)?;
    let preamble = preamble(cli);
    let mut prog = Program::new();
    prog.read(&preamble)?;
    prog.passes.shown_from = prog.passes.program.len();
    prog.read(&spec)?;
    schedule.into_iter().for_each(|edit| edit(&mut prog.passes.schedule));
    if let Some(s) = statement {
        prog.read(s)?;
    }
    let (passes, warnings) = prog.finish()?;
    Ok((passes, warnings, [preamble, spec, statement.unwrap_or("").to_string()].concat()))
}

/// The program text `text` on one line, its items separated by `; `.
pub fn one_line(text: &str) -> String {
    let mut items: Vec<String> = Vec::new();
    let mut depth = 0;
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty()) {
        match items.last_mut() {
            Some(last) if depth > 0 || last.ends_with('|') => *last = format!("{last} {line}"),
            _ => items.push(line.to_string()),
        }
        depth += crate::lang::lexer::depth_of(line);
    }
    items.join("; ")
}
