//! Runs a `sched::Pipe`. Every pass maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another: a pass over one term (`linear_mba::TERM_PASSES`, the
//! polish passes as `polish/NAME`) runs on each candidate and replaces it by its result; the
//! other passes take the list whole.

use crate::eval::{parse, show, size};
use crate::sched::{Cond, Pipe};
use crate::{Cli, Error, linear_mba, minimal, stats, width_of};
use std::cell::{Cell, RefCell};

/// Passes that take the candidate list whole.
const SET_PASSES: [&str; 6] = [
    // The candidates unchanged.
    "id",
    // The main candidate's pre-pass rebuilds: the main one, then those to union with it.
    "prepass",
    // One egglog round on all candidates unioned: its extraction (`egglog/LABEL` times it
    // as `egglog/LABEL`).
    "egglog",
    // The first candidate proved minimal (`minimal`).
    "take_minimal",
    // The polish passes of `Passes::polish` on each candidate, kept when smaller.
    "polish",
    // The main candidate printed and read back.
    "reprint",
];

/// The conditions of `if` and `retry`, on the candidates they see.
pub const CONDS: [&str; 8] = [
    // The main candidate has a shift, division or mulhi and its rebuild is not tiny.
    "opaque",
    // A candidate is proved minimal: no smaller term equals it (`Passes::minimal`).
    "minimal",
    // The main candidate has arithmetic or a constant directly under a bitwise operation.
    "mixed",
    // The pre-pass changes the main candidate.
    "rebuilds",
    // The last `fix` stopped at its count, the main candidate still changing.
    "moved",
    // The main candidate is the input of `simplify`.
    "input",
    // `Passes::rerun_input`.
    "rerun_input",
    // `Passes::printed` is not 0.
    "printed",
];

/// The names a `fix` count can take: `restarts` (`Cli::max_restarts` less the first
/// round), `extra` (`Passes::extra`), `printed` (`Passes::printed` less the first round).
pub const COUNTS: [&str; 3] = ["restarts", "extra", "printed"];

/// The names a `Pipe::Pass` can take.
pub fn names() -> Vec<String> {
    let polish = linear_mba::POLISH.iter().map(|(n, _)| format!("polish/{n}"));
    let egglog = ["first", "later", "rerun_input"].iter().map(|l| format!("egglog/{l}"));
    SET_PASSES.iter().map(|n| n.to_string()).chain(egglog).chain(linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string())).chain(polish).collect()
}

/// A candidate term and the pass it came from, for `stats` (`final/ORIGIN`).
#[derive(Clone, Debug, PartialEq)]
pub struct Cand {
    pub term: String,
    pub origin: String,
}

/// What the passes of one `simplify` call share.
pub struct Env<'a> {
    pub cli: &'a Cli,
    /// The egglog program of the numeric type.
    pub egg: String,
    /// The input of `simplify`.
    pub input: String,
    moved: Cell<bool>,
    /// The smallest candidate each enclosing `smallest` saw, innermost last.
    seen: RefCell<Vec<Option<(usize, Cand)>>>,
}

impl<'a> Env<'a> {
    pub fn new(cli: &'a Cli, egg: String, input: &str) -> Env<'a> {
        Env { cli, egg, input: input.to_string(), moved: Cell::new(false), seen: RefCell::new(Vec::new()) }
    }

    fn w(&self) -> u32 {
        width_of(&self.cli.num_type)
    }

    fn prepass(&self, s: &str) -> (String, Vec<String>) {
        linear_mba::simplify_linear_with(s, self.w(), self.cli.trace, &self.cli.passes)
    }

    fn count(&self, n: &str) -> usize {
        let p = &self.cli.passes;
        match n {
            "restarts" => self.cli.max_restarts.max(1) - 1,
            "extra" => p.extra,
            "printed" => p.printed.saturating_sub(1),
            _ => n.parse().unwrap(),
        }
    }
}

fn dedup(set: Vec<Cand>) -> Vec<Cand> {
    let mut out: Vec<Cand> = Vec::with_capacity(set.len());
    for c in set {
        if !out.iter().any(|o| o.term == c.term) {
            out.push(c);
        }
    }
    out
}

fn size_of(s: &str) -> usize {
    size(&parse(s))
}

const OPAQUE: [&str; 5] = ["(Shl ", "(Shr ", "(Div ", "(Mod ", "(Mulhi "];

/// The first candidate of `set` proved minimal. Without a shift, division or mulhi in the
/// candidates, only smaller terms without them need ruling out: no rule makes one.
fn proved_minimal<'s>(set: &'s [Cand], env: &Env) -> Option<&'s Cand> {
    if !env.cli.passes.minimal {
        return None;
    }
    let t_only = !OPAQUE.iter().any(|o| set.iter().any(|c| c.term.contains(o)));
    let ty = crate::eval::NumType::from_name(&env.cli.num_type);
    set.iter().find(|c| {
        let t = parse(&c.term);
        minimal::is_tidy(&t) && (ty.is_some_and(|ty| minimal::is_minimal(&t, ty)) || t_only && minimal::is_t_minimal(&t))
    })
}

fn holds(c: &Cond, set: &[Cand], env: &Env) -> bool {
    let Some(main) = set.first() else { return false };
    c.0.iter().all(|(neg, name)| {
        let v = match name.as_str() {
            "opaque" => OPAQUE.iter().any(|o| main.term.contains(o)) && size_of(&env.prepass(&main.term).0) > linear_mba::TINY,
            "minimal" => proved_minimal(set, env).is_some(),
            "mixed" => crate::mixed(&parse(&main.term)),
            "rebuilds" => env.prepass(&main.term).0 != main.term,
            "moved" => env.moved.get(),
            "input" => main.term == env.input,
            "rerun_input" => env.cli.passes.rerun_input,
            "printed" => env.cli.passes.printed > 0,
            _ => unreachable!("condition {name}"),
        };
        v != *neg
    })
}

/// The candidates `p` gives for `set`.
pub fn run(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    crate::sched::apply(&env.cli.passes);
    go(p, set, env)
}

fn go(p: &Pipe, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    match p {
        Pipe::Pass(name) => pass(name, set, env),
        Pipe::Seq(ps) => ps.iter().try_fold(set, |s, p| go(p, s, env)),
        Pipe::Union(ps) => {
            let mut out = Vec::new();
            for p in ps {
                out.extend(go(p, set.clone(), env)?);
            }
            Ok(dedup(out))
        }
        Pipe::Best(k, ps) => {
            let mut out = Vec::new();
            for p in ps {
                out.extend(go(p, set.clone(), env)?);
            }
            let mut out = dedup(out);
            out.sort_by_cached_key(|c| size_of(&c.term));
            out.truncate((*k).max(1));
            Ok(out)
        }
        Pipe::First(ps) => {
            for p in ps {
                let out = go(p, set.clone(), env)?;
                if out != set {
                    return Ok(out);
                }
            }
            Ok(set)
        }
        Pipe::Fix(n, p) => {
            let mut set = set;
            for _ in 0..env.count(n) {
                let out = go(p, set.clone(), env)?;
                let same = out.first().map(|c| &c.term) == set.first().map(|c| &c.term);
                env.moved.set(!same);
                set = out;
                if same {
                    break;
                }
            }
            Ok(set)
        }
        Pipe::Off(names, p) => crate::sched::with_off(names, || go(p, set, env)),
        Pipe::If(c, a, b) => go(if holds(c, &set, env) { a } else { b }, set, env),
        Pipe::Retry(c, a, b) => {
            let out = go(a, set.clone(), env)?;
            if !holds(c, &out, env) {
                return Ok(out);
            }
            let again = go(b, set, env)?;
            let n = |s: &[Cand]| s.first().map(|c| size_of(&c.term));
            Ok(if n(&again) <= n(&out) { again } else { out })
        }
        Pipe::Smallest(p) => {
            env.seen.borrow_mut().push(None);
            let out = go(p, set, env);
            let seen = env.seen.borrow_mut().pop().flatten();
            let out = out?;
            match seen {
                Some((n, c)) if out.first().is_some_and(|m| n < size_of(&m.term)) => Ok(dedup(std::iter::once(c).chain(out).collect())),
                _ => Ok(out),
            }
        }
        Pipe::Tag(name, p) => {
            let clock = std::time::Instant::now();
            let before = set.first().map(|c| c.term.clone());
            let mut out = go(p, set, env)?;
            stats::add(&format!("{name}/run"), stats::since(clock));
            if let Some(m) = out.first_mut().filter(|m| Some(&m.term) != before.as_ref()) {
                stats::add(&format!("{name}/won/{}", m.origin), 0.0);
                m.origin = name.clone();
            }
            Ok(out)
        }
    }
}

fn pre(e: &str) -> String {
    format!("pre/{}", stats::source_of(e).unwrap_or_else(|| "unlabeled".into()))
}

fn pass(name: &str, set: Vec<Cand>, env: &Env) -> Result<Vec<Cand>, Error> {
    let cli = env.cli;
    let w = env.w();
    let Some(main) = set.first().cloned() else { return Ok(set) };
    let new = |term: String, origin: String| Cand { term, origin };
    let out = match name {
        "id" => return Ok(set),
        "prepass" => {
            let (alt, other) = env.prepass(&main.term);
            std::iter::once(alt).chain(other).map(|e| new(e.clone(), pre(&e))).collect()
        }
        "take_minimal" => match proved_minimal(&set, env) {
            Some(c) => {
                stats::add("round/minimal", 0.0);
                vec![c.clone()]
            }
            None => set.clone(),
        },
        "polish" => set
            .iter()
            .map(|c| match linear_mba::polish_with(&c.term, w, &cli.passes) {
                (p, used) if !used.is_empty() && size_of(&p) < size_of(&c.term) => {
                    if cli.trace {
                        eprintln!("polish: {} -> {} by {}", size_of(&c.term), size_of(&p), used.join(","));
                    }
                    new(p, format!("polish/{}", used.last().unwrap()))
                }
                _ => c.clone(),
            })
            .collect(),
        "reprint" => {
            let out = crate::egglog_to_infix(&main.term, &|n| crate::norm_const(n, &cli.num_type));
            vec![new(crate::infix_to_egglog(&out, true), main.origin.clone())]
        }
        _ if name == "egglog" || name.starts_with("egglog/") => {
            let roots: Vec<&str> = set.iter().map(|c| c.term.as_str()).collect();
            let clock = std::time::Instant::now();
            let e = crate::egglog_round(&env.egg, &roots, cli)?;
            stats::add(name, stats::since(clock));
            if cli.trace {
                eprintln!("{name}: root {} extracted {}", size_of(&main.term), size_of(&e));
            }
            let origin = match stats::source_of(&e) {
                Some(src) => format!("pre/{src}"),
                None => name.to_string(),
            };
            vec![new(e, origin)]
        }
        _ => {
            let f = linear_mba::term_pass(name).unwrap_or_else(|| panic!("unknown pass {name}"));
            if crate::sched::is_off(name) {
                return Ok(set);
            }
            stats::time(&format!("pipe/{name}"), || {
                let ctx = linear_mba::Ctx::new(w);
                set.iter()
                    .map(|c| {
                        let t = parse(&c.term);
                        match f(&t, &ctx) {
                            Some(r) if r != t => new(show(&r), name.to_string()),
                            _ => c.clone(),
                        }
                    })
                    .collect()
            })
        }
    };
    // A term a pass gives back keeps the origin it came with.
    let out: Vec<Cand> = dedup(out)
        .into_iter()
        .map(|c| match set.iter().find(|s| s.term == c.term) {
            Some(s) => s.clone(),
            None => c,
        })
        .collect();
    for scope in env.seen.borrow_mut().iter_mut() {
        for c in &out {
            let n = size_of(&c.term);
            if scope.as_ref().is_none_or(|(m, _)| n < *m) {
                *scope = Some((n, c.clone()));
            }
        }
    }
    Ok(out)
}
