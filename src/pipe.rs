//! Runs a `sched::Pipe`. Every pass maps a list of equivalent candidate egglog terms (the
//! first is the main one) to another: a pass over one term (`linear_mba::TERM_PASSES`, the
//! polish passes as `polish/NAME`) runs on each candidate and replaces it by its result; the
//! other passes take the list whole.

use crate::eval::{parse, show, size};
use crate::sched::Pipe;
use crate::{Cli, Error, linear_mba, stats, width_of};
use std::cell::RefCell;

/// Passes that take the candidate list whole.
const SET_PASSES: [&str; 6] = [
    // The candidates unchanged.
    "id",
    // The restart rounds, each a pre-pass and an egglog round, then polish: `drive`.
    "drive",
    // The run from the printed form of the main candidate, kept when smaller.
    "printed",
    // The main candidate's pre-pass rebuilds: the main one, then those to union with it.
    "prepass",
    // One egglog round on all candidates unioned: its extraction.
    "egglog",
    // The polish passes of `Passes::polish` on each candidate.
    "polish",
];

/// The names a `Pipe::Pass` can take.
pub fn names() -> Vec<String> {
    let polish = linear_mba::POLISH.iter().map(|(n, _)| format!("polish/{n}"));
    SET_PASSES.iter().map(|n| n.to_string()).chain(linear_mba::TERM_PASSES.iter().map(|(n, _)| n.to_string())).chain(polish).collect()
}

/// What the passes of one `simplify` call share.
pub struct Env<'a> {
    pub cli: &'a Cli,
    /// The egglog program of the numeric type.
    pub egg: String,
    /// The input of `simplify`.
    pub input: String,
    /// Where the main candidate came from, for `stats` (`final/ORIGIN`).
    pub origin: RefCell<String>,
}

impl<'a> Env<'a> {
    pub fn new(cli: &'a Cli, egg: String, input: &str) -> Env<'a> {
        Env { cli, egg, input: input.to_string(), origin: RefCell::new("input".into()) }
    }
}

fn dedup(set: Vec<String>) -> Vec<String> {
    let mut out: Vec<String> = Vec::with_capacity(set.len());
    for s in set {
        if !out.contains(&s) {
            out.push(s);
        }
    }
    out
}

/// The candidates `p` gives for `set`.
pub fn run(p: &Pipe, set: Vec<String>, env: &Env) -> Result<Vec<String>, Error> {
    crate::sched::apply(&env.cli.passes);
    go(p, set, env)
}

fn go(p: &Pipe, set: Vec<String>, env: &Env) -> Result<Vec<String>, Error> {
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
            out.sort_by_cached_key(|s| size(&parse(s)));
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
            for _ in 0..*n {
                let out = go(p, set.clone(), env)?;
                let same = out.first() == set.first();
                set = out;
                if same {
                    break;
                }
            }
            Ok(set)
        }
        Pipe::Off(names, p) => crate::sched::with_off(names, || go(p, set, env)),
    }
}

fn pass(name: &str, set: Vec<String>, env: &Env) -> Result<Vec<String>, Error> {
    let cli = env.cli;
    let w = width_of(&cli.num_type);
    let Some(main) = set.first().cloned() else { return Ok(set) };
    let out = match name {
        "id" => set,
        "drive" => {
            let (seed, origin) = crate::drive(&env.egg, &main, cli, cli.max_restarts.max(1), cli.passes.extra)?;
            *env.origin.borrow_mut() = origin;
            vec![seed]
        }
        "printed" => vec![crate::printed(&env.egg, &env.input, main, cli, &env.origin)?],
        "prepass" => {
            let (alt, other) = linear_mba::simplify_linear_with(&main, w, cli.trace, &cli.passes);
            std::iter::once(alt).chain(other).collect()
        }
        "egglog" => {
            let roots: Vec<&str> = set.iter().map(String::as_str).collect();
            vec![crate::egglog_round(&env.egg, &roots, cli)?]
        }
        "polish" => set.into_iter().map(|s| match linear_mba::polish_with(&s, w, &cli.passes) {
            (p, used) if !used.is_empty() => p,
            _ => s,
        }).collect(),
        _ => {
            let f = linear_mba::term_pass(name).unwrap_or_else(|| panic!("unknown pass {name}"));
            if crate::sched::is_off(name) {
                return Ok(set);
            }
            stats::time(&format!("pipe/{name}"), || {
                let ctx = linear_mba::Ctx::new(w);
                set.into_iter()
                    .map(|s| {
                        let t = parse(&s);
                        match f(&t, &ctx) {
                            Some(r) if r != t => show(&r),
                            _ => s,
                        }
                    })
                    .collect()
            })
        }
    };
    Ok(dedup(out))
}
