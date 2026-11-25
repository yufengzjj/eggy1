//! The pass pipeline of `simplify`: the egglog schedule of a round, which pre-pass candidates
//! are built, how the rounds run and which polish passes run in what order. `Passes::default()` is the tuned pipeline;
//! `--passes` changes it with a spec such as `pre-=halve_input polish=push_not,factor extra=0`.

use std::fmt;

/// Pre-pass candidates built beside the first rebuild, in the order they are computed.
pub const PRE: [&str; 9] = [
    "unified",
    "no_wide",
    "split_bits",
    "halve_first",
    "over_products",
    "over_const_bitwise",
    "over_shared_bitwise",
    "halve_input",
    "unclustered",
];

/// The rulesets of `make_egg`.
pub const RULESETS: [&str; 6] = ["default-ruleset", "canonicalization", "constant-folding", "analysis", "identity-zero-element", "simplify"];

/// How one step of a round's egglog schedule runs its ruleset.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Step {
    /// Once, with the back-off scheduler (`run:` in a spec).
    Run,
    /// Once, matching everything (`once:`).
    Once,
    /// Until nothing changes (`sat:`).
    Saturate,
}

const STEPS: [(Step, &str); 3] = [(Step::Run, "run"), (Step::Once, "once"), (Step::Saturate, "sat")];

#[derive(Clone, Debug, PartialEq)]
pub struct Passes {
    /// The steps each of a round's `iter_limit` repetitions runs, in order.
    pub schedule: Vec<(Step, &'static str)>,
    /// Back-off scheduler: matches a rule may make per run before it is banned.
    pub match_limit: usize,
    /// Back-off scheduler: runs a banned rule sits out at first.
    pub ban_length: usize,
    /// Enabled entries of `PRE`.
    pub pre: Vec<&'static str>,
    /// Pre-pass rebuilds unioned into a round, smallest first (`unclustered` comes on top).
    pub keep: usize,
    /// Rounds added after the last one while the pre-pass still changes its extraction.
    pub extra: usize,
    /// Rerun the first round with the input when its result still mixes arithmetic into
    /// bitwise operations.
    pub rerun_input: bool,
    /// Rounds of the second run from the printed result (0: none).
    pub printed: usize,
    /// Take a rebuild proved minimal as the extraction without saturating.
    pub minimal: bool,
    /// Polish passes in order (names from `linear_mba::POLISH`); repeats allowed.
    pub polish: Vec<&'static str>,
    /// Polish stops after this many winning passes.
    pub polish_wins: usize,
}

impl Default for Passes {
    fn default() -> Passes {
        use Step::*;
        Passes {
            schedule: vec![
                (Run, "default-ruleset"),
                (Run, "canonicalization"),
                (Saturate, "constant-folding"),
                (Saturate, "analysis"),
                (Saturate, "identity-zero-element"),
                (Run, "simplify"),
            ],
            match_limit: 64,
            ban_length: 3,
            pre: PRE.to_vec(),
            keep: 2,
            extra: 2,
            rerun_input: true,
            printed: 2,
            minimal: true,
            polish: crate::linear_mba::POLISH.iter().map(|(n, _)| *n).collect(),
            polish_wins: 8,
        }
    }
}

impl Passes {
    /// Whether the pre-pass candidate `name` (an entry of `PRE`) is built.
    pub fn pre_on(&self, name: &str) -> bool {
        debug_assert!(PRE.contains(&name), "unknown pre-pass candidate {name}");
        self.pre.contains(&name)
    }

    /// The `run-schedule` command of a round with `iter` repetitions.
    pub fn egglog_schedule(&self, iter: usize) -> String {
        let steps: String = self
            .schedule
            .iter()
            .map(|(step, rs)| match step {
                Step::Run => format!("\n            (run-with babibo {rs})"),
                Step::Once => format!("\n            (run {rs})"),
                Step::Saturate => format!("\n            (saturate (run {rs}))"),
            })
            .collect();
        format!(
            "(run-schedule\n    (let-scheduler babibo (back-off :match-limit {} :ban-length {}))\n    (repeat {iter}\n        (seq{steps}\n        )\n    )\n)",
            self.match_limit, self.ban_length
        )
    }

    /// The default pipeline changed by `spec`: items separated by spaces or `;`, each
    /// `key=value`, and for the lists `pre`, `polish` and `schedule` also `key+=names` and
    /// `key-=names` (names separated by `,`; schedule steps written `run:`, `once:` or
    /// `sat:` and a ruleset).
    pub fn parse(spec: &str) -> Result<Passes, String> {
        let mut p = Passes::default();
        for item in spec.split([' ', ';']).filter(|s| !s.is_empty()) {
            let (key, op, val) = ["+=", "-=", "="]
                .iter()
                .find_map(|op| item.split_once(op).map(|(k, v)| (k, *op, v)))
                .ok_or_else(|| format!("expected key=value: {item}"))?;
            let names = |known: &[&'static str]| -> Result<Vec<&'static str>, String> {
                val.split(',').filter(|s| !s.is_empty()).map(|n| known.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown {key} name {n}; known: {}", known.join(",")))).collect()
            };
            let polish_names: Vec<&'static str> = crate::linear_mba::POLISH.iter().map(|(n, _)| *n).collect();
            let list = match key {
                "pre" => Some((&mut p.pre, names(&PRE)?)),
                "polish" => Some((&mut p.polish, names(&polish_names)?)),
                _ => None,
            };
            if let Some((list, ns)) = list {
                match op {
                    "=" => *list = ns,
                    "+=" => list.extend(ns),
                    _ => list.retain(|n| !ns.contains(n)),
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
            let num = || val.parse::<usize>().map_err(|_| format!("expected a number: {item}"));
            let flag = || match val {
                "1" | "true" | "on" => Ok(true),
                "0" | "false" | "off" => Ok(false),
                _ => Err(format!("expected 0 or 1: {item}")),
            };
            match key {
                "keep" => p.keep = num()?.max(1),
                "extra" => p.extra = num()?,
                "rerun_input" => p.rerun_input = flag()?,
                "printed" => p.printed = num()?,
                "minimal" => p.minimal = flag()?,
                "polish_wins" => p.polish_wins = num()?,
                "match_limit" => p.match_limit = num()?,
                "ban_length" => p.ban_length = num()?,
                _ => return Err(format!("unknown key {key}; known: schedule match_limit ban_length pre keep extra rerun_input printed minimal polish polish_wins")),
            }
        }
        p.pre.sort_by_key(|n| PRE.iter().position(|k| k == n));
        p.pre.dedup();
        Ok(p)
    }
}

/// The spec `Passes::parse` reads back to these passes.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(
            f,
            "schedule={} match_limit={} ban_length={} pre={} keep={} extra={} rerun_input={} printed={} minimal={} polish={} polish_wins={}",
            steps.join(","),
            self.match_limit,
            self.ban_length,
            self.pre.join(","),
            self.keep,
            self.extra,
            self.rerun_input as u8,
            self.printed,
            self.minimal as u8,
            self.polish.join(","),
            self.polish_wins
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spec_round_trip() {
        assert_eq!(Passes::parse("").unwrap(), Passes::default());
        let p = Passes::parse("pre-=halve_input,unified;polish=factor,push_not,factor extra=0 keep=3 minimal=off").unwrap();
        assert!(!p.pre_on("unified") && p.pre_on("no_wide"));
        assert_eq!(p.polish, ["factor", "push_not", "factor"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("pre+=nope").is_err() && Passes::parse("keep+=1").is_err());
        let p = Passes::parse("schedule-=sat:analysis schedule+=once:simplify,sat:analysis match_limit=128").unwrap();
        assert_eq!(p.schedule.last(), Some(&(Step::Saturate, "analysis")));
        assert_eq!(p.schedule.len(), 7);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("schedule=run:nope").is_err() && Passes::parse("schedule=go:simplify").is_err());
    }
}
