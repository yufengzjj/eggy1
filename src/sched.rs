//! The pass pipeline of `simplify`: which pre-pass candidates are built, how the rounds run
//! and which polish passes run in what order. `Passes::default()` is the tuned pipeline;
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

#[derive(Clone, Debug, PartialEq)]
pub struct Passes {
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
        Passes {
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

    /// The default pipeline changed by `spec`: items separated by spaces or `;`, each
    /// `key=value`, and for the lists `pre` and `polish` also `key+=names` and `key-=names`
    /// (names separated by `,`).
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
                _ => return Err(format!("unknown key {key}; known: pre polish keep extra rerun_input printed minimal polish_wins")),
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
        write!(
            f,
            "pre={} keep={} extra={} rerun_input={} printed={} minimal={} polish={} polish_wins={}",
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
    }
}
