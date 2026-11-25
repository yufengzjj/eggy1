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

/// Passes inside a rebuild that `off` can turn off: one in a chain then returns its input,
/// one of several alternatives gives no form.
pub const INNER: [&str; 34] = [
    "lowbits",
    "unshift",
    "tfunc_whole",
    "relate",
    "tfunc",
    "unify_operands",
    "recombine",
    "cut_products",
    "shifted_xor",
    "simplify_rebuilt",
    "cluster_regions",
    "simba",
    "small_blocks",
    "wide_blocks",
    "poly_mba",
    "poly/masked",
    "rebuild_values",
    "common_multiple",
    "related_leaves",
    "one_wide_term",
    "semi_linear",
    "drop_unused",
    "clustered",
    "peel",
    "peel_clustered",
    "semi/grouped",
    "semi/peel_grouped",
    "semi/shapes",
    "semi/pairs",
    "semi/peel_shapes",
    "semi/semi_split",
    "semi/scaled",
    "semi/bit_split",
    "semi/short_consts",
];

macro_rules! limits {
    ($($(#[doc = $doc:literal])* $id:ident $name:literal = $default:expr;)*) => {
        /// Numeric limits of the passes inside a rebuild; `--passes` sets them as `NAME=value`.
        #[derive(Clone, Copy, Debug, PartialEq)]
        pub enum Limit {
            $($(#[doc = $doc])* $id,)*
        }
        /// Names and defaults of the `Limit`s, in order.
        pub const LIMITS: &[(&str, usize)] = &[$(($name, $default),)*];
    };
}

limits! {
    /// `relate` in the rebuild without `clustered` only on regions of at most this many
    /// leaves; wider ones take seconds there.
    UnclusteredRelateLeaves "unclustered_relate_leaves" = 10;
    /// Most `rewrite` calls the rebuild without `clustered` makes; past them it is dropped.
    UnclusteredRewrites "unclustered_rewrites" = 256;
    /// Most `rewrite` calls of the other rebuilds after which the one without `clustered`
    /// is still tried: inputs that need more are slow to rebuild without it.
    UnclusteredAfter "unclustered_after" = 1024;
    /// Most `rewrite` calls the rebuild of the input with unified operands makes; past them
    /// it is dropped.
    UnifiedRewrites "unified_rewrites" = 128;
    /// Most combinations `related_leaves` rebuilds.
    RelatedRebuilds "related_rebuilds" = 8;
    /// Most arithmetic leaves `relate_region` tries.
    Related "related" = 4;
    /// Most leaf splits `bit_split` rebuilds per region.
    BitSplits "bit_splits" = 4;
    /// Most `P op Q` pairs `bit_split` rebuilds per `simplify_linear` call.
    BitSplitBudget "bit_split_budget" = 8;
    /// Most variable bits `split_bits` tries on one term.
    Splits "splits" = 4;
    /// How deep `split_bits` nests.
    SplitDepth "split_depth" = 2;
    /// Most rebuilds one `split_bits` call runs.
    SplitRuns "split_runs" = 16;
    /// Largest first rebuild `split_bits` runs on.
    SplitSize "split_size" = 64;
    /// Most leaves `small_blocks` handles.
    BlockLeaves "block_leaves" = 12;
    /// Most combinations of block choices `small_blocks` tries exhaustively, and steps of
    /// the `wide_blocks` search.
    BlockCombos "block_combos" = 1 << 15;
    /// Most `clustered` calls nested inside each other.
    ClusterDepth "cluster_depth" = 2;
    /// Most products `poly_mba` builds with every choice before it keeps to the first.
    PolyBuilds "poly_builds" = 512;
    /// Expansions with more monomials than this keep to the first choice at each level
    /// from the start, as after `poly_builds` products.
    PolyBranchMonos "poly_branch_monos" = 128;
    /// Uncached `rewrite` calls one `polish` call may make.
    PolishRewrites "polish_rewrites" = 2000;
}

thread_local! {
    /// Bits of the `INNER` passes turned off for the run on this thread.
    static OFF: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The limits of the run on this thread, if not the defaults.
    static LIMIT: std::cell::RefCell<Option<Vec<usize>>> = const { std::cell::RefCell::new(None) };
    /// Bits of the `INNER` passes an enclosing `Pipe::Off` turns off.
    static SCOPED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn off_bits(names: &[&str]) -> u64 {
    names.iter().filter_map(|n| INNER.iter().position(|k| k == n)).fold(0u64, |b, i| b | 1 << i)
}

/// Sets the `INNER` passes `p.off` (and an enclosing `Pipe::Off`) turns off and the limits
/// of `p` for the runs on this thread that follow.
pub fn apply(p: &Passes) {
    let bits = off_bits(&p.off) | SCOPED.with(|s| s.get());
    OFF.with(|o| o.set(bits));
    let custom = p.limits.iter().zip(LIMITS).any(|(v, (_, d))| v != d);
    LIMIT.with(|l| *l.borrow_mut() = custom.then(|| p.limits.clone()));
}

/// The value of `l` on this thread.
pub fn limit(l: Limit) -> usize {
    LIMIT.with(|v| v.borrow().as_ref().map_or(LIMITS[l as usize].1, |v| v[l as usize]))
}

/// `f()` with the `INNER` passes `names` also turned off.
pub fn with_off<R>(names: &[&str], f: impl FnOnce() -> R) -> R {
    let bits = off_bits(names);
    let (scoped, off) = (SCOPED.with(|s| s.replace(s.get() | bits)), OFF.with(|o| o.replace(o.get() | bits)));
    let r = f();
    SCOPED.with(|s| s.set(scoped));
    OFF.with(|o| o.set(off));
    r
}

/// A pass pipeline: every pass maps a list of equivalent candidate terms (the first is the
/// main one) to another, so any pass can follow any other. Written `name` or
/// `combinator(arguments)`, e.g. `seq(lowbits,rewrite,egglog,polish)`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pipe {
    /// A pass by name (`crate::pipe::names`).
    Pass(String),
    /// Each in turn on the candidates of the one before (`seq(a,b,...)`).
    Seq(Vec<Pipe>),
    /// All on the same candidates; their candidates in order, repeats dropped
    /// (`union(a,b,...)`).
    Union(Vec<Pipe>),
    /// All on the same candidates; the `k` smallest of their candidates, the earlier of
    /// equal ones first (`best(k,a,b,...)`).
    Best(usize, Vec<Pipe>),
    /// The candidates of the first whose candidates differ from its input's, else the
    /// input (`first(a,b,...)`).
    First(Vec<Pipe>),
    /// Repeated at most `n` times while the main candidate changes (`fix(n,p)`).
    Fix(usize, Box<Pipe>),
    /// With the `INNER` passes named also turned off (`off(relate+tfunc,p)`).
    Off(Vec<&'static str>, Box<Pipe>),
}

impl Pipe {
    pub fn parse(s: &str) -> Result<Pipe, String> {
        let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
        let (p, rest) = Pipe::parse_at(&s)?;
        if !rest.is_empty() {
            return Err(format!("unexpected {rest} in pipeline {s}"));
        }
        Ok(p)
    }

    fn parse_at(s: &str) -> Result<(Pipe, &str), String> {
        let end = s.find(['(', ',', ')']).unwrap_or(s.len());
        let (name, rest) = s.split_at(end);
        if name.is_empty() {
            return Err(format!("expected a pass or combinator at {s}"));
        }
        let Some(mut rest) = rest.strip_prefix('(') else {
            if !crate::pipe::names().iter().any(|n| n == name) {
                return Err(format!("unknown pass {name}; known: {}", crate::pipe::names().join(" ")));
            }
            return Ok((Pipe::Pass(name.to_string()), rest));
        };
        let mut args = Vec::new();
        let mut first = None;
        if matches!(name, "best" | "fix" | "off") {
            let end = rest.find(',').ok_or_else(|| format!("{name} needs a first argument and a pipeline: {s}"))?;
            first = Some(&rest[..end]);
            rest = &rest[end + 1..];
        }
        loop {
            let (p, r) = Pipe::parse_at(rest)?;
            args.push(p);
            match r.chars().next() {
                Some(',') => rest = &r[1..],
                Some(')') => {
                    rest = &r[1..];
                    break;
                }
                _ => return Err(format!("expected , or ) after an argument of {name}: {s}")),
            }
        }
        let num = || first.unwrap().parse::<usize>().map_err(|_| format!("expected a number: {name}({}", first.unwrap()));
        let one = |args: Vec<Pipe>| if args.len() == 1 { Ok(Box::new(args.into_iter().next().unwrap())) } else { Err(format!("{name} takes one pipeline: {s}")) };
        let p = match name {
            "seq" => Pipe::Seq(args),
            "union" => Pipe::Union(args),
            "first" => Pipe::First(args),
            "best" => Pipe::Best(num()?, args),
            "fix" => Pipe::Fix(num()?, one(args)?),
            "off" => {
                let names = first.unwrap().split('+').map(|n| INNER.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown off name {n}; known: {}", INNER.join(",")))).collect::<Result<_, _>>()?;
                Pipe::Off(names, one(args)?)
            }
            _ => return Err(format!("unknown combinator {name}; known: seq union best first fix off")),
        };
        Ok((p, rest))
    }
}

impl fmt::Display for Pipe {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let list = |f: &mut fmt::Formatter, name: &str, head: Option<String>, ps: &[Pipe]| {
            let args: Vec<String> = head.into_iter().chain(ps.iter().map(|p| p.to_string())).collect();
            write!(f, "{name}({})", args.join(","))
        };
        match self {
            Pipe::Pass(n) => write!(f, "{n}"),
            Pipe::Seq(ps) => list(f, "seq", None, ps),
            Pipe::Union(ps) => list(f, "union", None, ps),
            Pipe::First(ps) => list(f, "first", None, ps),
            Pipe::Best(k, ps) => list(f, "best", Some(k.to_string()), ps),
            Pipe::Fix(n, p) => list(f, "fix", Some(n.to_string()), std::slice::from_ref(p)),
            Pipe::Off(ns, p) => list(f, "off", Some(ns.join("+")), std::slice::from_ref(p)),
        }
    }
}

/// The pipeline of `simplify`: the restart rounds with the pre-pass and polish, then the
/// run from the printed result.
pub const PIPELINE: &str = "seq(drive,printed)";

/// `INNER` passes that `set_gates` turns off for inputs where paired runs without them
/// lost nothing.
pub const GATES: [&str; 3] = ["poly_mba", "lowbits", "small_blocks"];

/// Also turns off, for the runs on this thread that follow, the passes of `p.gates` that
/// inputs like `s` do not need: `poly_mba` without products of non-constant factors,
/// `lowbits` without those, shifts and bitwise operations with a constant operand, and
/// `small_blocks` with more than 3 products and no shift.
pub fn set_gates(p: &Passes, s: &crate::stats::Shape) {
    let skip = |n: &str| match n {
        "poly_mba" => s.mul == 0,
        "lowbits" => s.mul == 0 && s.shift == 0 && s.bitconst == 0,
        "small_blocks" => s.mul > 3 && s.shift == 0,
        _ => false,
    };
    let bits = p.gates.iter().filter(|n| skip(n)).filter_map(|n| INNER.iter().position(|k| k == n)).fold(0u64, |b, i| b | 1 << i);
    OFF.with(|o| o.set(o.get() | bits));
}

/// Whether the pass `name` is turned off on this thread.
pub fn is_off(name: &str) -> bool {
    let bits = OFF.with(|o| o.get());
    bits != 0 && INNER.iter().position(|k| *k == name).is_some_and(|i| bits >> i & 1 == 1)
}

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
    /// Entries of `INNER` turned off.
    pub off: Vec<&'static str>,
    /// Entries of `GATES` turned off for inputs that do not need them (`set_gates`).
    pub gates: Vec<&'static str>,
    /// Values of the `LIMITS`, in order.
    pub limits: Vec<usize>,
    /// The passes `simplify` runs on its input (`PIPELINE`).
    pub pipeline: Pipe,
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
            off: vec!["semi/peel_shapes"],
            gates: GATES.to_vec(),
            limits: LIMITS.iter().map(|(_, d)| *d).collect(),
            pipeline: Pipe::parse(PIPELINE).unwrap(),
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
    /// `key-=names` (also `off` and `gates`; names separated by `,`; schedule steps written `run:`, `once:` or
    /// `sat:` and a ruleset). The `LIMITS` are keys too (`split_runs=8`), and `pipeline`
    /// takes a `Pipe` (spaces inside its parentheses allowed).
    pub fn parse(spec: &str) -> Result<Passes, String> {
        let mut p = Passes::default();
        let mut items = Vec::new();
        let (mut depth, mut start) = (0i32, 0);
        for (i, c) in spec.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                ' ' | ';' if depth == 0 => {
                    items.push(&spec[start..i]);
                    start = i + 1;
                }
                _ => {}
            }
        }
        items.push(&spec[start..]);
        for item in items.into_iter().filter(|s| !s.is_empty()) {
            if let Some(val) = item.strip_prefix("pipeline=") {
                p.pipeline = Pipe::parse(val)?;
                continue;
            }
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
                "off" => Some((&mut p.off, names(&INNER)?)),
                "gates" => Some((&mut p.gates, names(&GATES)?)),
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
                _ => match LIMITS.iter().position(|(n, _)| *n == key) {
                    Some(i) => p.limits[i] = num()?,
                    None => {
                        let limits: Vec<&str> = LIMITS.iter().map(|(n, _)| *n).collect();
                        return Err(format!("unknown key {key}; known: schedule match_limit ban_length pre keep extra rerun_input printed minimal polish polish_wins off gates {}", limits.join(" ")));
                    }
                },
            }
        }
        p.pre.sort_by_key(|n| PRE.iter().position(|k| k == n));
        p.pre.dedup();
        p.off.sort_by_key(|n| INNER.iter().position(|k| k == n));
        p.off.dedup();
        p.gates.sort_by_key(|n| GATES.iter().position(|k| k == n));
        p.gates.dedup();
        Ok(p)
    }
}

/// The spec `Passes::parse` reads back to these passes.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(
            f,
            "schedule={} match_limit={} ban_length={} pre={} keep={} extra={} rerun_input={} printed={} minimal={} polish={} polish_wins={} off={} gates={}",
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
            self.polish_wins,
            self.off.join(","),
            self.gates.join(",")
        )?;
        for ((name, default), v) in LIMITS.iter().zip(&self.limits) {
            if v != default {
                write!(f, " {name}={v}")?;
            }
        }
        write!(f, " pipeline={}", self.pipeline)
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
        let p = Passes::parse("off=semi/bit_split,relate").unwrap();
        assert_eq!(p.off, ["relate", "semi/bit_split"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        apply(&p);
        assert!(is_off("relate") && !is_off("simba"));
        apply(&Passes::default());
        assert!(!is_off("relate"));
        let p = Passes::parse("gates-=lowbits").unwrap();
        assert_eq!(p.gates, ["poly_mba", "small_blocks"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        set_gates(&p, &crate::stats::Shape::default());
        assert!(is_off("poly_mba") && !is_off("lowbits") && !is_off("small_blocks"));
        apply(&p);
        let p = Passes::parse("schedule-=sat:analysis schedule+=once:simplify,sat:analysis match_limit=128").unwrap();
        assert_eq!(p.schedule.last(), Some(&(Step::Saturate, "analysis")));
        assert_eq!(p.schedule.len(), 7);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("schedule=run:nope").is_err() && Passes::parse("schedule=go:simplify").is_err());
        let p = Passes::parse("split_runs=4 poly_builds=64").unwrap();
        assert!(p.to_string().contains(" split_runs=4 poly_builds=64 "));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("split_runs+=1").is_err() && Passes::parse("split_runs=x").is_err());
        assert_eq!(limit(Limit::SplitRuns), 16);
        apply(&p);
        assert_eq!((limit(Limit::SplitRuns), limit(Limit::PolyBuilds), limit(Limit::SplitDepth)), (4, 64, 2));
        apply(&Passes::default());
        assert_eq!(limit(Limit::SplitRuns), 16);
        let p = Passes::parse("keep=1 pipeline=seq(lowbits, best(2, rewrite, off(relate+tfunc, rebuild)), fix(3, egglog), polish/factor) extra=0").unwrap();
        assert_eq!(p.pipeline.to_string(), "seq(lowbits,best(2,rewrite,off(relate+tfunc,rebuild)),fix(3,egglog),polish/factor)");
        assert_eq!((p.keep, p.extra), (1, 0));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["pipeline=nope", "pipeline=seq(rewrite", "pipeline=best(x,rewrite)", "pipeline=fix(2,a,b)", "pipeline=off(nope,rewrite)", "pipeline=loop(rewrite)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        with_off(&["relate"], || {
            apply(&Passes::default());
            assert!(is_off("relate"));
        });
        apply(&Passes::default());
        assert!(!is_off("relate"));
    }
}
