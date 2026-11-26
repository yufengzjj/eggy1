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
    /// Most `P op Q` pairs `bit_split` rebuilds per pre-pass candidate (`Pipe::Cand`).
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
    /// Bits of the `INNER` passes asked whether they are off, since the last `swap_touched`.
    static TOUCHED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The passes of the run on this thread (`apply`), the default ones until set.
    static CURRENT: std::cell::RefCell<Option<std::rc::Rc<Passes>>> = const { std::cell::RefCell::new(None) };
}

/// The passes `apply` last set on this thread.
pub fn current() -> std::rc::Rc<Passes> {
    CURRENT.with(|c| c.borrow_mut().get_or_insert_with(|| std::rc::Rc::new(Passes::default())).clone())
}

/// The `INNER` passes asked whether they are off since the last call, which sets them to `v`.
pub fn swap_touched(v: u64) -> u64 {
    TOUCHED.with(|t| t.replace(v))
}

/// Bits of the `INNER` passes turned off on this thread.
pub fn off_bits_now() -> u64 {
    OFF.with(|o| o.get())
}

/// A hash of the limits on this thread, 0 for the defaults.
pub fn limits_key() -> u64 {
    use std::hash::{Hash, Hasher};
    LIMIT.with(|v| {
        v.borrow().as_ref().map_or(0, |v| {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            v.hash(&mut h);
            h.finish() | 1
        })
    })
}

fn off_bits(names: &[&str]) -> u64 {
    names.iter().filter_map(|n| INNER.iter().position(|k| k == n)).fold(0u64, |b, i| b | 1 << i)
}

/// Sets the `INNER` passes `p.off` (and an enclosing `Pipe::Off`) turns off and the limits
/// of `p` for the runs on this thread that follow.
pub fn apply(p: &Passes) {
    CURRENT.with(|c| {
        let mut c = c.borrow_mut();
        if c.as_deref() != Some(p) {
            *c = Some(std::rc::Rc::new(p.clone()));
        }
    });
    let bits = off_bits(&p.off) | SCOPED.with(|s| s.get());
    OFF.with(|o| o.set(bits));
    let custom = p.limits.iter().zip(LIMITS).any(|(v, (_, d))| v != d);
    LIMIT.with(|l| *l.borrow_mut() = custom.then(|| p.limits.clone()));
}

/// The value of `l` on this thread.
pub fn limit(l: Limit) -> usize {
    LIMIT.with(|v| v.borrow().as_ref().map_or(LIMITS[l as usize].1, |v| v[l as usize]))
}

/// The value on this thread of the limit named `name`.
pub fn limit_named(name: &str) -> Option<usize> {
    let i = LIMITS.iter().position(|(n, _)| *n == name)?;
    Some(LIMIT.with(|v| v.borrow().as_ref().map_or(LIMITS[i].1, |v| v[i])))
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
    /// A pass by name (`crate::pipe::is_pass`).
    Pass(String),
    /// Each in turn on the candidates of the one before (`seq(a,b,...)`).
    Seq(Vec<Pipe>),
    /// All on the same candidates; their candidates in order, repeats dropped
    /// (`union(a,b,...)`).
    Union(Vec<Pipe>),
    /// All on the same candidates; the `k` smallest of their candidates, the earlier of
    /// equal ones first (`best(k,a,b,...)`; `k` as in `Fix`).
    Best(String, Vec<Pipe>),
    /// The candidates of the first whose candidates differ from its input's, else the
    /// input (`first(a,b,...)`).
    First(Vec<Pipe>),
    /// Repeated at most `n` times while the main candidate changes (`fix(n,p)`); `n` is a
    /// number or a name of `crate::pipe::COUNTS` (`fix(restarts,p)`).
    Fix(String, Box<Pipe>),
    /// With the `INNER` passes named also turned off (`off(relate+tfunc,p)`).
    Off(Vec<&'static str>, Box<Pipe>),
    /// `a` where the condition holds for the candidates, else `b` (`if(c,a,b)`, `if(c,a)`
    /// with `b` = `id`).
    If(Cond, Box<Pipe>, Box<Pipe>),
    /// `a`, and where the condition holds for its candidates, `b` on the same input taken
    /// instead when its main candidate is no larger (`retry(c,a,b)`).
    Retry(Cond, Box<Pipe>, Box<Pipe>),
    /// The candidates of `p`, unless a pass inside gave a strictly smaller candidate than
    /// their main one: then the first smallest (`smallest(p)`).
    Smallest(Box<Pipe>),
    /// `p` timed as `NAME/run`; a main candidate it changed is counted in `NAME/won/ORIGIN`
    /// and gets origin `NAME` (`tag(NAME,p)`).
    Tag(String, Box<Pipe>),
    /// The candidates the condition holds for, each taken alone (`filter(c)`).
    Filter(Cond),
    /// The pre-pass candidate `NAME`: `p` with its own `bit_split_budget`, timed as
    /// `pre/NAME/made`, its candidates with origin `NAME`; none when `NAME` is an entry of
    /// `PRE` turned off (`cand(NAME,p)`).
    Cand(String, Box<Pipe>),
    /// `p` with run settings of the enclosing `scope` changed, each restored after
    /// (`with(rewrites=128+semi_leaves=2,p)`; values are numbers or `LIMITS` names;
    /// `crate::linear_mba::Ctx::setting`).
    With(Vec<(String, String)>, Box<Pipe>),
    /// `p` with its passes over one term sharing one run: memos, budgets, settings
    /// (`scope(p)`).
    Scope(Box<Pipe>),
    /// `p`, taken only when its main candidate is smaller than the input's; timed as
    /// `NAME/run`, counted in `NAME/won` and `NAME/gain` when taken, which gives the main
    /// candidate origin `NAME` (`smaller(NAME,p)`).
    Smaller(String, Box<Pipe>),
    /// `p` repeated while the `smaller` inside take a result, until they have taken `n`
    /// (`wins(n,p)`; `n` as in `Fix`).
    Wins(String, Box<Pipe>),
    /// Each candidate that is a linear region rebuilt by the first candidate of `p`, with the
    /// atom leaves of that form rewritten by `Passes::rewrite`; otherwise, or when `p` gives
    /// none, its operands rewritten (`regions(p)`).
    Regions(Box<Pipe>),
    /// `p`, then `Passes::rewrite` again on its main candidate, kept when smaller, where it
    /// changed a term with an arithmetic leaf of a bitwise operation (`again(p)`).
    Again(Box<Pipe>),
}

/// A condition on candidates: alternatives separated by `|`, each names of
/// `crate::pipe::CONDS` (or `lt:R`, `gt:R`, `eq:R`, `le:P/Q:R` against register `R`) that
/// must all hold, joined by `+`, each negated by a leading `!` (`mixed+!minimal|tiny`).
#[derive(Clone, Debug, PartialEq)]
pub struct Cond(pub Vec<Vec<(bool, String)>>);

impl Cond {
    fn parse(s: &str) -> Result<Cond, String> {
        let term = |t: &str| {
            let (neg, n) = match t.strip_prefix('!') {
                Some(n) => (true, n),
                None => (false, t),
            };
            match crate::pipe::is_cond(n) {
                true => Ok((neg, n.to_string())),
                false => Err(format!("unknown condition {n}; known: {} lt:R gt:R eq:R le:P/Q:R", crate::pipe::CONDS.join(" "))),
            }
        };
        Ok(Cond(s.split('|').map(|a| a.split('+').map(term).collect::<Result<_, _>>()).collect::<Result<_, _>>()?))
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let alt = |a: &Vec<(bool, String)>| a.iter().map(|(neg, n)| format!("{}{n}", if *neg { "!" } else { "" })).collect::<Vec<_>>().join("+");
        write!(f, "{}", self.0.iter().map(alt).collect::<Vec<_>>().join("|"))
    }
}

fn count_ok(c: &str) -> Result<String, String> {
    match c.parse::<usize>().is_ok() || crate::pipe::COUNTS.contains(&c) {
        true => Ok(c.to_string()),
        false => Err(format!("expected a number or one of {}: {c}", crate::pipe::COUNTS.join(" "))),
    }
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
            if !crate::pipe::is_pass(name) {
                return Err(format!("unknown pass {name}; known: {}", crate::pipe::names().join(" ")));
            }
            return Ok((Pipe::Pass(name.to_string()), rest));
        };
        if name == "filter" {
            let end = rest.find(')').ok_or_else(|| format!("expected ) after filter: {s}"))?;
            return Ok((Pipe::Filter(Cond::parse(&rest[..end])?), &rest[end + 1..]));
        }
        let mut args = Vec::new();
        let mut first = "";
        if matches!(name, "best" | "fix" | "off" | "if" | "retry" | "tag" | "cand" | "with" | "smaller" | "wins") {
            let end = rest.find(',').ok_or_else(|| format!("{name} needs a first argument and a pipeline: {s}"))?;
            first = &rest[..end];
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
        let n = args.len();
        let mut args = args.into_iter();
        let p = match (name, n) {
            ("seq", _) => Pipe::Seq(args.collect()),
            ("union", _) => Pipe::Union(args.collect()),
            ("first", _) => Pipe::First(args.collect()),
            ("best", _) => Pipe::Best(count_ok(first)?, args.collect()),
            ("fix", 1) => Pipe::Fix(count_ok(first)?, Box::new(args.next().unwrap())),
            ("off", 1) => {
                let names = first.split('+').map(|n| INNER.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown off name {n}; known: {}", INNER.join(",")))).collect::<Result<_, _>>()?;
                Pipe::Off(names, Box::new(args.next().unwrap()))
            }
            ("if", 1 | 2) => {
                let c = Cond::parse(first)?;
                let a = Box::new(args.next().unwrap());
                Pipe::If(c, a, Box::new(args.next().unwrap_or(Pipe::Pass("id".into()))))
            }
            ("retry", 2) => {
                let c = Cond::parse(first)?;
                let a = Box::new(args.next().unwrap());
                Pipe::Retry(c, a, Box::new(args.next().unwrap()))
            }
            ("smallest", 1) => Pipe::Smallest(Box::new(args.next().unwrap())),
            ("scope", 1) => Pipe::Scope(Box::new(args.next().unwrap())),
            ("regions", 1) => Pipe::Regions(Box::new(args.next().unwrap())),
            ("again", 1) => Pipe::Again(Box::new(args.next().unwrap())),
            ("tag", 1) => Pipe::Tag(first.to_string(), Box::new(args.next().unwrap())),
            ("cand", 1) => Pipe::Cand(first.to_string(), Box::new(args.next().unwrap())),
            ("smaller", 1) => Pipe::Smaller(first.to_string(), Box::new(args.next().unwrap())),
            ("wins", 1) => Pipe::Wins(count_ok(first)?, Box::new(args.next().unwrap())),
            ("with", 1) => {
                let set = first.split('+').map(|kv| {
                    let (k, v) = kv.split_once('=').ok_or_else(|| format!("expected KEY=VALUE in with: {kv}"))?;
                    let known = ["rewrites", "semi_leaves", "relate_leaves", "bit_splits"];
                    if !known.contains(&k) {
                        return Err(format!("unknown setting {k}; known: {}", known.join(" ")));
                    }
                    if !(v.parse::<usize>().is_ok() || LIMITS.iter().any(|(n, _)| *n == v)) {
                        return Err(format!("bad value {v} for {k}"));
                    }
                    Ok((k.to_string(), v.to_string()))
                });
                Pipe::With(set.collect::<Result<_, _>>()?, Box::new(args.next().unwrap()))
            }
            ("fix" | "off" | "smallest" | "scope" | "tag" | "cand" | "with" | "smaller" | "wins" | "regions" | "again", _) => return Err(format!("{name} takes one pipeline: {s}")),
            ("if" | "retry", _) => return Err(format!("{name} takes a condition and two pipelines: {s}")),
            _ => return Err(format!("unknown combinator {name}; known: seq union best first fix off if retry smallest tag filter cand with scope smaller wins regions again")),
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
        let one = std::slice::from_ref;
        match self {
            Pipe::Pass(n) => write!(f, "{n}"),
            Pipe::Seq(ps) => list(f, "seq", None, ps),
            Pipe::Union(ps) => list(f, "union", None, ps),
            Pipe::First(ps) => list(f, "first", None, ps),
            Pipe::Best(k, ps) => list(f, "best", Some(k.clone()), ps),
            Pipe::Fix(n, p) => list(f, "fix", Some(n.clone()), one(p)),
            Pipe::Off(ns, p) => list(f, "off", Some(ns.join("+")), one(p)),
            Pipe::If(c, a, b) if **b == Pipe::Pass("id".into()) => list(f, "if", Some(c.to_string()), one(a)),
            Pipe::If(c, a, b) => list(f, "if", Some(c.to_string()), &[(**a).clone(), (**b).clone()]),
            Pipe::Retry(c, a, b) => list(f, "retry", Some(c.to_string()), &[(**a).clone(), (**b).clone()]),
            Pipe::Smallest(p) => list(f, "smallest", None, one(p)),
            Pipe::Scope(p) => list(f, "scope", None, one(p)),
            Pipe::Tag(n, p) => list(f, "tag", Some(n.clone()), one(p)),
            Pipe::Cand(n, p) => list(f, "cand", Some(n.clone()), one(p)),
            Pipe::Smaller(n, p) => list(f, "smaller", Some(n.clone()), one(p)),
            Pipe::Wins(n, p) => list(f, "wins", Some(n.clone()), one(p)),
            Pipe::Regions(p) => list(f, "regions", None, one(p)),
            Pipe::Again(p) => list(f, "again", None, one(p)),
            Pipe::Filter(c) => write!(f, "filter({c})"),
            Pipe::With(kv, p) => list(f, "with", Some(kv.iter().map(|(k, v)| format!("{k}={v}")).collect::<Vec<_>>().join("+")), one(p)),
        }
    }
}

/// A later round: the pre-pass rebuilds, then their extraction, or the one proved minimal.
const LATER: &str = "seq(prepass,if(minimal,take_minimal,egglog/later))";

/// The first round. Saturating a large input is most of the run time and rarely beats its
/// rebuild, so the input joins only inputs with shifts, division or mulhi whose rebuild is
/// not tiny (`opaque`), or a rerun when the result still mixes arithmetic or constants
/// into bitwise operations.
const FIRST: &str = "if(opaque,seq(union(id,prepass),if(minimal,take_minimal,egglog/first)),retry(rerun_input+mixed+!minimal,seq(prepass,if(minimal,take_minimal,egglog/first)),seq(union(id,prepass),egglog/rerun_input)))";

/// The pipeline of `simplify`: the restart rounds while the extraction changes, extra ones
/// while the pre-pass still rebuilds it, polish, all keeping the smallest form seen (the
/// extraction prefers fewer non-constant nodes, results are compared by node count); then
/// the same from the printed result, kept when smaller.
pub fn pipeline() -> String {
    format!(
        "seq(smallest(seq(fix(1,{FIRST}),if(moved,fix(restarts,{LATER})),if(moved,fix(extra,if(rebuilds,{LATER}))),polish)),if(printed+!input,tag(rerun_printed,best(1,id,seq(reprint,smallest(seq(fix(1,{FIRST}),if(moved,fix(printed,{LATER})),polish)))))))"
    )
}

/// The rebuild of one term (`Passes::rewrite`, what `linear_mba::rewrite` memoizes): a linear
/// region rebuilt by the smallest of `simba`, `small_blocks` and `wide_blocks`, or else its
/// operands rewritten; `poly_mba` taken instead when strictly smaller.
pub const REWRITE: &str = "again(best(1,regions(best(1,simba,small_blocks,wide_blocks)),poly_mba))";

/// The final polish (`Passes::polish`), on one candidate: the polish passes `names` in
/// turn, each kept when smaller, repeated while one is, until 8 are; on one run whose
/// `rewrite` calls are limited. `join_linear` rewrites every pair of leaf groups many times,
/// and semi-linear groups of many leaves take seconds there.
pub fn polish(names: &[&str]) -> String {
    let step = |n: &&str| {
        let run = format!("seq(polish/{n},drop_identities)");
        let run = if *n == "join_linear" { format!("with(semi_leaves=2,{run})") } else { run };
        format!("smaller(polish/{n},{run})")
    };
    let steps: Vec<String> = names.iter().map(step).collect();
    format!("scope(with(rewrites=polish_rewrites,wins(8,seq({}))))", steps.join(","))
}

/// A rebuild of the main candidate: the whole term replaced by a T-function lookup, or its
/// regions rewritten, clustered, related and its subterms replaced (`~(y - 1)` replaced
/// before the rebuild would become `-y`, a leaf the rebuild no longer relates to `y - 1`).
const REBUILD: &str = "first(tfunc_whole,seq(rewrite_top,cluster_top,relate,tfunc))";
/// `REBUILD` without `relate`.
const REBUILD_PLAIN: &str = "first(tfunc_whole,seq(rewrite_top,cluster_top,tfunc))";

/// The pre-pass (`Passes::prepass`), on one run (`scope`). Registers: `t0` the input, `t`
/// with low bits and shifts rewritten, `r` the first rebuild, `n` the rebuild without
/// `wide_blocks`, `f`/`b` the candidates finished, `u` the rebuild without clusters, `m`
/// the ones kept.
pub fn prepass() -> String {
    let r = REBUILD;
    let rp = REBUILD_PLAIN;
    [
        "scope(seq(save/t0,gates,lowbits,unshift,save/t,",
        &format!("cand(first,{r}),"),
        // Unified operands let the regions around them share leaves, but the rebuild of the
        // input as written is sometimes smaller; dropped once it needs `unified_rewrites` rewrites.
        "best(1,id,cand(unified,seq(load/t,unify_operands,filter(!eq:t),with(rewrites=unified_rewrites,first(tfunc_whole,seq(rewrite,within,cluster_regions,relate,within,tfunc)))))),",
        "save/r,union(id,",
        // A region rebuilt by `wide_blocks` is smaller there, but the other rebuilds can leave
        // subterms the abstracted rebuilds share across terms; a larger one unioned beside the
        // first rebuild made the rules finish worse as often as better.
        &format!("cand(no_wide,if(used_wide,seq(load/t,off(wide_blocks,{r}),save/n,filter(lt:r)),none)),"),
        "cand(no_wide_abstracted,seq(load/n,off(wide_blocks,union(over_const_bitwise,over_shared_bitwise)),filter(lt:r+le:3/4:n))),",
        "cand(split_bits,if(fits_split,seq(split_bits,filter(!eq:r)),none)),",
        &format!("cand(halve_first,seq(halve,filter(!eq:r),{rp})),"),
        "cand(over_products,seq(over_products,filter(!eq:r))),",
        "cand(over_const_bitwise,seq(over_const_bitwise,filter(!eq:r))),",
        "cand(over_shared_bitwise,seq(over_shared_bitwise,filter(!eq:r))),",
        // Halving the whole input can give semi-linear regions that are slow to search.
        &format!("cand(halve_input,with(semi_leaves=2,if(tiny,none,seq(load/t,halve,filter(!eq:t),{rp}))))),"),
        // A form from abstracted subterms only a little smaller than the first rebuild, or
        // larger, made the rules finish worse at least as often as better (Ensia, LLVM Pluto).
        "finish,save/f,filter(!abstracted|le:3/4:f),save/b,label/b,",
        // A region rebuilt in clusters is smaller there but can leave the rules a worse start
        // than rebuilding it whole.
        "cand(unclustered,if(used_clustered+few_rewrites,seq(load/t,if(!replaceable,off(clustered,with(relate_leaves=unclustered_relate_leaves+rewrites=unclustered_rewrites,",
        "seq(rewrite,within,relate,within,tfunc,finish,drop_identities))),none)),none)),",
        // An equal-size one can take the extraction from the first rebuild with nothing gained.
        "label/b,save/u,load/b,best(keep,id),save/m,union(seq(load/u,filter(lt:m)),load/m,seq(load/u,filter(gt:m+lt:t0))),pre_done))",
    ]
    .concat()
}

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
    INNER.iter().position(|k| *k == name).is_some_and(is_off_at)
}

/// The position of `name` in `INNER`, for `is_off_at`.
pub const fn inner_index(name: &str) -> usize {
    let mut i = 0;
    while i < INNER.len() {
        let (a, b) = (INNER[i].as_bytes(), name.as_bytes());
        if a.len() == b.len() {
            let mut j = 0;
            while j < a.len() && a[j] == b[j] {
                j += 1;
            }
            if j == a.len() {
                return i;
            }
        }
        i += 1;
    }
    panic!("not an INNER pass")
}

/// `is_off` of the `INNER` pass at position `i`.
pub fn is_off_at(i: usize) -> bool {
    TOUCHED.with(|t| t.set(t.get() | 1 << i));
    OFF.with(|o| o.get()) >> i & 1 == 1
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
    /// Entries of `INNER` turned off.
    pub off: Vec<&'static str>,
    /// Entries of `GATES` turned off for inputs that do not need them (`set_gates`).
    pub gates: Vec<&'static str>,
    /// Values of the `LIMITS`, in order.
    pub limits: Vec<usize>,
    /// The passes `simplify` runs on its input (`pipeline()`).
    pub pipeline: Pipe,
    /// The pre-pass on one term (`prepass()`): its first candidate is the main rebuild, the
    /// others are unioned with it.
    pub prepass: Pipe,
    /// The final polish, on each candidate alone (`polish(...)`); a candidate is replaced
    /// by its first result when smaller.
    pub polish: Pipe,
    /// The rebuild of one term (`REWRITE`), memoized by `linear_mba::rewrite` and used by the
    /// passes inside it for subterms.
    pub rewrite: Pipe,
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
            off: vec!["semi/peel_shapes"],
            gates: GATES.to_vec(),
            limits: LIMITS.iter().map(|(_, d)| *d).collect(),
            pipeline: Pipe::parse(&pipeline()).unwrap(),
            prepass: Pipe::parse(&prepass()).unwrap(),
            polish: Pipe::parse(&polish(&crate::linear_mba::POLISH.map(|(n, _)| n))).unwrap(),
            rewrite: Pipe::parse(REWRITE).unwrap(),
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
    /// `key=value`, and for the lists `pre`, `off`, `gates` and `schedule` also `key+=names`
    /// and `key-=names` (names separated by `,`; schedule steps written `run:`, `once:` or
    /// `sat:` and a ruleset). The `LIMITS` are keys too (`split_runs=8`); `pipeline`,
    /// `prepass`, `polish` and `rewrite` take a `Pipe` (spaces inside its parentheses allowed), and
    /// `polish` also a list of polish pass names, run as `polish(names)`.
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
            if let Some(val) = item.strip_prefix("prepass=") {
                p.prepass = Pipe::parse(val)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("pipeline=") {
                p.pipeline = Pipe::parse(val)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("rewrite=") {
                p.rewrite = Pipe::parse(val)?;
                continue;
            }
            if let Some(val) = item.strip_prefix("polish=") {
                let names: Vec<&str> = val.split(',').filter(|s| !s.is_empty()).collect();
                let all_polish = names.iter().all(|n| crate::linear_mba::POLISH.iter().any(|(m, _)| m == n));
                p.polish = Pipe::parse(&if all_polish { polish(&names) } else { val.to_string() })?;
                continue;
            }
            let (key, op, val) = ["+=", "-=", "="]
                .iter()
                .find_map(|op| item.split_once(op).map(|(k, v)| (k, *op, v)))
                .ok_or_else(|| format!("expected key=value: {item}"))?;
            let names = |known: &[&'static str]| -> Result<Vec<&'static str>, String> {
                val.split(',').filter(|s| !s.is_empty()).map(|n| known.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown {key} name {n}; known: {}", known.join(",")))).collect()
            };
            let list = match key {
                "pre" => Some((&mut p.pre, names(&PRE)?)),
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
                "match_limit" => p.match_limit = num()?,
                "ban_length" => p.ban_length = num()?,
                _ => match LIMITS.iter().position(|(n, _)| *n == key) {
                    Some(i) => p.limits[i] = num()?,
                    None => {
                        let limits: Vec<&str> = LIMITS.iter().map(|(n, _)| *n).collect();
                        return Err(format!("unknown key {key}; known: schedule match_limit ban_length pre keep extra rerun_input printed minimal off gates pipeline prepass polish rewrite {}", limits.join(" ")));
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
            "schedule={} match_limit={} ban_length={} pre={} keep={} extra={} rerun_input={} printed={} minimal={} off={} gates={}",
            steps.join(","),
            self.match_limit,
            self.ban_length,
            self.pre.join(","),
            self.keep,
            self.extra,
            self.rerun_input as u8,
            self.printed,
            self.minimal as u8,
            self.off.join(","),
            self.gates.join(",")
        )?;
        for ((name, default), v) in LIMITS.iter().zip(&self.limits) {
            if v != default {
                write!(f, " {name}={v}")?;
            }
        }
        write!(f, " pipeline={} prepass={} polish={} rewrite={}", self.pipeline, self.prepass, self.polish, self.rewrite)
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
        assert_eq!(p.polish, Pipe::parse(&polish(&["factor", "push_not", "factor"])).unwrap());
        assert_eq!(Pipe::parse(&Passes::default().polish.to_string()).unwrap(), Passes::default().polish);
        let p = Passes::parse("rewrite=regions(best(1,simba,poly_mba))").unwrap();
        assert_eq!(p.rewrite.to_string(), "regions(best(1,simba,poly_mba))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("polish+=factor").is_err() && Passes::parse("polish=nope").is_err());
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
        let p = Passes::parse("pipeline=smallest(seq(fix(restarts,retry(mixed+!minimal,prepass,egglog/later)),if(!input,tag(t,polish),id)))").unwrap();
        assert_eq!(p.pipeline.to_string(), "smallest(seq(fix(restarts,retry(mixed+!minimal,prepass,egglog/later)),if(!input,tag(t,polish))))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(Pipe::parse(&Passes::default().pipeline.to_string()).unwrap(), Passes::default().pipeline);
        assert_eq!(Pipe::parse(&Passes::default().prepass.to_string()).unwrap(), Passes::default().prepass);
        let p = Passes::parse("prepass=scope(seq(save/t,with(rewrites=unified_rewrites+semi_leaves=2,rewrite),filter(lt:t|le:3/4:t+!tiny),cand(halve_input,load/t)))").unwrap();
        assert_eq!(p.prepass.to_string(), "scope(seq(save/t,with(rewrites=unified_rewrites+semi_leaves=2,rewrite),filter(lt:t|le:3/4:t+!tiny),cand(halve_input,load/t)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["prepass=filter(lt)", "prepass=filter(le:3:t)", "prepass=with(rewrites=x,id)", "prepass=with(nope=1,id)", "prepass=save/", "prepass=scope(id,id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        for bad in ["pipeline=nope", "pipeline=seq(rewrite", "pipeline=best(x,rewrite)", "pipeline=fix(2,a,b)", "pipeline=off(nope,rewrite)", "pipeline=loop(rewrite)", "pipeline=fix(many,id)", "pipeline=if(nope,id)", "pipeline=if(mixed,id,id,id)", "pipeline=retry(mixed,id)"] {
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
