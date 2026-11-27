//! The pass pipeline of `simplify`: the egglog schedule of a round, the five pipelines of
//! `Passes` (`pipeline`, `prepass`, `polish`, `rewrite`, `simba`) and the rebuilds of subterms.
//! `Passes::default()` is the tuned pipeline of `default.pipe`; `--passes` changes it with a spec
//! such as `pre-=halve_input polish=push_not,factor extra=0`.

use crate::lang::ast::Pipe;
use crate::lang::defs::{Def, Defs};
use crate::lang::source::Lets;
use crate::lang::vars::{get, parsing, var};
use crate::rust_vars::{BAN_LENGTH, FLAG0, INNER, ITER_LIMIT, MATCH_LIMIT, RUST_VARS, is_extern_switch};

/// The rebuilds of subterms that passes inside a rebuild make (`Passes::subs`), by name, and
/// their default pipelines: `rewrite` (the memoized `Passes::rewrite`) or `rebuild` (the
/// rebuild of `simplify_linear` without `relate`, `linear_mba::rebuild_once`).
pub const SUBS: [(&str, &str); 13] = [
    // Each group of a clustered region, and each term of a group that did not shrink.
    ("cluster", "rewrite"),
    // A region with arithmetic leaves related, the shrunk region whole, complemented leaves.
    ("relate", "rewrite"),
    // The sides of a `bit_split`.
    ("bit_split", "rewrite"),
    // The halved operands of `halve`.
    ("halve", "rewrite"),
    // A region with its unused leaves set to 0.
    ("drop_unused", "rewrite"),
    // The factors of recombined products and the region they changed.
    ("recombine", "rewrite"),
    // The joined groups of `join_constants` and `join_linear`.
    ("polish", "rewrite"),
    // A product factor with its constants cut below the other's trailing zeros.
    ("low_factor", "rewrite"),
    // The leaves `poly_mba` expands over and its factors with a constant bitwise operation.
    ("poly", "rewrite"),
    // The cases of `over_products`.
    ("over_products", "rebuild"),
    // The cases of `split_bits`.
    ("split_bits", "rebuild"),
    // The terms of `over_const_bitwise` and `over_shared_bitwise`.
    ("over_bitwise", "rebuild"),
    // The cases of `shift_cases`.
    ("shift_cases", "rebuild"),
];

/// The position of `name` in `SUBS`.
pub const fn sub_index(name: &str) -> usize {
    let mut i = 0;
    while i < SUBS.len() {
        let (a, b) = (SUBS[i].0.as_bytes(), name.as_bytes());
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
    panic!("not a SUBS name")
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

pub(crate) const STEPS: [(Step, &str); 3] = [(Step::Run, "run"), (Step::Once, "once"), (Step::Saturate, "sat")];

#[derive(Clone, Debug, PartialEq)]
pub struct Passes {
    /// The steps each of a round's `iter_limit` repetitions runs, in order.
    pub schedule: Vec<(Step, &'static str)>,
    /// The assignments (`Pipe::Bind` of globals, `on` and `off`) a run starts with, in order: the
    /// first `defaults` from `default.pipe`, the rest from `--passes` (`entry_steps`).
    pub entry: Vec<Pipe>,
    pub defaults: usize,
    /// `check_limits` of `default.pipe` (or of `--passes`, which may redefine it), run once
    /// after the entry assignments (`eval::in_run`).
    pub check: Pipe,
    /// The passes `simplify` runs on its input.
    pub pipeline: Pipe,
    /// The pre-pass on one term: its first candidate is the main rebuild, the others are
    /// unioned with it.
    pub prepass: Pipe,
    /// The final polish, on each candidate alone; a candidate is replaced by its first result
    /// when smaller.
    pub polish: Pipe,
    /// The rebuild of one term, memoized by `linear_mba::rewrite` and used by the
    /// passes inside it for subterms.
    pub rewrite: Pipe,
    /// The rebuild of one linear region, the `simba` pass.
    pub simba: Pipe,
    /// The rebuilds of subterms, in the order of `SUBS`.
    pub subs: Vec<Pipe>,
    /// The functions `(def (NAME) body)` defines, in order; each may call those before it.
    /// The first `default_defs` come from `default.pipe`.
    pub defs: Vec<std::sync::Arc<Def>>,
    pub default_defs: usize,
    /// The variables the source files define (`NAME = VALUE` items), in order; the first
    /// `default_globals` in `default.pipe`.
    pub globals: Vec<usize>,
    pub default_globals: usize,
    /// The positions in `entry` of the `--passes` items that define a variable.
    pub defines: Vec<usize>,
}

/// The default passes, and the names `default.pipe` defines for `--passes` to use.
pub(crate) static DEFAULT: std::sync::LazyLock<(Passes, Defs)> = std::sync::LazyLock::new(|| {
    crate::lang::builtins::all();
    let mut p = Passes::base();
    let mut defs = Defs::new();
    let mut globals = Vec::new();
    parsing(&mut globals, || p.apply_source(include_str!("default.pipe"), &mut defs, &mut Lets::default(), true)).and_then(|()| p.check()).unwrap_or_else(|e| panic!("src/default.pipe: {e}"));
    p.globals = globals;
    p.check = check_of(&defs);
    if let Some(e) = p.undefined().first() {
        panic!("{e}");
    }
    p.defaults = p.entry.len();
    p.default_defs = p.defs.len();
    p.default_globals = p.globals.len();
    (p, defs)
});

/// The checks `(let check_limits ...)` defines in `defs`.
pub(crate) fn check_of(defs: &Defs) -> Pipe {
    defs.get("check_limits").map_or_else(Pipe::id, |n| n.pipe.clone())
}

impl Default for Passes {
    fn default() -> Passes {
        DEFAULT.0.clone()
    }
}

impl Passes {
    /// The settings `default.pipe` starts from; its pipelines are `id`.
    fn base() -> Passes {
        use Step::*;
        let id = Pipe::id();
        Passes {
            schedule: vec![
                (Run, "default-ruleset"),
                (Run, "canonicalization"),
                (Saturate, "constant-folding"),
                (Saturate, "analysis"),
                (Saturate, "identity-zero-element"),
                (Run, "simplify"),
            ],
            entry: Vec::new(),
            defaults: 0,
            check: id.clone(),
            pipeline: id.clone(),
            prepass: id.clone(),
            polish: id.clone(),
            rewrite: id.clone(),
            simba: id,
            subs: SUBS.iter().map(|(_, d)| crate::lang::builtins::resolve(d).unwrap()).collect(),
            defs: Vec::new(),
            default_defs: 0,
            globals: Vec::new(),
            default_globals: 0,
            defines: Vec::new(),
        }
    }

    /// The `run-schedule` command of an egglog round: `iter_limit` repetitions, the back-off
    /// scheduler with `match_limit` and `ban_length`.
    pub fn egglog_schedule(&self) -> String {
        let iter = get(ITER_LIMIT);
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
            get(MATCH_LIMIT),
            get(BAN_LENGTH)
        )
    }

    /// The variables the Rust code reads that the source files do not define, as errors: a
    /// pass switch (`INNER`) is defined by an `extern @switch` or, for a step inside a pass,
    /// in `default.pipe`.
    fn undefined(&self) -> Vec<String> {
        let sigs = crate::lang::builtins::all();
        let defined = |i: usize| self.globals.contains(&i) || i < FLAG0 && is_extern_switch(INNER[i]);
        let mut out: Vec<String> = (0..RUST_VARS).filter(|i| !defined(*i)).map(|i| format!("src/default.pipe: {} is read by the Rust code and not defined", var(i).name)).collect();
        out.extend(INNER.iter().enumerate().filter(|(i, n)| is_extern_switch(n) && self.globals.contains(i)).map(|(_, n)| format!("src/default.pipe: {n} is defined by its extern @switch")));
        out.extend(sigs.iter().filter(|s| s.switch && !INNER.contains(&s.name.as_str())).map(|s| format!("src/builtins.pipe: {} has @switch and is not in rust_vars::INNER", s.name)));
        out
    }

    /// `(def (name) body)` for a defined function of the Rust code: `pipeline`, `prepass`,
    /// `polish`, `rewrite`, `simba` or `sub_NAME`.
    pub(crate) fn define(&mut self, name: &str, body: Pipe) -> Result<(), String> {
        let slot = match name {
            "pipeline" => &mut self.pipeline,
            "prepass" => &mut self.prepass,
            "polish" => &mut self.polish,
            "rewrite" => &mut self.rewrite,
            "simba" => &mut self.simba,
            _ => {
                let sub = name.strip_prefix("sub_").unwrap_or(name);
                let names: Vec<&str> = SUBS.iter().map(|(n, _)| *n).collect();
                let i = names.iter().position(|n| *n == sub).ok_or_else(|| format!("unknown sub_{sub}; known: {}", names.join(" ")))?;
                &mut self.subs[i]
            }
        };
        *slot = body;
        Ok(())
    }
}

/// Whether `name` is a function the Rust code defines and calls, which `(def (NAME) p)`
/// (written also `NAME=p`) replaces: `pipeline`, `prepass`, `polish`, `rewrite`, `simba`,
/// `sub_NAME`.
pub fn defined_builtin(name: &str) -> bool {
    ["pipeline", "prepass", "polish", "rewrite", "simba"].contains(&name) || name.strip_prefix("sub_").is_some_and(|n| crate::passes::SUBS.iter().any(|(s, _)| *s == n))
}

thread_local! {
    /// The passes of the run on this thread (`set_current`), the default ones until set.
    static CURRENT: std::cell::RefCell<Option<std::rc::Rc<Passes>>> = const { std::cell::RefCell::new(None) };
}

/// The passes `set_current` last set on this thread.
pub fn current() -> std::rc::Rc<Passes> {
    CURRENT.with(|c| c.borrow_mut().get_or_insert_with(|| std::rc::Rc::new(Passes::default())).clone())
}

/// Makes `p` the passes of the runs on this thread that follow (`current`).
pub fn set_current(p: &Passes) {
    CURRENT.with(|c| {
        let mut c = c.borrow_mut();
        if c.as_deref() != Some(p) {
            *c = Some(std::rc::Rc::new(p.clone()));
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::passes::polish;
    use crate::lang::ast::{Expanded, show};
    use crate::lang::defs::sig_of;
    use crate::lang::lexer::NO_EXTERN;
    use crate::lang::parser::{parse, parse_with};
    use crate::lang::vars::{NONE, ReadSet, VarKind, epoch_ns, in_scope, kind, swap_read, var_index, var_names};
    use crate::rust_vars::{DEADLINE, Limit, RESTARTS, RUST_VARS, is_off, limit, turn_off, turn_on, with_off};

    fn x() -> crate::cand::Cand {
        crate::cand::Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input")
    }

    /// `s` parsed with the names `default.pipe` defines.
    fn parse_default(s: &str) -> Pipe {
        parse_with(s, &DEFAULT.1, &mut Vec::new()).unwrap()
    }

    /// The value of variable `name` after the entry assignments of `p`.
    fn after_entry(p: &Passes, name: &str) -> u64 {
        let i = parsing(&mut p.globals.clone(), || var_index(name)).unwrap();
        crate::lang::eval::in_run(p, None, x, || get(i))
    }

    #[test]
    fn off_ends_with_its_scope() {
        let p = Passes::parse("off+=relate").unwrap();
        crate::lang::eval::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("semi_peel_shapes"), "the entry assignments run first");
            in_scope(|| {
                turn_on("relate");
                crate::lang::eval::in_run(&p, None, x, || assert!(!is_off("relate"), "a run inside a run keeps the bindings of its caller"));
                turn_off("tfunc");
            });
            assert!(!is_off("tfunc") && is_off("relate"), "a pass turned off in a scope is on again after it");
        });
        assert!(!is_off("relate") && !is_off("semi_peel_shapes"), "the entry bindings end with the run");
    }

    #[test]
    fn entry_assignments() {
        let p = Passes::parse("extra=5 split_runs=vars*3 extra=extra+1 off=relate,tfunc off+=simba off-=tfunc").unwrap();
        assert_eq!(after_entry(&p, "extra"), 6, "items run in order, a later one reading an earlier");
        assert_eq!(after_entry(&p, "split_runs"), 6, "a value is evaluated on the input");
        assert_eq!(after_entry(&p, "keep"), 2, "default.pipe comes first");
        crate::lang::eval::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("simba") && !is_off("tfunc"));
            assert!(!is_off("semi_peel_shapes"), "off= turns every other pass on");
        });
        assert!(!is_off("relate") && get(var_index("extra").unwrap()) == NONE, "nothing leaks out of a run");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(p.to_string().contains(" extra=5 split_runs=vars * 3 extra=extra + 1 off=relate,tfunc off+=simba off-=tfunc "), "{p}");
        let p = Passes::parse("off-=semi_peel_shapes keep=0 prove_minimal=0 restarts=7 match_limit=9").unwrap();
        assert!(crate::lang::eval::in_run(&p, None, x, || !is_off("semi_peel_shapes")));
        assert_eq!([after_entry(&p, "keep"), after_entry(&p, "prove_minimal"), after_entry(&p, "restarts")], [0, 0, 7]);
        assert!(crate::lang::eval::in_run(&p, None, x, || p.egglog_schedule().contains(":match-limit 9 :ban-length 3")));
        let p = Passes::parse("off=").unwrap();
        assert_eq!(p.entry[p.defaults..], [Expanded::switches(true, &INNER)]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let cli = crate::Cli { max_restarts: 5, iter_limit: 3, passes: Passes::parse("iter_limit=iter_limit*2").unwrap(), ..Default::default() };
        let (m, i) = crate::lang::eval::in_run(&cli.passes, Some(&cli), x, || (get(RESTARTS), get(ITER_LIMIT)));
        assert_eq!((m, i), (5, 6), "-m and -i come before the --passes items");
        let shown = cli.passes.show_run(5, 3);
        assert!(shown.starts_with("# A run: keep = 2 | ") && shown.contains("| restarts = 5 | iter_limit = 3 | iter_limit = iter_limit * 2 | check_limits | pipeline\n"), "{shown}");
        assert_eq!(Passes::parse(&shown).unwrap(), cli.passes);
        for bad in ["minimal=0", "relate=none", "nope=1", "split_runs=4 | rewrite", "keep+=1", "size=3"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn default_pipe_assigns_every_variable() {
        let p = Passes::default();
        let cli = crate::Cli::default();
        let all = || (0..RUST_VARS).chain(p.globals.iter().copied().filter(|i| *i >= RUST_VARS));
        let unset: Vec<&str> = crate::lang::eval::in_run(&p, None, x, || all().filter(|&i| var(i).kind != VarKind::Pass && get(i) == NONE).map(|i| var(i).name).collect());
        assert_eq!(unset, ["rewrites", "bit_split_budget", "restarts", "iter_limit", "time_limit"]);
        let unset: Vec<&str> = crate::lang::eval::in_run(&p, Some(&cli), x, || all().filter(|&i| get(i) == NONE && var(i).kind != VarKind::Pass).map(|i| var(i).name).collect());
        assert_eq!(unset, ["rewrites", "bit_split_budget", "time_limit"], "-m and -i set restarts and iter_limit");
        assert_eq!(get(var_index("max_leaves").unwrap()), NONE, "outside a run every variable is none");
    }

    #[test]
    fn source_defines_every_variable_rust_reads() {
        let p = Passes::default();
        assert_eq!(p.undefined(), Vec::<String>::new(), "every name the Rust code reads is defined, every extern @switch is in INNER");
        let defined: Vec<&str> = p.globals.iter().map(|i| var(*i).name).collect();
        for i in 0..RUST_VARS {
            assert_eq!(defined.contains(&var(i).name), i >= FLAG0 || !is_extern_switch(var(i).name), "{}", var(i).name);
        }
        let steps: Vec<&str> = INNER.iter().copied().filter(|n| !is_extern_switch(n)).collect();
        assert_eq!(steps, ["poly_masked", "semi_grouped", "semi_peel_grouped", "semi_shapes", "semi_pairs", "semi_peel_shapes", "semi_split", "semi_scaled", "semi_bit_split", "semi_short_consts"], "the switches of steps inside passes are defined in default.pipe");
        let only_pipelines: Vec<&str> = p.globals.iter().filter(|i| **i >= RUST_VARS).map(|i| var(*i).name).collect();
        let pre = ["pre_unified", "pre_no_wide", "pre_split_bits", "pre_halve_first", "pre_over_products", "pre_over_const_bitwise", "pre_over_shared_bitwise", "pre_halve_input", "pre_unclustered"];
        assert_eq!(only_pipelines, [&["extra", "printed"][..], &pre, &["unclustered_relate_leaves", "unclustered_rewrites", "unified_rewrites", "cand_bit_splits", "polish_rewrites", "polish_wins"]].concat());
        let mut all = p.clone();
        all.default_globals = 0;
        assert_eq!(all.unread_globals(), Vec::<&str>::new(), "a pipeline reads each variable the Rust code does not");
        assert_eq!(Passes::parse_noting("").unwrap().1, Vec::<String>::new(), "default.pipe gives no warnings");
        let kinds = [("relate", VarKind::Pass), ("semi_shapes", VarKind::Pass), ("cut", VarKind::Flag), ("max_leaves", VarKind::Limit), ("memo_contexts", VarKind::Unread), ("wide_blocks_cache_size", VarKind::Unread), ("semi_leaves", VarKind::Setting), ("keep", VarKind::Setting), ("rewrites", VarKind::Budget), ("bit_split_budget", VarKind::Budget), ("time_limit", VarKind::Deadline), ("extra", VarKind::Global)];
        for (n, k) in kinds {
            assert_eq!(kind(var_index(n).unwrap()), k, "{n}");
        }
        let r = crate::lang::eval::in_run(&p, None, x, || {
            swap_read(ReadSet::EMPTY);
            let e = Pipe::global(var_index("memo_contexts").unwrap());
            let env = crate::lang::eval::Env::prepass(&p, 64, None, false, x().term());
            crate::lang::eval::run(&Pipe::app("filter", vec![e]), vec![x()], &env).unwrap();
            swap_read(ReadSet::EMPTY)
        });
        assert!(!r.ones().any(|i| i == var_index("memo_contexts").unwrap()), "a pipeline reading an UNREAD limit does not record it");
    }

    #[test]
    fn caps_reject_larger_values() {
        assert_eq!(after_entry(&Passes::parse("max_leaves=5 max_wide_leaves=64").unwrap(), "max_leaves"), 5);
        let caps = [
            ("block_max_block", 5),
            ("max_leaves", crate::linear_mba::TABLE_LEAVES as u64),
            ("max_wide_leaves", 64),
            ("lowbits_max_bits", 63),
            ("lowbits_max_context_bits", 63),
            ("lowbits_max_refine_bits", 63),
            ("overlap_max_terms", 63),
            ("unify_operands_max_leaves", 63),
            ("decompose_max_free_classes", 63),
            ("wide_blocks_max_term_leaves", 63),
            ("wide_blocks_max_block", 63),
            ("shapes_max_size", 15),
            ("tfunc_max_vars", crate::tfunc::VARS_CAP as u64),
            ("tfunc_points", crate::tfunc::POINTS_CAP as u64),
            ("tfunc_max_carries", 128),
            ("minimal_lanes", crate::minimal::LANES_CAP as u64),
            ("minimal_max_vars", 31),
        ];
        let prepass = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::lang::eval::run(&p.prepass, vec![x()], &crate::lang::eval::Env::prepass(&p, 64, None, false, x().term())).err().map(|e| e.to_string())
        };
        for (name, cap) in caps {
            let msg = format!("{name} is at most {cap}");
            assert!(include_str!("default.pipe").contains(&format!("(assert ({name} <= {cap}) \"{msg}\")")), "{name}");
            assert_eq!(prepass(&format!("{name}={cap}")), None, "{name}");
            for bad in [(cap + 1).to_string(), "none".into()] {
                assert_eq!(prepass(&format!("{name}={bad}")).as_deref(), Some(msg.as_str()), "{name}={bad}");
            }
        }
        let input = crate::cand::Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input");
        let cli = crate::Cli { passes: Passes::parse("max_leaves=7").unwrap(), ..crate::Cli::default() };
        assert_eq!(crate::simplify(input.term(), &cli).err().map(|e| e.to_string()).as_deref(), Some("max_leaves is at most 6"), "checked when the run starts");
        let p = Passes::parse("prepass=(max_leaves = 7 | id)").unwrap();
        let r = crate::lang::eval::run(&p.prepass, vec![input.clone()], &crate::lang::eval::Env::prepass(&p, 64, None, false, input.term()));
        assert!(r.is_ok(), "only the entry assignments are checked, not those inside a pipeline");
        let p = Passes::parse("prepass=(max_leaves = vars * 4 | check_limits | rewrite)").unwrap();
        let cli = crate::Cli { passes: p, ..crate::Cli::default() };
        let r = crate::simplify(input.term(), &cli);
        assert_eq!(r.err().map(|e| e.to_string()).as_deref(), Some("max_leaves is at most 6"), "a pipeline can check its own assignments; a pre-pass run inside the pipeline gives its error");
    }

    #[test]
    fn any_number_of_globals() {
        let dir = std::env::temp_dir().join(format!("eggy1-globals-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("many.pipe");
        let mut text: String = (0..300).map(|i| format!("many_g{i} = {i}\n")).collect();
        text.push_str("(def (prepass) (fix (many_g299 - many_g298) rewrite) | (if many_g150 lowbits))\n");
        std::fs::write(&f, text).unwrap();
        let p = Passes::parse(&format!("file={}", f.display())).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!([after_entry(&p, "many_g0"), after_entry(&p, "many_g150"), after_entry(&p, "many_g299")], [0, 150, 299]);
        let r = crate::lang::eval::in_run(&p, None, x, || crate::lang::eval::run(&p.prepass, vec![x()], &crate::lang::eval::Env::prepass(&p, 64, None, false, x().term())).unwrap());
        assert_eq!(r[0].term().to_string(), x().term().to_string());
    }

    #[test]
    fn memo_keys_hold_source_globals() {
        let dir = std::env::temp_dir().join(format!("eggy1-memo-globals-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("memo.pipe");
        std::fs::write(&f, "pick = 0
(def (rewrite) (if pick (again (best 1 (regions (best 1 simba small_blocks wide_blocks)) poly_mba)) id))
(def (prepass) (scope pick = 0 | rewrite | pick = 1 | rewrite))
").unwrap();
        let p = Passes::parse(&format!("file={}", f.display())).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        let t = || crate::cand::Cand::new("(Add (And (Var \"x\") (Var \"y\")) (Or (Var \"x\") (Var \"y\")))", "input");
        let r = crate::lang::eval::in_run(&p, None, t, || crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(&p, 64, None, false, t().term())).unwrap());
        assert_eq!(r[0].term(), "(Add (Var \"x\") (Var \"y\"))", "the rewrite memoized with pick = 0 is not reused with pick = 1");
    }

    #[test]
    fn moved_constants_bind_in_their_scope() {
        let input = "(Mul (Var \"x\") (Mul (Var \"x\") (Var \"x\")))";
        let t = || crate::cand::Cand::new(&format!("(And (Add {input} (Var \"x\")) (Num 1))"), "input");
        let plain = Passes::parse("prepass=(scope lowbits)").unwrap();
        let scoped = Passes::parse("prepass=(scope (lowbits_max_try = 1 | lowbits) | lowbits)").unwrap();
        let none = Passes::parse("prepass=(scope (lowbits_max_try = 1 | id) | lowbits)").unwrap();
        let run = |p: &Passes| crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(p, 8, None, false, t().term())).unwrap()[0].term().to_string();
        assert_eq!(run(&plain), "(Num 0)", "x*x*x + x is even");
        assert_eq!(run(&none), "(Num 0)", "the assignment ends with its sequence");
        let inner = Passes::parse("prepass=(scope lowbits_max_try = 1 | lowbits)").unwrap();
        assert_ne!(run(&inner), "(Num 0)", "with nothing enumerated nothing folds");
        assert_eq!(run(&scoped), "(Num 0)");
        crate::lang::eval::in_run(&plain, None, t, || {
            assert_eq!(limit(Limit::LowbitsMaxTry), 256);
            crate::lang::eval::run(&parse("lowbits_max_try = 1 | id").unwrap(), vec![t()], &crate::lang::eval::Env::prepass(&plain, 8, None, false, t().term())).unwrap();
            assert_eq!(limit(Limit::LowbitsMaxTry), 256, "a run ends the bindings made in it");
        });
    }

    #[test]
    fn moved_poly_constants_bind_in_their_scope() {
        let (x, y) = ("(Var \"x\")", "(Var \"y\")");
        let input = format!("(Sub (Mul (Add {x} {y}) (Add {x} {y})) (Add (Mul {x} {x}) (Mul (Num 2) (Mul {x} {y}))))");
        let t = || crate::cand::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(&p, 8, None, false, t().term())).unwrap()[0].term().to_string()
        };
        let plain = run("prepass=(scope (best 1 id poly_mba))");
        assert_eq!(plain, format!("(Mul {y} {y})"));
        assert_eq!(run("prepass=(scope poly_max_monos = 0 | (best 1 id poly_mba))"), input, "no product is multiplied out");
        assert_eq!(run("prepass=(scope (poly_max_monos = 0 | id) | (best 1 id poly_mba))"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (poly_max_monos = 0 | (best 1 id poly_mba)) | (best 1 id poly_mba))"), plain, "the memo keeps the scopes apart");
    }

    #[test]
    fn moved_polish_constants_bind_in_their_scope() {
        let input = crate::expr_convert::infix_to_egglog("(s - (z & (y | s))) + z + (u ^ x ^ z)", true);
        let t = || crate::cand::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            let r = crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(&p, 32, None, false, t().term())).unwrap();
            crate::eval::size(&crate::eval::parse(r[0].term()))
        };
        let before = crate::eval::size(&crate::eval::parse(&input));
        let plain = run("prepass=(scope polish_join_linear)");
        assert!(plain < before, "a move makes it smaller");
        assert_eq!(run("prepass=(scope join_linear_max_groups = 0 | polish_join_linear)"), before, "no region is moved in");
        assert_eq!(run("prepass=(scope (join_linear_max_groups = 0 | id) | polish_join_linear)"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (join_linear_max_groups = 0 | polish_join_linear) | polish_join_linear)"), plain, "the memo keeps the scopes apart");
    }

    #[test]
    fn tfunc_constants_bind_in_their_scope() {
        let input = crate::expr_convert::infix_to_egglog("x & -(x & -(x & y))", true);
        let t = || crate::cand::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(&p, 64, None, false, t().term())).unwrap()[0].term().to_string()
        };
        let plain = run("prepass=(scope tfunc)");
        assert_eq!(plain, "(And (Var \"x\") (Var \"y\"))");
        assert_eq!(run("prepass=(scope tfunc_max_size = 2 | tfunc)"), input, "no table entry is small enough");
        assert_eq!(run("prepass=(scope (tfunc_max_size = 2 | id) | tfunc)"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (tfunc_max_size = 2 | tfunc) | tfunc)"), plain, "the tables keep the values apart");
    }

    #[test]
    fn wide_blocks_constants_bind_in_their_scope() {
        let input = crate::expr_convert::infix_to_egglog("-2*((((h ^ g) & a) | f) - (((h ^ g) & a) & f)) - 2*(((g + j) - (g & j)) + ((a | h) - (a & h)) - ((g | j) | (a ^ h))) + 2*(((b | h) - (b & h)) + ((g + d) - (g | d)) - ((b ^ h) | (g & d))) + 3*(~f & ~b) + c + i", true);
        let t = || crate::cand::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::lang::eval::run(&p.prepass, vec![t()], &crate::lang::eval::Env::prepass(&p, 64, None, false, t().term())).unwrap()[0].term().to_string()
        };
        let plain = run("prepass=(scope (best 1 id wide_blocks))");
        assert_ne!(plain, input, "a block form is smaller");
        assert_eq!(run("prepass=(scope wide_blocks_max_block = 2 | (best 1 id wide_blocks))"), input, "no block is small enough");
        assert_eq!(run("prepass=(scope (wide_blocks_max_block = 2 | id) | (best 1 id wide_blocks))"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (wide_blocks_max_block = 2 | (best 1 id wide_blocks)) | (best 1 id wide_blocks))"), plain, "the cache keeps the scopes apart");
    }

    #[test]
    fn time_limit_zero_is_a_deadline() {
        let at = |spec: &str| crate::lang::eval::in_run(&Passes::parse(spec).unwrap(), None, x, || (get(DEADLINE), epoch_ns()));
        assert_eq!(at("time_limit=none").0, NONE);
        let (deadline, now) = at("time_limit=0");
        assert!(deadline <= now, "0 is a deadline now");
        let (deadline, now) = at("time_limit=2000");
        assert!(deadline > now + 1_000_000_000 && deadline <= now + 2_000_000_000);
        assert_eq!(at("time_limit=1000 time_limit=none").0, NONE, "a later item wins");
    }

    #[test]
    fn spec_round_trip() {
        assert_eq!(Passes::parse("").unwrap(), Passes::default());
        let p = Passes::parse("pre-=halve_input,unified;polish=factor,push_not,factor extra=0 keep=3 prove_minimal=0").unwrap();
        assert!(after_entry(&p, "pre_unified") == 0 && after_entry(&p, "pre_halve_input") == 0 && after_entry(&p, "pre_no_wide") == 1);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(p.polish, parse_default(&polish(&["factor", "push_not", "factor"])));
        let p = Passes::parse("pre=no_wide,unified pre+=halve_input pre-=unified").unwrap();
        let on: Vec<&str> = var_names().into_iter().filter_map(|n| n.strip_prefix("pre_")).filter(|n| after_entry(&p, &format!("pre_{n}")) == 1).collect();
        assert_eq!(on, ["no_wide", "halve_input"], "pre= turns the others off, pre+= and pre-= one each");
        assert!(p.to_string().contains(" pre_unified=1 pre_no_wide=1 pre_split_bits=0"), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("pre=done").is_err(), "pre_done is a function, not a switch");
        for (old, new) in [("sub/cluster=rebuild", "sub_cluster"), ("off=semi/bit_split", "semi_bit_split"), ("semi/peel_shapes=1", "semi_peel_shapes"), ("semi/peel_shapes = 1", "semi_peel_shapes"), ("polish=polish/factor", "polish_factor")] {
            let e = Passes::parse(old).unwrap_err();
            assert!(e.contains(&format!("names cannot contain '/': write {new}")), "{old}: {e}");
        }
        assert_eq!(parse(&Passes::default().polish.to_string()).unwrap(), Passes::default().polish);
        let p = Passes::parse("rewrite=(regions (best 1 simba poly_mba))").unwrap();
        assert_eq!(p.rewrite.to_string(), "(regions (best 1 simba poly_mba))");
        assert_eq!(parse(&Passes::default().simba.to_string()).unwrap(), Passes::default().simba);
        let p = Passes::parse("sub_cluster=(regions simba) sub_split_bits=rewrite").unwrap();
        assert_eq!(p.subs[sub_index("cluster")].to_string(), "(regions simba)");
        assert!(p.to_string().contains(" sub_cluster=(regions simba) sub_split_bits=rewrite"));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("sub_nope=rewrite").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("polish+=factor").is_err() && Passes::parse("polish=nope").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("pre+=nope").is_err() && Passes::parse("keep+=1").is_err());
        let p = Passes::parse("off=semi_bit_split,relate").unwrap();
        assert_eq!(p.entry[p.defaults..], [Expanded::switches(true, &INNER), Expanded::switches(false, &["semi_bit_split", "relate"])]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(crate::lang::eval::in_run(&p, None, x, || is_off("relate") && !is_off("simba")));
        assert!(!is_off("relate"));
        in_scope(|| {
            turn_off("poly_mba");
            assert!(is_off("poly_mba") && !is_off("lowbits"));
        });
        assert!(!is_off("poly_mba"));
        let p = Passes::parse("prepass=(if (mul < 1 && size >= 10 || vars >= 3) (off lowbits)) | lowbits").unwrap();
        assert_eq!(p.prepass.to_string(), "(if (mul < 1 && size >= 10 || vars >= 3) (off lowbits)) | lowbits");
        assert!(Passes::parse("prepass=(if (nope >= 1) id)").is_err() && Passes::parse("prepass=(off nope)").is_err() && Passes::parse("prepass=(if (mul >= x) id)").is_err());
        let e = Passes::parse("prepass=seq(lowbits,rewrite)").unwrap_err();
        assert!(e.contains("no longer read"), "{e}");
        let p = Passes::parse("schedule-=sat:analysis schedule+=once:simplify,sat:analysis match_limit=128").unwrap();
        assert_eq!(p.schedule.last(), Some(&(Step::Saturate, "analysis")));
        assert_eq!(p.schedule.len(), 7);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("schedule=run:nope").is_err() && Passes::parse("schedule=go:simplify").is_err());
        let p = Passes::parse("split_runs=4 poly_builds=64").unwrap();
        assert!(p.to_string().contains(" split_runs=4 poly_builds=64 "));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("split_runs+=1").is_err() && Passes::parse("split_runs=x").is_err());
        assert_eq!(limit(Limit::SplitRuns), usize::MAX, "outside a run every variable is none");
        let got = crate::lang::eval::in_run(&p, None, x, || (limit(Limit::SplitRuns), limit(Limit::PolyBuilds), limit(Limit::SplitDepth)));
        assert_eq!(got, (4, 64, 2));
        assert_eq!(limit(Limit::SplitRuns), usize::MAX);
        let p = Passes::parse("keep=1 pipeline=lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish_factor extra=0").unwrap();
        assert_eq!(p.pipeline.to_string(), "lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish_factor");
        assert_eq!((after_entry(&p, "keep"), after_entry(&p, "extra")), (1, 0));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let p = Passes::parse("pipeline=(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish) id))").unwrap();
        assert_eq!(p.pipeline.to_string(), "(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(parse(&Passes::default().pipeline.to_string()).unwrap(), Passes::default().pipeline);
        assert_eq!(Passes::parse(&format!("prepass={}", Passes::default().prepass)).unwrap().prepass, Passes::default().prepass);
        let d = Passes::default();
        assert_eq!(Passes::parse(&d.to_string()).unwrap(), d);
        assert_eq!(Passes::parse(&format!("{d:#}")).unwrap(), d);
        let p = Passes::parse("extra=0 prepass=lowbits | (if mixed rewrite) # a comment\n| polish keep=3;pipeline=(fix 2 prepass | egglog)").unwrap();
        assert_eq!((after_entry(&p, "extra"), after_entry(&p, "keep")), (0, 3));
        assert_eq!(p.prepass, parse("(seq lowbits (if mixed rewrite id) polish)").unwrap());
        assert_eq!(p.pipeline, parse("(fix 2 (seq prepass egglog))").unwrap());
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let p = Passes::parse("prepass=(scope (save t) | (rewrites = unified_rewrites | semi_leaves = 2 | rewrite) | (filter (size < (size (main t)) || size <= (size (main t)) * 3 / 4 && !tiny)) | (cand pre_halve_input halve_input (load t)))").unwrap();
        assert_eq!(p.prepass.to_string(), "(scope (save t) | (rewrites = unified_rewrites | semi_leaves = 2 | rewrite) | (filter (size < (size (main t)) || size <= (size (main t)) * 3 / 4 && !tiny)) | (cand pre_halve_input halve_input (load t)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["prepass=(filter lt)", "prepass=(filter (size <=))", "prepass=(rewrites = x | id)", "prepass=(save)", "prepass=(scope id id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        assert_eq!(Passes::default().check(), Ok(()));
        assert_eq!(Passes::default().polish, parse_default(&polish(&crate::linear_mba::POLISH.map(|(n, _)| n))));
        let p = Passes::parse("(let twice (fix 2 rewrite)) rewrite=twice | (best 1 twice simba) pipeline=(fix 1 first_round) | polish").unwrap();
        assert_eq!(p.rewrite, parse("(fix 2 rewrite) | (best 1 (fix 2 rewrite) simba)").unwrap());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["(let rewrite id)", "(let x id) (let y nope)", "(let x id) extra", "pipeline=undefined_name", "file=no/such/file.pipe"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        let dir = std::env::temp_dir().join(format!("eggy1-passes-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("a.pipe");
        std::fs::write(&f, "# a file
(let r2 rewrite | rewrite)
extra = 1
times = extra + 1 # a new variable
(def (prepass)
  lowbits | r2 | (fix times rewrite))
").unwrap();
        let (p, notes) = Passes::parse_noting(&format!("file={} keep=3", f.display())).unwrap();
        assert!(notes.is_empty(), "{notes:?}");
        assert_eq!((after_entry(&p, "extra"), after_entry(&p, "keep"), after_entry(&p, "times")), (1, 3, 2));
        assert_eq!(show(&p.prepass), "lowbits | rewrite | rewrite | (fix times rewrite)");
        assert!(p.to_string().contains(" extra=1 times = extra + 1 keep=3 "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("times=1").is_err(), "a variable of one parse is unknown in another");
        let bad = [
            ("off=relate\n", "off names a function or a definition"),
            ("lowbits | rewrite\n", "expected (let ...), (def ...) or NAME = VALUE"),
            ("prepass = lowbits\n", "a source file defines it as (def (prepass) ...)"),
            ("(def (prepass)\n  lowbits\n", "unclosed form"),
            ("(extern (x g:group) group)\n", "only read from src/builtins.pipe"),
        ];
        for (text, msg) in bad {
            std::fs::write(&f, text).unwrap();
            let e = Passes::parse(&format!("file={}", f.display())).unwrap_err();
            assert!(e.contains(msg), "{text}: {e}");
        }
        std::fs::write(&f, "unused_one = 3\nkep = 1\n").unwrap();
        let (_, notes) = Passes::parse_noting(&format!("file={}", f.display())).unwrap();
        assert_eq!(notes, ["unused_one is defined and never read", "kep is defined and never read"]);
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(Passes::parse("rewrite=(fix (restarts - 1) rewrite)").is_ok(), "restarts is a variable");
        for bad in ["prepass=egglog", "simba=reprint", "sub_cluster=(egglog first)", "prepass=lowbits | prepass", "polish=polish", "rewrite=(again polish)", "prepass=(if rebuilds id)"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("simplify run") || e.contains("reaches itself"), "{bad}: {e}");
        }
        assert!(Passes::parse("pipeline=(fix restarts prepass | egglog | polish)").is_ok());
        assert!(Passes::parse("prepass=(egglog x)").unwrap_err().contains("(extern @pipe @simplify_only (egglog label:name? g:group) group)"));
        assert!(Passes::parse("polish=(if mixed reprint)").unwrap_err().contains("reprint needs a simplify run and cannot be in polish"));
        for bad in ["(extern (x g:group) group)", "keep=1 (extern (x g:group) group)", "pipeline=extern"] {
            assert!(Passes::parse(bad).unwrap_err().contains(NO_EXTERN), "{bad}");
        }
        for bad in ["prepass=(load x)", "prepass=(save t) | (load u)", "prepass=(load t) | (save t)", "polish=(filter (size < (size (main t))))", "rewrite=(if (same (main t)) id)", "prepass=(if mixed (save t)) | (label u)", "pipeline=(retry (size < (size (main t))) id (save t))"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("before it is bound"), "{bad}: {e}");
        }
        for bad in ["prepass=t = (load t)", "prepass=t = u | (load t)", "prepass=(load t) | t = id", "prepass=t = (u = id) | (load u) | (load v)", "(def (f) t = id) prepass=f | (load t)"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("before it is bound"), "{bad}: {e}");
        }
        for good in ["prepass=(if mixed (save t)) | (load t)", "prepass=(fix 3 (union (load t) id) | (save t))", "pipeline=(retry (size < (size (main t))) (save t) (load t))", "prepass=(best (size (main t)) (save t) id)", "prepass=t = rewrite | (load t)", "prepass=t = (u = id) | (load u) | (load t)", "(def (f p) p | none) prepass=(f t = rewrite) | (load t)"] {
            assert!(Passes::parse(good).is_ok(), "{good}");
        }
        assert_eq!(Passes::default().warnings(), Vec::<String>::new());
        let mut lets = Lets::default();
        Passes::base().apply(include_str!("default.pipe"), &mut Defs::new(), &mut lets).unwrap();
        assert!(lets.defined.iter().all(|(n, _)| n == "check_limits" || n.split(' ').next().is_some_and(|n| lets.used.iter().any(|u| u == n))), "{:?} {:?}", lets.defined, lets.used);
        let (_, w) = Passes::parse_noting("(let foo rewrite) (let bar lowbits) prepass=bar | (save t) | (save q) | (load t) | ((off relate) | (save x) | id) | (rewrite | (off relate))").unwrap();
        assert_eq!(w.len(), 4, "{w:?}");
        assert!(w[0].contains("let foo") && w[1].contains("group variable q") && w[2].contains("group variable x") && w[3].contains("(off relate) ends"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=(save t) | rewrite | (save t) | (load t)").unwrap();
        assert!(w.len() == 1 && w[0].contains("bound again"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=t = (off relate) | (load t)").unwrap();
        assert!(w.len() == 1 && w[0].contains("(off relate) ends"), "the right side of a group assignment is a scope: {w:?}");
        let (_, w) = Passes::parse_noting("prepass=t = id | t = rewrite | (load t) | u = rewrite | id").unwrap();
        assert!(w.len() == 2 && w[0].contains("group variable u is bound and never read") && w[1].contains("group variable t is bound again"), "{w:?}");
        for ok in ["prepass=(save t) | (if mixed (save t)) | (load t)", "prepass=(save t) | (cand pre_unified unified (save t)) | (load t)", "prepass=(fix 3 (save t) | rewrite) | (load t)", "prepass=(save t) | (filter (size < (size (main t)))) | (save t) | (load t)", "prepass=(save t) | (first rewrite (save t)) | (load t)", "prepass=(if mixed (save t) (save t)) | (load t)"] {
            assert_eq!(Passes::parse_noting(ok).unwrap().1, Vec::<String>::new(), "{ok}");
        }
        let p = Passes::parse("prepass=rewrite | time_limit = 500 | relate | time_limit = size-1 * 2 | tfunc | time_limit = none | lowbits").unwrap();
        assert_eq!(p.prepass.to_string(), "rewrite | time_limit = 500 | relate | time_limit = size - 1 * 2 | tfunc | time_limit = none | lowbits");
        assert_eq!(p, Passes::parse(&p.prepass.to_string().replace("rewrite |", "prepass=rewrite |")).unwrap());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for old in ["prepass=(time-limit 500) | rewrite", "prepass=time-limit", "prepass=(time-limit)", "time-limit=500"] {
            let e = Passes::parse(old).unwrap_err();
            assert!(e.contains("time_limit"), "{old}: {e}");
        }
        assert!(Passes::parse("prepass=(if (size-x > 1) id)").unwrap_err().contains("size-x reads as size - x"));
        for old in ["prepass=(with rewrites=8 rewrite)", "(let w (with semi_leaves=2 rewrite))", "pipeline=(if true id)"] {
            let e = Passes::parse(old).unwrap_err();
            assert!(e.contains("no longer"), "{old}: {e}");
        }
        let (_, w) = Passes::parse_noting("prepass=rewrite | time_limit = 100").unwrap();
        assert!(w.len() == 1 && w[0].contains("time_limit = 100 ends its sequence"), "{w:?}");
        assert_eq!(Passes::parse_noting("prepass=rewrite | (if mixed time_limit = 100) | relate").unwrap().1, Vec::<String>::new());
        let flat = Passes::parse("(let g relate | tfunc) (let h (relate | tfunc)) prepass=lowbits | g | finish rewrite=lowbits | h | finish").unwrap();
        assert_eq!(flat.prepass.to_string(), "lowbits | relate | tfunc | finish");
        assert_eq!(flat.rewrite.to_string(), "lowbits | (relate | tfunc) | finish");
        let p = Passes::parse("prepass=(off relate tfunc) | (on relate cut) | rewrite time_limit=500").unwrap();
        assert_eq!(p.prepass.to_string(), "(off relate tfunc) | (on relate cut) | rewrite");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("prepass=(on nope)").is_err() && Passes::parse("prepass=(on)").is_err() && Passes::parse("prepass=on/relate").is_err());
        let (_, w) = Passes::parse_noting("prepass=rewrite | (scope (rewrites = 8 | (off relate))) | (off cut) | lowbits").unwrap();
        assert!(w.len() == 1 && w[0].contains("(off relate) ends its sequence"), "{w:?}");
        let e = Passes::parse("prepass=save/t").unwrap_err();
        assert!(e.contains("(save t)"), "{e}");
        for bad in ["pipeline=nope", "pipeline=(seq rewrite", "pipeline=(best x rewrite)", "pipeline=(fix 2 a b)", "pipeline=(loop rewrite)", "pipeline=(fix many id)", "pipeline=(if nope id)", "pipeline=(if mixed id id id)", "pipeline=(retry mixed id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        with_off(&["relate"], || {
            assert!(crate::lang::eval::in_run(&Passes::default(), None, x, || is_off("relate")));
        });
        assert!(!is_off("relate"));
    }

    #[test]
    fn assignment_items_and_warnings() {
        let p = Passes::parse("prepass=lowbits | split_runs=4 | rewrite").unwrap();
        assert_eq!(p.prepass.to_string(), "lowbits | split_runs = 4 | rewrite");
        assert_eq!(p.entry, Passes::default().entry, "an assignment after | stays in the pipeline");
        let p = Passes::parse("prepass=lowbits split_runs=4").unwrap();
        assert_eq!((p.prepass.to_string().as_str(), after_entry(&p, "split_runs")), ("lowbits", 4));
        let p = Passes::parse("prepass=lowbits | split_runs = vars * 2 | rewrite extra=0").unwrap();
        assert_eq!((p.prepass.to_string().as_str(), after_entry(&p, "extra")), ("lowbits | split_runs = vars * 2 | rewrite", 0));
        let p = Passes::parse("time_limit=2000 cand_bit_splits=3").unwrap();
        assert_eq!(after_entry(&p, "cand_bit_splits"), 3);
        assert!(p.to_string().contains(" time_limit=2000 cand_bit_splits=3 "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(after_entry(&Passes::parse("bit_split_budget=8").unwrap(), "bit_split_budget"), 8, "any variable is an item");
        let warn = |s: &str| Passes::parse_noting(s).unwrap().1;
        assert!(warn("prepass=rewrite | split_runs = 4").iter().any(|w| w.contains("split_runs = 4 ends its sequence")));
        assert!(warn("prepass=(off relate)").iter().any(|w| w.contains("(off relate) ends")), "a pipeline is a sequence too");
        let w = warn("prepass=split_runs = 4 | split_runs = 8 | rewrite");
        assert!(w.len() == 1 && w[0].contains("split_runs is assigned again"), "{w:?}");
        let w = warn("prepass=(off relate) | relate = 1 | rewrite");
        assert!(w.len() == 1 && w[0].contains("relate is assigned again"), "{w:?}");
        for ok in ["prepass=split_runs = 4 | rewrite | split_runs = 8 | rewrite", "prepass=split_runs = 4 | split_runs = split_runs * 2 | rewrite", "prepass=split_runs = 4 | (split_runs = 8 | rewrite) | rewrite", "prepass=cut = 1 | rewrite"] {
            assert_eq!(warn(ok), Vec::<String>::new(), "{ok}");
        }
        let w = warn("prepass=kep = 3 | rewrite");
        assert_eq!(w, ["prepass: number variable kep is bound and never read", "prepass: number variable kep is a new local variable; did you mean keep?"]);
        let w = warn("prepass=(save rewrits) | rewrite | (load rewrits)");
        assert_eq!(w, ["prepass: group variable rewrits is a new local variable; did you mean rewrites?"], "a distance of 1 or 2 past 4 letters");
        for ok in ["prepass=(save r) | (load r)", "prepass=(save tt) | (load tt)", "prepass=(save mux) | (load mux)", "prepass=(save before) | (load before)"] {
            assert_eq!(warn(ok), Vec::<String>::new(), "{ok}");
        }
        assert_eq!(warn("keep = 3 extra=1"), Vec::<String>::new(), "spaces around = in --passes: the source form");
        assert!(Passes::parse("kep=3").is_err(), "NAME=VALUE assigns a variable that exists");
        let p = Passes::parse("fresh = 3 prepass=(fix fresh rewrite)").unwrap();
        assert_eq!(after_entry(&p, "fresh"), 3);
        assert!(p.to_string().contains(" fresh = 3 "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
    }

    #[test]
    fn def_items() {
        let d = Passes::default();
        for name in ["pipeline", "prepass", "polish", "rewrite", "simba", "sub_cluster"] {
            let short = Passes::parse(&format!("{name}=lowbits | rewrite")).unwrap();
            assert_eq!(Passes::parse(&format!("(def ({name}) lowbits | rewrite)")).unwrap(), short, "{name}");
            assert_ne!(short, d);
        }
        assert_eq!(Passes::parse("polish=factor,push_not").unwrap().polish, parse_default(&polish(&["factor", "push_not"])));
        let p = Passes::parse("(def (twice) rewrite | rewrite) (def (more) twice | relate) prepass=lowbits | more | twice").unwrap();
        assert_eq!(p.defs.len(), p.default_defs + 2);
        assert_eq!(p.prepass.to_string(), "lowbits | more | twice");
        assert_eq!(p.defs[p.default_defs + 1].body.to_string(), "twice | relate");
        assert!(p.to_string().contains(" (def (twice) rewrite | rewrite) (def (more) twice | relate) pipeline="), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(format!("{p:#}").contains("\n# (twice g:group) group\n(def (twice) rewrite | rewrite)\n"));
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        assert_eq!(Passes::parse("(def @inline (g) relate | tfunc) prepass=lowbits | g").unwrap(), Passes::parse("(let g relate | tfunc) prepass=lowbits | g").unwrap());
        for (bad, msg) in [
            ("(def (f) id) (def (f) id)", "already a function"),
            ("(def (f) id) (let f id)", "already a function"),
            ("(def (f) id) (def @inline (f) id)", "already a function"),
            ("(let f id) (def (f) id)", "already defined by let"),
            ("(def (gates) id)", "already defined by let"),
            ("(def (lowbits) id)", "the name of a pass"),
            ("(def (split_runs) id)", "the name of a variable"),
            ("(def @inline (prepass) id)", "replaced only by (def (prepass) p)"),
            ("(let polish id)", "replaced only by"),
            ("(def (sub_nope) id)", "unknown sub_NAME"),
            ("(def (f) prepass) (def (g) f) prepass=lowbits | g", "prepass reaches itself"),
            ("(def (f) polish) (def (g) (if mixed f)) polish=g", "polish reaches itself"),
            ("(def (f) egglog) (def (g) f) prepass=g", "egglog needs a simplify run and cannot be in f, which prepass calls"),
            ("(def (f) (load t))", "f reads group variable t before it is bound"),
            ("(def (f) (save t)) prepass=f | (load t)", "prepass reads group variable t"),
            ("(def (f) id) prepass=(f 1)", "f takes no arguments: (f g:group) group"),
            ("(def (f) id) prepass=(if f id)", "f gives candidates, not a number"),
            ("(def (f) id) prepass=f = 1", "f is a function and cannot be assigned"),
        ] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
        for ok in ["(def (f) egglog) pipeline=f | polish", "(def (f) rewrite | relate) sub_cluster=f", "(def @inline (g) id) (def @inline (g) rewrite) prepass=g", "(def (f) (save t) | (load t)) prepass=(save t) | f | (load t)"] {
            assert!(Passes::parse(ok).is_ok(), "{ok}");
        }
        let warn = |s: &str| Passes::parse_noting(s).unwrap().1;
        let w = warn("(def (f) rewrite) (def @inline (g) rewrite) (def (h) relate) prepass=h");
        assert!(w.len() == 2 && w[0].contains("(def (f) ...) is never used") && w[1].contains("(def @inline (g) ...) is never used"), "{w:?}");
        let w = warn("(def (f) (save t) | rewrite) prepass=f");
        assert!(w.len() == 1 && w[0].contains("f: group variable t is bound and never read"), "{w:?}");
    }

    #[test]
    fn explicit_parameters() {
        let spec = "(def @pipe (f p g) g | p) (def (twice p g) (p (p g))) (def @pipe (big k g) (size (main g)) > k) prepass=(f rewrite) | (save t) | u = (twice relate t) | (if (big 3) (load u))";
        let p = Passes::parse(spec).unwrap();
        let sigs: Vec<String> = p.defs[p.default_defs..].iter().map(|d| sig_of(d).decl()).collect();
        assert_eq!(sigs, ["(extern @pipe (f p:pipe g:group) group)", "(extern (twice p:pipe g:group) group)", "(extern @pipe (big k:num g:group) num)"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        assert!(p.to_string().contains("(def @pipe (big k g) (size (main g)) > k)"), "{p}");
        for ok in ["(def (k r:group n:num p:pipe x:name) (load r) | (fix n p) | (tag x id)) prepass=(save t) | (k t 2 id x)", "(def @pipe (big k g) (size (main g)) > k) prepass=keep = (big 3) | id"] {
            assert!(Passes::parse(ok).is_ok(), "{ok}: {:?}", Passes::parse(ok).err());
        }
        for (bad, msg) in [
            ("prepass=size | rewrite", "size gives a number; rewrite takes candidates"),
            ("(def @pipe (big k g) (size (main g)) > k) prepass=big | rewrite", "big gives a number; rewrite takes candidates"),
            ("(def @pipe (big k g) (size (main g)) > k) prepass=(big 3 (lowbits | unshift))", "big gives a number, not candidates"),
            ("(def @pipe (big k g) (size (main g)) > k) prepass=t = (big 3 (lowbits | unshift)) | (load t)", "t is a number variable, so it cannot name a group variable"),
            ("(def @pipe (big k g) size > k)", "size needs its input here"),
            ("(def @pipe (big k g) (mixed) || k)", "mixed needs its input here"),
            ("(def @pipe (f g) rewrite)", "the body of an @pipe function starts with a value"),
            ("(def @pipe (f n:num) id)", "the last parameter of an @pipe function is its input, a group"),
            ("(def @inline @pipe (f g) g | size)", "cannot be @inline"),
            ("(def (f x:bogus) id)", "unknown type bogus"),
            ("(def (f p:pipe) (fix p id))", "parameter p is used as a pipeline and as an expression"),
            ("(def (twice p g) (p (p g))) prepass=id | (twice rewrite t)", "twice is not @pipe"),
            ("(def @pipe (f p g) g | p) (def (h a:group) (f id a)) prepass=(h u)", "prepass reads group variable u before it is bound"),
            ("(def @pipe (f p g) g | p) prepass=(f id u)", "prepass reads group variable u before it is bound"),
            ("(def @pipe (f p g) g | p) prepass=(f id 1)", "f takes a pipeline"),
            ("(def @pipe (big k g) (size (main g)) > k) prepass=t = (big 3) | (load t)", "t is a number variable, so it cannot name a group variable"),
            ("(def @pipe (big k g) (size (main g)) > k) prepass=t = (k + 1)", "unknown name k"),
        ] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn pipelines_that_give_a_number() {
        let spec = "(def (f) rewrite | size) (def @pipe (h g) g | lowbits | size > 3) (def @inline @pipe (k p g) g | p | (union id g)) prepass=split_runs = (rewrite | size) | (if ((t = rewrite | size) < f) (k (t | rewrite))) | (filter (h (lowbits | unshift)))";
        let p = Passes::parse(spec).unwrap();
        let sigs: Vec<String> = p.defs[p.default_defs..].iter().map(|d| sig_of(d).decl()).collect();
        assert_eq!(sigs, ["(extern @pipe (f g:group) num)", "(extern @pipe (h g:group) num)", "(extern @pipe (k p:pipe g:group) group)"]);
        let s = p.to_string();
        for part in ["(def (f) rewrite | size)", "(def @pipe (h g) g | lowbits | size > 3)", "(def @inline @pipe (k p g) g | p | (union id g))", "split_runs = (rewrite | size)", "(if ((t = rewrite | size) < f) (k (t | rewrite)))", "(filter (h (lowbits | unshift)))"] {
            assert!(s.contains(part), "{part}: {s}");
        }
        assert_eq!(Passes::parse(&s).unwrap(), p);
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        for ok in ["prepass=(fix (rewrite | size) id)", "prepass=(if ((rewrite | size) < size) id)", "prepass=(if (any (rewrite | size) < 3) id)", "prepass=(if ((size (main (rewrite))) < (mixed (main (lowbits | unshift)))) id)", "polish=keep = (prepass | size) | id"] {
            assert!(Passes::parse(ok).is_ok(), "{ok}: {:?}", Passes::parse(ok).err());
        }
        for (bad, msg) in [
            ("prepass=(fix 3 rewrite | size)", "rewrite | size gives a number, not candidates"),
            ("prepass=rewrite | size | rewrite", "size gives a number; rewrite takes candidates"),
            ("prepass=(if ((rewrite | id) < 3) id)", "(rewrite | id) gives candidates, not a number"),
            ("(def @pipe (f g) (size (main g)) > (rewrite | size))", "(rewrite | size) needs its input here"),
            ("(def @inline (f) rewrite | size)", "cannot be @inline"),
            ("prepass=t = (rewrite | size) | (save t)", "t is a number variable, so it cannot name a group variable"),

            ("prepass=(save t) | t = 1 | (load t)", "t is a group variable, so it cannot hold a number: 1 gives a number"),
            ("prepass=keep = (lowbits | unshift)", "keep is a variable that holds a number, so it cannot be bound to candidates: (lowbits | unshift) gives candidates"),
            ("(def @pipe (f p g) g | p) prepass=(f id rewrite)", "f takes a pipeline"),
            ("prepass=(lowbits x)", "lowbits takes no arguments"),
        ] {
            let e = Passes::parse(bad).err().unwrap_or_else(|| panic!("{bad} parses"));
            assert!(e.contains(msg), "{bad}: {e}");
        }
        let warn = |s: &str| Passes::parse_noting(s).unwrap().1;
        let w = warn("prepass=(save t) | rewrite | t");
        assert!(w.len() == 1 && w[0].contains("prepass: t drops its input"), "{w:?}");
        assert!(warn("prepass=(save t) | rewrite | (load t)").is_empty(), "(load t) gives no warning");
        assert!(warn("(def @inline @pipe (k g) g | rewrite) prepass=rewrite | k").is_empty(), "nor the input of an @inline call");
        let w = warn("(def (f r) t = r | (load t)) (def (h r) r) prepass=(f rewrite) | (h id)");
        assert_eq!(w.len(), 2, "{w:?}");
        assert!(w[0].contains("(def (f r) ...): parameter r is used only where a pipeline or a group fits, so it is read as a pipeline; write r:pipe, or r:group"), "{w:?}");
        assert!(w[1].contains("(def (h r) ...): parameter r"), "{w:?}");
        assert!(warn("(def (f r:pipe) t = r | (load t)) (def (h r) (fix 2 r)) prepass=(f rewrite) | (h id)").is_empty());
    }

    #[test]
    fn def_parameters() {
        let spec = "(def (try_without name p) (best 1 p ((off name) | p))) (def (hold r p) p | (union id (load r))) prepass=(try_without relate rewrite) | (save t) | (hold t (lowbits | rewrite))";
        let p = Passes::parse(spec).unwrap();
        let sigs: Vec<String> = p.defs[p.default_defs..].iter().map(|d| sig_of(d).to_string()).collect();
        assert_eq!(sigs, ["(try_without name:name p:pipe g:group) group", "(hold r:group p:pipe g:group) group"]);
        assert_eq!(p.prepass.to_string(), "(try_without relate rewrite) | (save t) | (hold t lowbits | rewrite)");
        let Pipe::Seq(steps) = &p.prepass else { panic!() };
        let Some((c, _)) = steps[0].call() else { panic!() };
        assert_eq!(c.body.to_string(), "(best 1 p ((off relate) | p))", "a call has its name arguments in place");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(format!("{p:#}").contains("
# (hold r:group p:pipe g:group) group
(def (hold r:group p) p | (union id (load r)))
"), "{p:#}");
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let inline = Passes::parse("(def @inline (g r p) p | (load r)) prepass=(save t) | (g t rewrite) | (save u) | (g u (if (size > 1) id))").unwrap();
        assert_eq!(inline.prepass.to_string(), "(save t) | rewrite | (load t) | (save u) | (if (size > 1) id) | (load u)", "an @inline body flat in the sequence");
        let nested = Passes::parse("(def (g n q) (off n) | q) (def (h m p) (g m (p | (save x))) | (load x)) prepass=(h tfunc rewrite)").unwrap();
        let Some((h, _)) = nested.prepass.call() else { panic!() };
        let Pipe::Seq(body) = &*h.body else { panic!() };
        let Some((g, _)) = body[0].call() else { panic!() };
        assert_eq!(g.body.to_string(), "(off tfunc) | q", "a name argument passed on is put in place in the inner call too");
        for ok in [
            "(def (f a b) (load a) | (load b)) prepass=(save t) | (f t t)",
            "(def (f p) (save t) | p | (load t)) prepass=(save t) | (f ((load t) | rewrite))",
            "(def (f r) (tag r id) | (origin r id) | (smaller r id) | (egglog r)) pipeline=(f x)",
            "(def (f r) (if ((size (main r)) > 1 && (same (main r))) id) | (label r)) prepass=(save t) | (f t)",
        ] {
            assert!(Passes::parse(ok).is_ok(), "{ok}: {:?}", Passes::parse(ok).err());
        }
        for (bad, msg) in [
            ("(def (f n) (fix n n))", "parameter n is used as an expression and as a pipeline"),
            ("(def (f n) (fix n id) | (load n))", "parameter n is used as an expression and as a group variable"),
            ("(def (f n) (fix n id) | n = 1)", "parameter n cannot be assigned"),
            ("(def (g) (if (size <= n) id)) (def (f n) (fix n g))", "unknown name n in an expression"),
            ("(def (f n p) (fix n p)) prepass=(f id id)", "id gives candidates, not a number: (id g:group) group; an expression reads variables and number functions; f takes an expression and a pipeline: (f n:num p:pipe g:group) group"),
            ("(def (f n p) (fix n p)) prepass=(f 3 4)", "f takes an expression and a pipeline: (f n:num p:pipe g:group) group"),
            ("(def (f n p) (fix n p)) prepass=(f 3)", "f takes an expression and a pipeline"),
            ("(def (f r n) (load r) | (fix n id)) prepass=(f 3 3)", "expected a group variable after f, found 3"),
            ("(def (f n) (fix n id)) prepass=(f relate = 1)", "an assignment is a step"),
            ("(def (f n) (fix n id)) prepass=(f (load t))", "f takes an expression"),
            ("(def (f n) (fix n id)) prepass=(f ((size (main t)) + 1))", "prepass reads group variable t before it is bound"),
            ("(def @inline (f n) (load t) | (fix n id)) prepass=(f 1)", "prepass reads group variable t before it is bound"),
            ("(def (k r) (load r)) (def @inline (i n) (k t) | (fix n id)) prepass=(i 1)", "prepass reads group variable t before it is bound"),
            ("(def (f p) p | (load p))", "parameter p is used as a pipeline and as a group variable"),
            ("(def (f r) (load r) | (tag r id))", "parameter r is used as a group variable and as a name"),
            ("(def (f p q) p)", "def (f p q): parameter q is never used in the body"),
            ("(def (f r) r = 1)", "parameter r cannot be assigned"),
            ("(def (f relate) id)", "parameter relate is the name of a variable, function or definition"),
            ("(def (f rewrite) id)", "the name of a variable, function or definition"),
            ("(def (f gates) id)", "the name of a variable, function or definition"),
            ("(def (f p p) p)", "parameter p is written twice"),
            ("(def (f f) id)", "parameter f is written twice"),
            ("(def (prepass p) p)", "takes no parameters"),
            ("(def (f p) (p id))", "parameter p takes a group value: (p g)"),
            ("(def (f p) p) prepass=f", "f needs parentheses: (f ...); (f p:pipe g:group) group"),
            ("(def (f p) p) prepass=(f)", "f takes a pipeline: (f p:pipe g:group) group"),
            ("(def (f p) p) prepass=(f id id)", "f takes a pipeline: (f p:pipe g:group) group"),
            ("(def (f r p) (load r) | p) prepass=(f (id) id)", "expected a group variable after f, found ("),
            ("(def (f r p) (load r) | p) prepass=(f t)", "f takes a group variable and a pipeline: (f r:group p:pipe g:group) group"),
            ("(def (f n p) (off n) | p) prepass=(f nope id)", "unknown off name nope (the argument for n)"),
            ("(def (f p) p) prepass=(if f id)", "f gives candidates, not a number: (f p:pipe g:group) group"),
            ("(def (f p) p) prepass=f = 1", "f is a function and cannot be assigned: (f p:pipe g:group) group"),
            ("(def (f r) (load r)) prepass=(f t)", "prepass reads group variable t before it is bound"),
            ("(def (f a b) (load a) | (load b)) prepass=(save t) | (f t u)", "prepass reads group variable u before it is bound"),
            ("(def (f a) (save a))", "parameter a cannot be assigned"),
            ("(def (f a) a = rewrite)", "parameter a cannot be assigned"),
            ("(def (f p) id | p) prepass=(f (load t))", "prepass reads group variable t before it is bound"),
            ("(def (g p) p) prepass=(g prepass)", "prepass reaches itself"),
            ("(def (g p) p | polish) polish=(g id)", "polish reaches itself"),
            ("(def (g p) p) (def (h q) (g q)) prepass=(h (if mixed prepass))", "prepass reaches itself"),
            ("(def (g p) p) prepass=(g egglog)", "egglog needs a simplify run and cannot be in prepass"),
            ("(def @inline (g p) p) prepass=(g egglog)", "egglog needs a simplify run and cannot be in prepass"),
        ] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains(msg), "{bad}: {e}");
        }
        let warn = |s: &str| Passes::parse_noting(s).unwrap().1;
        let w = warn("(def (f p) (save t) | p) prepass=(f id)");
        assert!(w.len() == 1 && w[0].contains("f: group variable t is bound and never read"), "{w:?}");
        let w = warn("(def (f p:pipe) p) (def @inline (g p:pipe) p) prepass=id");
        assert!(w.len() == 2 && w[0].contains("(def (f p) ...) is never used") && w[1].contains("(def @inline (g p) ...) is never used"), "{w:?}");
        let w = warn("(def (f p n) (fix n p)) prepass=id");
        assert!(w.len() == 1 && w[0].contains("(def (f p n) ...) is never used"), "{w:?}");
        let w = warn("(def @inline (f n) (save s) | (fix n id)) prepass=(f 2) | rewrite");
        assert!(w.len() == 1 && w[0].contains("prepass: group variable s is bound and never read"), "an @inline body is checked where it is called: {w:?}");
        let w = warn("(def @inline (f n) split_runs = n) prepass=rewrite | (f 2)");
        assert!(w.len() == 1 && w[0].contains("prepass: split_runs = n ends its sequence"), "{w:?}");
    }

    #[test]
    fn numeric_parameters() {
        let spec = "(def (with_budget n p) rewrites = n | p) (def (if_small k p) (if (size <= k) p)) (def (g q) q | rewrite)             (def (f n) (if_small (n * 2) (g ((filter (size <= n)) | (with_budget (n + 1) rewrite)))))             (def @inline (lim n p) split_runs = n | p) (def @inline (lim2 n p) (split_runs = n | p))             prepass=(f 3) | (lim none id) | (lim2 (size - 1) (with_budget 8 rewrite))";
        let p = Passes::parse(spec).unwrap();
        let sigs: Vec<String> = p.defs[p.default_defs..].iter().map(|d| sig_of(d).to_string()).collect();
        assert_eq!(sigs[0], "(with_budget n:num p:pipe g:group) group");
        assert_eq!(sigs[3], "(f n:num g:group) group");
        assert_eq!(sigs[4], "(lim n:num p:pipe g:group) group", "an @inline function with a numeric parameter is a function too");
        assert_eq!(p.prepass.to_string(), "(f 3) | (lim none id) | (lim2 (size - 1) (with_budget 8 rewrite))");
        assert!(p.to_string().contains(" (def @inline (lim n p) split_runs = n | p) (def @inline (lim2 n p) (split_runs = n | p)) "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let plain = Passes::parse("(def @inline (g p) p | relate) prepass=(g rewrite)").unwrap();
        assert!(plain.defs.len() == plain.default_defs, "an @inline function without a numeric parameter is expanded");
    }
}
