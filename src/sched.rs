//! The pass pipeline of `simplify`: the egglog schedule of a round, which pre-pass candidates
//! are built, how the rounds run and which polish passes run in what order. `Passes::default()` is the tuned pipeline;
//! `--passes` changes it with a spec such as `pre-=halve_input polish=push_not,factor extra=0`.

use crate::pipe_lang as lang;
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
/// one of several alternatives gives no form. Each is an `extern @switch` of `builtins.pipe`
/// or, with a `/`, a part of one (`DEFAULT` checks this).
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

/// Switches besides the `INNER` passes: `cut` (off unless turned on: a step skipped past a
/// `time_limit` makes the run cut, `crate::pipe::cut`), `rerun_input` (rerun the first round
/// with the input when its result still mixes arithmetic into bitwise operations),
/// `prove_minimal` (take a rebuild proved minimal as the extraction without saturating),
/// `relate_parts` (`relate` on parts of a region wider than `relate_leaves`).
pub const FLAGS: [&str; 4] = ["cut", "rerun_input", "prove_minimal", "relate_parts"];

/// The `INNER` pass or `FLAGS` switch named `name`, which `(on NAME)` and `(off NAME)` take.
pub fn switch(name: &str) -> Option<&'static str> {
    INNER.iter().chain(&FLAGS).find(|k| **k == name).copied()
}

macro_rules! limits {
    ($($(#[doc = $doc:literal])* $id:ident $name:literal;)*) => {
        /// Numeric limits and constants of the passes, defined in `default.pipe`.
        #[derive(Clone, Copy, Debug, PartialEq)]
        pub enum Limit {
            $($(#[doc = $doc])* $id,)*
        }
        /// Names of the `Limit`s, in order.
        pub const LIMITS: &[&str] = &[$($name,)*];
    };
}

limits! {
    /// Most `rewrite` calls of the other rebuilds after which the one without `clustered`
    /// is still tried: inputs that need more are slow to rebuild without it.
    UnclusteredAfter "unclustered_after";
    /// Most combinations `related_leaves` rebuilds.
    RelatedRebuilds "related_rebuilds";
    /// Most arithmetic leaves `relate_region` tries.
    Related "related";
    /// Most leaf splits `bit_split` rebuilds per region.
    BitSplits "bit_splits";
    /// Most `P op Q` pairs `bit_split` rebuilds per pre-pass candidate: `cand` sets
    /// the budget `bit_split_budget` to it.
    CandBitSplits "cand_bit_splits";
    /// Most variable bits `split_bits` tries on one term.
    Splits "splits";
    /// How deep `split_bits` nests.
    SplitDepth "split_depth";
    /// Most rebuilds one `split_bits` call runs.
    SplitRuns "split_runs";
    /// Largest first rebuild `split_bits` runs on.
    SplitSize "split_size";
    /// Most leaves `small_blocks` handles.
    BlockLeaves "block_leaves";
    /// Most combinations of block choices `small_blocks` tries exhaustively, and steps of
    /// the `wide_blocks` search.
    BlockCombos "block_combos";
    /// `small_blocks`: most leaves of one block; it interpolates from the points with at most
    /// this many ones and tries every table of a block, `2^(2^k)` of them.
    BlockMaxBlock "block_max_block";
    /// `small_blocks`: rounds of coordinate descent when the combinations are too many to try.
    BlockDescentRounds "block_descent_rounds";
    /// `small_blocks`: spread-out points checked first in the full check, which rejects most
    /// regions sooner; changes no result.
    BlockSpreadPoints "block_spread_points";
    /// Most `clustered` calls nested inside each other.
    ClusterDepth "cluster_depth";
    /// Most products `poly_mba` builds with every choice before it keeps to the first.
    PolyBuilds "poly_builds";
    /// Expansions with more monomials than this keep to the first choice at each level
    /// from the start, as after `poly_builds` products.
    PolyBranchMonos "poly_branch_monos";
    /// Rebuilds of at most this size are not searched further: the input is not halved, and
    /// the driver does not saturate the input beside them (the conditions `tiny`, `opaque`).
    TinySize "tiny_size";
    /// Most leaves of a linear region rebuilt from its values on {0,1}^n; truth tables are
    /// `u64`.
    MaxLeaves "max_leaves";
    /// Most leaves of a wide region evaluated whole (`used_leaves`, `relate`, `peel`); the
    /// used leaves are a `u64` mask.
    MaxWideLeaves "max_wide_leaves";
    /// `lowbits`: most leaf bits enumerated for one subterm.
    LowbitsMaxBits "lowbits_max_bits";
    /// `lowbits`: most leaf bits enumerated for a proof in context.
    LowbitsMaxContextBits "lowbits_max_context_bits";
    /// `lowbits`: proofs over more leaf bits than this also draw on `lowbits_wide_budget`.
    LowbitsNarrowContextBits "lowbits_narrow_context_bits";
    /// `lowbits`: largest subterm enumerated or proved in context.
    LowbitsMaxTry "lowbits_max_try";
    /// `lowbits`: most distinct values of a subterm replaced by one of them in context.
    LowbitsMaxValues "lowbits_max_values";
    /// `lowbits`: without a variable shift, only subterms with a product whose value is
    /// fixed by this many low bits of the leaves are enumerated.
    LowbitsMaxProductBits "lowbits_max_product_bits";
    /// `lowbits`: evaluation steps per call, over all enumerations.
    LowbitsBudget "lowbits_budget";
    /// `lowbits`: evaluation steps of the proofs over more than `lowbits_narrow_context_bits` bits.
    LowbitsWideBudget "lowbits_wide_budget";
    /// `lowbits`: largest product factor `shorter_low` rebuilds after cutting its constants.
    LowbitsMaxLowRebuild "lowbits_max_low_rebuild";
    /// `lowbits`: low bits `refine_low` enumerates past the known ones.
    LowbitsRefineBits "lowbits_refine_bits";
    /// `lowbits`: most leaf bits `refine_low` enumerates in all.
    LowbitsMaxRefineBits "lowbits_max_refine_bits";
    /// `lowbits`: evaluation steps of `refine_low` per call.
    LowbitsRefineBudget "lowbits_refine_budget";
    /// `lowbits`: most terms of a factor that `over_products` multiplies out.
    LowbitsMaxFactorTerms "lowbits_max_factor_terms";
    /// `poly_mba`: most monomials of a product it multiplies out.
    PolyMaxMonos "poly_max_monos";
    /// `poly_mba`: expansions with more monomials per node of the term are not rebuilt.
    PolyMonosPerNode "poly_monos_per_node";
    /// `poly_mba`: candidate factors pulled out at the top level of a rebuild (one below it).
    PolyFactorTries "poly_factor_tries";
    /// `poly_mba`: most monomials of a polynomial factored, and of one rebuilt again from its
    /// null-reduced form.
    PolyMaxFactorMonos "poly_max_factor_monos";
    /// `poly_mba`: most conjunctions of a polynomial factored.
    PolyMaxFactorVars "poly_max_factor_vars";
    /// `poly_mba`: most pivot conjunctions a factoring tries.
    PolyMaxPivots "poly_max_pivots";
    /// `poly_mba`: past this many roots of a coefficient equation only the likely ones are kept.
    PolyMaxRoots "poly_max_roots";
    /// `poly_mba`: most root combinations a factoring tries.
    PolyMaxFactorSteps "poly_max_factor_steps";
    /// `poly_mba`: most factorings one pivot gives.
    PolyMaxSolutions "poly_max_solutions";
    /// `poly_mba`: most factorings shifted by constants beside the linear rest.
    PolyMaxShifted "poly_max_shifted";
    /// `poly_mba`: most monomials of a shifted factor.
    PolyMaxShiftedMonos "poly_max_shifted_monos";
    /// `poly_mba`: the linear rest beside a shifted factoring has at most this many times
    /// `poly_max_shifted_monos` monomials.
    PolyShiftedRestRatio "poly_shifted_rest_ratio";
    /// `poly_mba`: most bit sets the masked expansion splits the width into.
    PolyMaxAtoms "poly_max_atoms";
    /// `poly_mba`: most monomials of the masked expansion (or `poly_masked_monos_ratio` times
    /// the plain one's).
    PolyMaxMaskedMonos "poly_max_masked_monos";
    /// `poly_mba`: the masked expansion may also have this many times the plain one's monomials.
    PolyMaskedMonosRatio "poly_masked_monos_ratio";
    /// `poly_mba`: largest term the masked expansion rebuilds for a single product with
    /// constants in both factors.
    PolyMaxMaskedSize "poly_max_masked_size";
    /// `common_multiple`: smallest `|c|` pulled out.
    CommonMultipleMin "common_multiple_min";
    /// `common_multiple`: most values of `c` tried.
    CommonMultipleTries "common_multiple_tries";
    /// `overlapping_terms`: most distinct non-zero values of a table it searches.
    OverlapMaxValues "overlap_max_values";
    /// `overlapping_terms`: most ways tried to resolve points whose value is the sum of
    /// several subsets of the coefficients.
    OverlapMaxChoices "overlap_max_choices";
    /// `overlapping_terms`: most bitwise terms of a sum it searches.
    OverlapMaxTerms "overlap_max_terms";
    /// `related_leaves`: most arithmetic leaves related to the region's other leaves.
    RelatedLeavesMaxArith "related_leaves_max_arith";
    /// `relate`: most further arithmetic leaves tried that the region also has written out.
    RelateMaxWrittenOut "relate_max_written_out";
    /// `relate`: largest product leaf tried when it is not an operand of a bitwise operation.
    RelateMaxFreeProduct "relate_max_free_product";
    /// `relate`: most arithmetic leaves `relate_parts` tries.
    RelateMaxParts "relate_max_parts";
    /// `relate`: in a wide region where no leaf or term cancelled, a result is kept only at
    /// most this percent of the region's size.
    RelateWideMaxPercent "relate_wide_max_percent";
    /// `unify_operands`: most leaves of an arithmetic operand compared by its values.
    UnifyOperandsMaxLeaves "unify_operands_max_leaves";
    /// `join_constants`: most leaves of two leaf groups rebuilt together with the constant.
    JoinConstantsMaxLeaves "join_constants_max_leaves";
    /// `join_constants`: most rebuilds with the constant per region.
    JoinConstantsMaxSets "join_constants_max_sets";
    /// `join_linear`: most leaf groups of a region it moves leaves between.
    JoinLinearMaxGroups "join_linear_max_groups";
    /// `join_linear`: most nodes a move may add and still be followed by a second one.
    JoinLinearNearSlack "join_linear_near_slack";
    /// `join_linear`: most such moves followed by a second one.
    JoinLinearNearMoves "join_linear_near_moves";
    /// `join_linear`: most leaf groups of a region where moves are followed by a second one.
    JoinLinearMaxNearGroups "join_linear_max_near_groups";
    /// `shift_cases`: most variable shift amounts split on, nested.
    ShiftCasesDepth "shift_cases_depth";
    /// `shift_cases`: largest term it runs on (it rebuilds up to `2w` cases per amount).
    ShiftCasesMaxSize "shift_cases_max_size";
    /// `shift_cases`: most variable shift amounts split on at each level.
    ShiftCasesAmounts "shift_cases_amounts";
    /// Most variables of a truth table split as `g(A) op h(B)` (`decompose`) when its
    /// shortest bitwise expression is looked for.
    DecomposeMaxVars "decompose_max_vars";
    /// `decompose`: smallest size to beat for which it also fills free points.
    DecomposeMinFreeSize "decompose_min_free_size";
    /// `decompose`: most classes of free points enumerated for one side.
    DecomposeMaxFreeClasses "decompose_max_free_classes";
    /// `decompose`: most variables of a side whose free points are filled.
    DecomposeFillMaxVars "decompose_fill_max_vars";
    /// `decompose`: most variables shared by the sides of a `^` that a function of them is
    /// XORed into.
    DecomposeXorMaxShared "decompose_xor_max_shared";
    /// Most results one key of the `rewrite`, `simba_memo` and `relate` memos keeps, the
    /// oldest dropped first.
    MemoContexts "memo_contexts";
    /// Most instructions times points a wide region is evaluated on {0,1}^n (`used_leaves`,
    /// `peel`).
    UsedLeavesBudget "used_leaves_budget";
    /// `peel`: least size per leaf of a region it tries.
    PeelMinSize "peel_min_size";
    /// `peel`: spread-out points at which a region must look bitwise before its bit tables
    /// are built.
    PeelSpreadPoints "peel_spread_points";
    /// `wide_blocks`: most leaves of one term it expands; points are counted in a `usize`.
    WideBlocksMaxTermLeaves "wide_blocks_max_term_leaves";
    /// `wide_blocks`: most leaves of one block rebuilt as one term.
    WideBlocksMaxBlock "wide_blocks_max_block";
    /// `wide_blocks`: search steps per block and multiplier for the tables of a block.
    WideBlocksSteps "wide_blocks_steps";
    /// `wide_blocks`: most tables collected per block of at most 6 leaves.
    WideBlocksMaxTables "wide_blocks_max_tables";
    /// `wide_blocks`: most tables collected per block of more leaves (split by disjoint
    /// decomposition, which is slow).
    WideBlocksMaxWideTables "wide_blocks_max_wide_tables";
    /// `wide_blocks`: most of the smallest tables per block kept for the search over blocks.
    WideBlocksMaxFunctions "wide_blocks_max_functions";
    /// `wide_blocks`: most regions its thread cache keeps before it is cleared.
    WideBlocksCacheSize "wide_blocks_cache_size";
    /// `wide_blocks`: rounds of coordinate descent before the branch and bound.
    WideBlocksDescentRounds "wide_blocks_descent_rounds";
    /// `wide_blocks`: a region less than this many times its blocks' least term sizes is
    /// skipped, as mostly in block form already.
    WideBlocksMinRatio "wide_blocks_min_ratio";
    /// Largest bitwise expression with free constants `semi/shapes` and `semi/pairs` search;
    /// the table of level 15 takes about 100 MB.
    ShapesMaxSize "shapes_max_size";
    /// `semi/pairs`: most bit groups of a region.
    PairsMaxGroups "pairs_max_groups";
    /// `semi/pairs`: most shape entries checked per call.
    PairsBudget "pairs_budget";
    /// `semi/pairs`: largest total size of the two shapes.
    PairsMaxSize "pairs_max_size";
    /// `semi/pairs`: most coefficients tried, the smallest first.
    PairsMaxScales "pairs_max_scales";
    /// `semi/pairs`: most carries per bit of the carry DP before it gives up.
    PairsMaxCarries "pairs_max_carries";
    /// `semi/semi_split`: most combinations of the other sets' constants per set.
    SemiSplitMaxCombos "semi_split_max_combos";
    /// `semi_linear`: most groups whose `-2^(r-1)` entries are also read as `+2^(r-1)`.
    SemiHalfFlips "semi_half_flips";
    /// `semi_linear`: most variants of the groups joined by their high bits enumerated.
    SemiMaxMerges "semi_max_merges";
    /// `semi_linear`: most bit groups encoded by constant leaves (every code assignment tried).
    SemiMaxCodeGroups "semi_max_code_groups";
    /// `split_bits`: most unknown bits of a factor that selects a product.
    SplitMaxUnknownBits "split_max_unknown_bits";
    /// `tfunc`: most variables (or bitwise atoms) of a subterm looked up; the points are a
    /// fixed array.
    TfuncMaxVars "tfunc_max_vars";
    /// `tfunc`: largest expression of its lookup table.
    TfuncMaxSize "tfunc_max_size";
    /// `tfunc`: points a subterm is evaluated at for the lookup; the values are a fixed array.
    TfuncPoints "tfunc_points";
    /// `tfunc`: largest subterm tried; larger ones are rarely replaceable and costly to prove.
    TfuncMaxTry "tfunc_max_try";
    /// T-function proofs (`tfunc`, `lowbits`): most carries; the carry state is a `u128`.
    TfuncMaxCarries "tfunc_max_carries";
    /// T-function proofs: most reachable carry states per bit before giving up.
    TfuncMaxStates "tfunc_max_states";
    /// T-function proofs: largest constant multiplier (or its negation) expanded into adders.
    TfuncMaxFactor "tfunc_max_factor";
    /// Minimality proofs: points a term and the smaller ones are compared at.
    MinimalPoints "minimal_points";
    /// Minimality proofs over `+ - * & | ^ ~ neg`: points of the low-bit value vectors, a
    /// fixed array.
    MinimalLanes "minimal_lanes";
    /// Minimality proofs over `+ - * & | ^ ~ neg`: most pairs of terms combined.
    MinimalBudget "minimal_budget";
    /// Minimality proofs by enumeration: most variables of a term of more than `2k - 1` nodes;
    /// variable sets are a `u32`.
    MinimalMaxVars "minimal_max_vars";
    /// Minimality proofs over `+ - * & | ^ ~ neg`: largest term proved in 4 bits.
    MinimalMaxSize4bit "minimal_max_size_4bit";
    /// Minimality proofs over `+ - * & | ^ ~ neg`: largest term proved in 8 bits.
    MinimalMaxSize8bit "minimal_max_size_8bit";
}

/// The limits read only for the size of a cache, which changes no result: not recorded as
/// read (`limit_unread`), also where a pipeline reads them.
pub const UNREAD: [Limit; 2] = [Limit::MemoContexts, Limit::WideBlocksCacheSize];

/// Variables besides the limits: `rewrites` (uncached `rewrite` calls left), `semi_leaves`
/// (most leaves of a semi-linear region rebuilt), `relate_leaves` (most leaves of a region
/// `relate` tries), `bit_split_budget` (`bit_split` pairs left).
pub const SETTINGS: [&str; 4] = ["rewrites", "semi_leaves", "relate_leaves", "bit_split_budget"];

/// Settings of a run the Rust code reads: `keep` (pre-pass rebuilds unioned into a round,
/// read as at least 1), `match_limit` and `ban_length` (the back-off scheduler of the next
/// egglog round), `restarts` (`-m`) and `iter_limit` (`-i`, schedule repetitions of an egglog
/// round).
pub const RUN: [&str; 5] = ["keep", "match_limit", "ban_length", "restarts", "iter_limit"];

/// How the Rust code uses a variable, which decides how a binding combines with the outer
/// ones.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum VarKind {
    /// An `INNER` pass: 0 off, any other value (also `none`) on.
    Pass,
    /// A `FLAGS` switch: 0 off, any other value (also `none`) on.
    Flag,
    /// An entry of `LIMITS`.
    Limit,
    /// An entry of `UNREAD`.
    Unread,
    /// `semi_leaves`, `relate_leaves` and the `RUN` settings.
    Setting,
    /// `rewrites`, `bit_split_budget`: a binding is at most what the outer one has left, and
    /// what is used inside is used up outside too.
    Budget,
    /// `time_limit`, a deadline in ns of `epoch_ns`: a binding is never later than the outer
    /// one.
    Deadline,
    /// A variable a source file defines that the Rust code does not read.
    Global,
}

/// A variable of the runs on this thread: one the Rust code reads (an `INNER` pass, a `FLAGS`
/// switch, a `LIMITS` entry, a `SETTINGS` entry, a `RUN` setting or the deadline, at a fixed
/// position below `RUST_VARS`), or one only the pipelines read.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Var {
    pub name: &'static str,
    pub kind: VarKind,
}

const FLAG0: usize = INNER.len();
const LIMIT0: usize = FLAG0 + FLAGS.len();
const SETTING0: usize = LIMIT0 + LIMITS.len();
pub const REWRITES: usize = SETTING0;
pub const SEMI_LEAVES: usize = SETTING0 + 1;
pub const RELATE_LEAVES: usize = SETTING0 + 2;
pub const BIT_SPLIT_BUDGET: usize = SETTING0 + 3;
const RUN0: usize = SETTING0 + SETTINGS.len();
pub const CUT: usize = FLAG0;
pub const RERUN_INPUT: usize = FLAG0 + 1;
pub const PROVE_MINIMAL: usize = FLAG0 + 2;
pub const KEEP: usize = RUN0;
pub const MATCH_LIMIT: usize = RUN0 + 1;
pub const BAN_LENGTH: usize = RUN0 + 2;
pub const RESTARTS: usize = RUN0 + 3;
pub const ITER_LIMIT: usize = RUN0 + 4;
pub const DEADLINE: usize = RUN0 + RUN.len();
/// The variables the Rust code reads; those the source files define besides follow them.
pub const RUST_VARS: usize = DEADLINE + 1;
/// The read bit that stands for all the `LIMITS` (`limits_key`).
const LIMITS_BIT: usize = RUST_VARS;
/// The read bit that stands for all the variables past `RUST_VARS` (`globals_hash`).
const GLOBALS_BIT: usize = RUST_VARS + 1;
const READ_WORDS: usize = (RUST_VARS + 2).div_ceil(64);

/// A set of variables below `RUST_VARS`, `LIMITS_BIT` and `GLOBALS_BIT`, as the memos record
/// what a computation read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReadSet([u64; READ_WORDS]);

impl ReadSet {
    pub const EMPTY: ReadSet = ReadSet([0; READ_WORDS]);

    pub fn union(mut self, o: ReadSet) -> ReadSet {
        self.0.iter_mut().zip(o.0).for_each(|(a, b)| *a |= b);
        self
    }

    pub fn remove(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }

    fn ones(self) -> impl Iterator<Item = usize> {
        self.0.into_iter().enumerate().flat_map(|(k, mut bits)| {
            std::iter::from_fn(move || {
                let i = bits.trailing_zeros() as usize;
                bits &= bits.wrapping_sub(1);
                (i < 64).then_some(k * 64 + i)
            })
        })
    }
}

/// `none`, no limit: the value of every variable until it is assigned.
pub const NONE: u64 = u64::MAX;

const fn is_unread(i: usize) -> bool {
    let mut k = 0;
    while k < UNREAD.len() {
        if LIMIT0 + UNREAD[k] as usize == i {
            return true;
        }
        k += 1;
    }
    false
}

/// The name and kind of the variable at position `i` below `RUST_VARS`.
const fn rust_var(i: usize) -> (&'static str, VarKind) {
    match i {
        _ if i < FLAG0 => (INNER[i], VarKind::Pass),
        _ if i < LIMIT0 => (FLAGS[i - FLAG0], VarKind::Flag),
        _ if i < SETTING0 && is_unread(i) => (LIMITS[i - LIMIT0], VarKind::Unread),
        _ if i < SETTING0 => (LIMITS[i - LIMIT0], VarKind::Limit),
        _ if i == SEMI_LEAVES || i == RELATE_LEAVES => (SETTINGS[i - SETTING0], VarKind::Setting),
        _ if i < RUN0 => (SETTINGS[i - SETTING0], VarKind::Budget),
        _ if i < DEADLINE => (RUN[i - RUN0], VarKind::Setting),
        _ => ("time_limit", VarKind::Deadline),
    }
}

/// The kind of the variable at position `i`.
pub fn kind(i: usize) -> VarKind {
    if i < RUST_VARS { rust_var(i).1 } else { VarKind::Global }
}

/// The names of the variables past `RUST_VARS`, in the order the source files first defined
/// them in this process; each keeps its position.
static GLOBALS: std::sync::RwLock<Vec<&'static str>> = std::sync::RwLock::new(Vec::new());

/// The number of variables with a position so far.
fn count() -> usize {
    RUST_VARS + GLOBALS.read().unwrap().len()
}

/// The variable at position `i`.
pub fn var(i: usize) -> Var {
    let name = if i < RUST_VARS { rust_var(i).0 } else { GLOBALS.read().unwrap()[i - RUST_VARS] };
    Var { name, kind: kind(i) }
}

thread_local! {
    /// The variables past `RUST_VARS` that the source files of the parse under way on this
    /// thread define (`Passes::globals`), while one is.
    static PARSED: std::cell::RefCell<Option<Vec<usize>>> = const { std::cell::RefCell::new(None) };
}

/// The position of the variable `name`: one the Rust code reads, or one that `default.pipe` or
/// the source files of the parse under way define.
pub fn var_index(name: &str) -> Option<usize> {
    if let Some(i) = (0..RUST_VARS).find(|i| rust_var(*i).0 == name) {
        return Some(i);
    }
    let i = GLOBALS.read().unwrap().iter().position(|n| *n == name)? + RUST_VARS;
    match PARSED.with(|p| p.borrow().as_ref().map(|g| g.contains(&i))) {
        Some(found) => found.then_some(i),
        None => DEFAULT.0.globals.contains(&i).then_some(i),
    }
}

/// `f` with the variables `globals` defined for `var_index`, as a parse that defines them sees
/// them; `f` may add more.
fn parsing<R>(globals: &mut Vec<usize>, f: impl FnOnce() -> R) -> R {
    let outer = PARSED.with(|p| p.replace(Some(std::mem::take(globals))));
    let r = f();
    *globals = PARSED.with(|p| p.replace(outer)).unwrap_or_default();
    r
}

/// The position of a variable past `RUST_VARS` named `name`, given one when it has none, and
/// recorded as defined by the parse under way.
fn global_slot(name: &str) -> usize {
    let i = {
        let mut g = GLOBALS.write().unwrap();
        match g.iter().position(|n| *n == name) {
            Some(i) => RUST_VARS + i,
            None => {
                g.push(lang::intern(name));
                RUST_VARS + g.len() - 1
            }
        }
    };
    PARSED.with(|p| p.borrow_mut().get_or_insert_with(Vec::new).push(i));
    i
}

/// The names of all variables `var_index` finds, in order.
pub fn var_names() -> Vec<&'static str> {
    (0..count()).map(|i| var(i).name).filter(|n| var_index(n).is_some()).collect()
}

/// Whether the variable at `i` is a switch: an `INNER` pass or a `FLAGS` switch.
pub fn is_switch(i: usize) -> bool {
    matches!(kind(i), VarKind::Pass | VarKind::Flag)
}

thread_local! {
    /// The current value of each variable. Shallow binding: `bind` keeps the outer value in
    /// the innermost scope of `FRAMES`, which puts it back when it ends.
    static VARS: [std::cell::Cell<u64>; RUST_VARS] = const { [const { std::cell::Cell::new(NONE) }; RUST_VARS] };
    /// The values of the variables past `RUST_VARS`, by position less `RUST_VARS`; `none`
    /// past the end.
    static GLOBAL_VALS: std::cell::RefCell<Vec<u64>> = const { std::cell::RefCell::new(Vec::new()) };
    /// A hash of `GLOBAL_VALS`, made when first needed after a `set` of one of them.
    static GLOBALS_HASH: std::cell::Cell<Option<u64>> = const { std::cell::Cell::new(None) };
    /// A hash of the values of the `LIMITS`, kept up to date by `set`.
    static LIMITS_HASH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The scopes under way, innermost last: each variable bound there, its value outside and
    /// the value bound.
    static FRAMES: std::cell::RefCell<Vec<Vec<(usize, u64, u64)>>> = const { std::cell::RefCell::new(Vec::new()) };
    /// Bits of the variables read since the last `swap_read`.
    static READ: [std::cell::Cell<u64>; READ_WORDS] = const { [const { std::cell::Cell::new(0) }; READ_WORDS] };
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

/// The value of variable `i`, not recorded as read.
pub fn get(i: usize) -> u64 {
    if i < RUST_VARS { VARS.with(|v| v[i].get()) } else { GLOBAL_VALS.with(|g| g.borrow().get(i - RUST_VARS).copied().unwrap_or(NONE)) }
}

/// The value of variable `i`, recorded as read for the memos (`swap_read`).
pub fn read(i: usize) -> u64 {
    mark_read(if i < RUST_VARS { i } else { GLOBALS_BIT });
    get(i)
}

/// `read` for a pipeline: the `UNREAD` limits are not recorded.
pub fn read_var(i: usize) -> u64 {
    if is_unread(i) { get(i) } else { read(i) }
}

fn mark_read(i: usize) {
    READ.with(|r| {
        let c = &r[i / 64];
        c.set(c.get() | 1 << (i % 64));
    });
}

/// Sets variable `i` outside any binding: a scope that binds it later restores this value.
pub fn set(i: usize, v: u64) {
    if i >= RUST_VARS {
        GLOBAL_VALS.with(|g| {
            let mut g = g.borrow_mut();
            let k = i - RUST_VARS;
            if k >= g.len() {
                g.resize(k + 1, NONE);
            }
            g[k] = v;
        });
        GLOBALS_HASH.with(|c| c.set(None));
        return;
    }
    VARS.with(|a| {
        a[i].set(v);
        if (LIMIT0..SETTING0).contains(&i) {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            a[LIMIT0..SETTING0].iter().for_each(|c| c.get().hash(&mut h));
            LIMITS_HASH.with(|c| c.set(h.finish()));
        }
    });
}

/// Binds variable `i` to `v` in the innermost scope (`in_scope`) until it ends; a budget is
/// at most what the outer binding has left, a deadline no later than the outer one.
pub fn bind(i: usize, v: u64) {
    let cur = get(i);
    let kind = kind(i);
    let new = FRAMES.with(|f| {
        let mut f = f.borrow_mut();
        let Some(frame) = f.last_mut() else { return v };
        let slot = frame.iter().position(|e| e.0 == i);
        let outer = match slot {
            Some(s) if kind == VarKind::Budget => {
                let e = &mut frame[s];
                e.1 = e.1.saturating_sub(e.2.saturating_sub(cur));
                e.1
            }
            Some(s) => frame[s].1,
            None => cur,
        };
        let new = match kind {
            VarKind::Budget | VarKind::Deadline => v.min(outer),
            _ => v,
        };
        match slot {
            Some(s) => frame[s].2 = new,
            None => frame.push((i, cur, new)),
        }
        new
    });
    set(i, new);
}

/// Takes one from the budget `i`; false when it is used up.
pub fn take(i: usize) -> bool {
    let left = get(i);
    set(i, left.saturating_sub(1));
    left > 0
}

/// `f` as a scope: the variables bound inside it are back after, a budget less what was
/// used inside.
pub fn in_scope<R>(f: impl FnOnce() -> R) -> R {
    FRAMES.with(|fr| fr.borrow_mut().push(Vec::new()));
    let r = f();
    let frame = FRAMES.with(|fr| fr.borrow_mut().pop()).unwrap_or_default();
    for (i, old, bound) in frame {
        let back = match kind(i) {
            VarKind::Budget => old.saturating_sub(bound.saturating_sub(get(i))),
            _ => old,
        };
        set(i, back);
    }
    r
}

/// The variables read since the last call, which sets them to `v`.
pub fn swap_read(v: ReadSet) -> ReadSet {
    READ.with(|r| ReadSet(std::array::from_fn(|k| r[k].replace(v.0[k]))))
}

/// The values of the variables in `bits`, in order.
pub fn values(bits: ReadSet) -> Vec<u64> {
    VARS.with(|a| bits.ones().map(|i| value_at(a, i)).collect())
}

/// Whether the variables in `bits` have the values `vals` (`values`).
pub fn same_values(bits: ReadSet, vals: &[u64]) -> bool {
    VARS.with(|a| bits.ones().zip(vals).all(|(i, v)| value_at(a, i) == *v))
}

fn value_at(a: &[std::cell::Cell<u64>; RUST_VARS], i: usize) -> u64 {
    match i {
        LIMITS_BIT => LIMITS_HASH.with(|c| c.get()),
        GLOBALS_BIT => globals_hash(),
        _ => a[i].get(),
    }
}

/// A hash of the values of the variables past `RUST_VARS` on this thread.
fn globals_hash() -> u64 {
    GLOBALS_HASH.with(|c| {
        if let Some(v) = c.get() {
            return v;
        }
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        GLOBAL_VALS.with(|g| g.borrow().iter().enumerate().filter(|(_, v)| **v != NONE).for_each(|e| e.hash(&mut h)));
        let v = h.finish();
        c.set(Some(v));
        v
    })
}

/// The values of all variables but the budgets and the deadline, which a result depends on
/// only where they cut it short.
pub fn key() -> Vec<u64> {
    (0..count()).filter(|i| !matches!(kind(*i), VarKind::Budget | VarKind::Deadline)).map(get).collect()
}

/// A hash of the `LIMITS` on this thread, for the key of a memo that may depend on any of
/// them; recorded as a read of all of them.
pub fn limits_key() -> u64 {
    mark_read(LIMITS_BIT);
    LIMITS_HASH.with(|c| c.get())
}

/// Nanoseconds since the first call in the process, the unit of `DEADLINE`.
pub fn epoch_ns() -> u64 {
    static EPOCH: std::sync::LazyLock<std::time::Instant> = std::sync::LazyLock::new(std::time::Instant::now);
    EPOCH.elapsed().as_nanos() as u64
}

/// The value of `l` on this thread; `none` is `usize::MAX`.
pub fn limit(l: Limit) -> usize {
    read(LIMIT0 + l as usize) as usize
}

/// `limit` not recorded as read, for a value that changes no result (an `UNREAD` entry).
pub fn limit_unread(l: Limit) -> usize {
    debug_assert!(is_unread(LIMIT0 + l as usize), "{} is not in UNREAD", LIMITS[l as usize]);
    get(LIMIT0 + l as usize) as usize
}

/// `limit` as a `u32`, `none` and values past it `u32::MAX`.
pub fn limit_u32(l: Limit) -> u32 {
    read(LIMIT0 + l as usize).min(u32::MAX as u64) as u32
}

/// `f` as part of a run of the default passes, for code called outside any pipeline: there
/// every variable is `none`.
#[cfg(test)]
pub(crate) fn in_default_run<R>(f: impl FnOnce() -> R) -> R {
    crate::pipe::in_run(&Passes::default(), None, || crate::pipe::Cand::new("(Var \"x\")", "input"), f)
}

/// `f` with the `INNER` passes `names` turned off, as `((off NAMES) | f)` would run it.
pub fn with_off<R>(names: &[&str], f: impl FnOnce() -> R) -> R {
    in_scope(|| {
        names.iter().for_each(|n| turn_off(n));
        f()
    })
}

/// A term of the pipeline language (`crate::pipe_lang`): a step, which maps a list of
/// equivalent candidate terms (the first is the main one) to another, so any step can follow
/// any other (`lowbits | rewrite | (fix 3 egglog)`), or an expression, evaluated on the
/// candidates to a number or `NONE` (true when not 0). Every function, built-in (the
/// operators too) or defined, is applied by an `App`.
#[derive(Clone, Debug, PartialEq)]
pub enum Pipe {
    /// A number; `NONE` is `none`.
    Num(u64),
    /// A name argument: a stats or origin name, an egglog label, a note register, or the group
    /// variable a built-in binds or reads (`(save t)`, `(size t)`).
    Name(String),
    /// A string literal (`text`), its escapes read.
    Text(String),
    /// A read of a variable or parameter.
    Var(Slot),
    /// A function applied to its arguments in the order of its parameters. For a built-in,
    /// an optional one not written is left out, except the second branch of `if`, which is
    /// `id`; for a function that gives a number, the input written follows the arguments
    /// (`(mixed g)`, `(size (rewrite))`; `pipe::Builtin::input_at`). Written without the
    /// arguments it is a function value (`print`).
    App(Fun, std::sync::Arc<[Pipe]>),
    /// Each in turn on the candidates of the one before (`a | b`), as a scope. Where the last
    /// gives a number (`(lowbits | size)`), so does the sequence: the last on what the others
    /// give, those as a scope that ends before it.
    Seq(Vec<Pipe>),
    /// `NAME = VALUE`, the input passing on unchanged. A global binds in the enclosing scope
    /// to the number the right side gives (a switch is on for any value but 0, `time_limit`
    /// takes milliseconds from now), a local number variable likewise in the run's table, a
    /// group variable to the candidates the right side gives as a scope of its own, a
    /// function variable to the right side as a closure over the values of the variables it
    /// reads (`crate::pipe::Closure`).
    Bind(Slot, std::sync::Arc<Pipe>),
    /// A macro call as written and what it expands to, which is what runs.
    Expanded(Box<Expanded>),
}

/// A variable or parameter, resolved when parsed.
#[derive(Clone, Debug, PartialEq)]
pub enum Slot {
    /// A global variable, by its position in `VARS`, looked up along the calls; `time_limit`
    /// reads as the milliseconds left, `keep` as at least 1.
    Global(usize),
    /// A local variable of the run, looked up in the text. A group variable read gives its
    /// candidates whatever the input; a function variable is applied to the input.
    Local(String, Holds),
    /// A parameter of the function whose body this is, by its position, and its name: a
    /// pipeline argument runs where the call is written, a numeric one gives the value it had
    /// at the call.
    Param(usize, String),
}

/// What a local variable holds.
#[derive(Clone, Debug, PartialEq)]
pub enum Holds {
    Num,
    Group,
    Fn(crate::builtins::Ty),
}

/// The function an `App` applies: a built-in, an operator (a built-in too, its `Impl` held
/// in the node so that evaluating it reads nothing else) or a `def`.
#[derive(Clone, Debug, PartialEq)]
pub enum Fun {
    Builtin(&'static crate::pipe::Builtin),
    Op(crate::pipe::Operator, &'static crate::pipe::Builtin),
    Def(std::sync::Arc<Call>),
}

impl Fun {
    /// The type of the parameter argument `i` of `args` is for; `None` for the input written
    /// after the arguments of a function that gives a number.
    pub fn param_ty(&self, args: &[Pipe], i: usize) -> Option<&crate::builtins::Ty> {
        match self {
            Fun::Builtin(b) if b.input_at(args) == Some(i) => None,
            Fun::Builtin(b) | Fun::Op(_, b) => Some(&b.sig.param(i).ty),
            Fun::Def(c) => c.def.params.get(i).map(|p| &p.ty),
        }
    }
}

/// A macro call (`(smallest p)`, `(off NAME ...)`, `(on NAME ...)`) as written, `head` and
/// `args`, which `--show-passes`, errors, checks and warnings read, and its expansion, which
/// runs.
#[derive(Clone, Debug)]
pub struct Expanded {
    pub head: &'static str,
    pub args: Vec<Pipe>,
    pub steps: Vec<Pipe>,
    /// The steps are a scope; otherwise they run in the enclosing one, as the call would.
    pub scoped: bool,
    /// Runs past the time limit too: its steps only bind.
    pub bookkeeping: bool,
}

impl PartialEq for Expanded {
    fn eq(&self, o: &Expanded) -> bool {
        self.head == o.head && self.args == o.args
    }
}

impl Expanded {
    /// `(off NAME ...)` (`on` false) or `(on NAME ...)`: `NAME = 0 | ...` or `NAME = 1 | ...`
    /// for the `INNER` passes and `FLAGS` switches named, in the enclosing sequence. A name
    /// that is no switch (a parameter until a call puts its argument in place) expands to
    /// nothing.
    pub fn switches(on: bool, names: &[&str]) -> Pipe {
        let steps = names.iter().filter_map(|n| switch_index(n)).map(|i| Pipe::Bind(Slot::Global(i), std::sync::Arc::new(Pipe::Num(on as u64)))).collect();
        let args = names.iter().map(|n| Pipe::Name(n.to_string())).collect();
        Pipe::Expanded(Box::new(Expanded { head: if on { "on" } else { "off" }, args, steps, scoped: false, bookkeeping: true }))
    }

    /// For `on` and `off`: whether it is `on`, and the names.
    pub fn switch_names(&self) -> Option<(bool, Vec<&str>)> {
        let on = match self.head {
            "on" => true,
            "off" => false,
            _ => return None,
        };
        let names = self.args.iter().map(|a| if let Pipe::Name(n) = a { n.as_str() } else { unreachable!("a switch name") });
        Some((on, names.collect()))
    }
}

/// A function `(def (NAME PARAM ...) body)` defined in `--passes` or `default.pipe`.
#[derive(Debug, PartialEq)]
pub struct Def {
    pub name: String,
    /// The parameters, their types inferred from the body: `pipe`, `num`, `group` or `name`.
    pub params: Vec<crate::builtins::Param>,
    /// The body, name parameters written as their names.
    pub body: std::sync::Arc<Pipe>,
    /// `(def @inline ...)` with a numeric parameter: a call has its own arguments but no run
    /// of its own (other `@inline` functions are expanded where they are called).
    pub inline: bool,
    /// The body of an `inline` one is written `a | b`, which joins the caller's sequence.
    pub flat: bool,
    /// `@pipe`: the input parameter, bound to the candidates `|` gives; `None` in the form
    /// without it, whose body runs on the input as it is.
    pub input: Option<String>,
    /// Written as a step: `@pipe`, or the form without an input parameter.
    pub step: bool,
    /// The body when it gives a number: a call gives a number (`body` is then a `filter` of
    /// it, for the checks).
    pub value: Option<Pipe>,
    /// `value` runs steps (`lowbits | size`), so a call is a run of its own.
    pub steps: bool,
    /// The input `value` reads where it is not written, so that a call takes it implicitly
    /// (`(def (under k) size <= k)`).
    pub implicit: Option<crate::builtins::Ty>,
}

impl Def {
    /// Whether a parameter is a name, which a call puts in place in its own copy of the body;
    /// a group parameter too in an `inline` one, which shares the caller's group variables.
    pub fn has_names(&self) -> bool {
        self.params.iter().any(|p| p.ty == crate::builtins::Ty::Name || p.ty == crate::builtins::Ty::Group && self.inline) || self.inline && self.input.is_some()
    }

    /// The group variables bound when the body starts: the group parameters and the input.
    pub fn bound(&self) -> Vec<String> {
        let groups = self.params.iter().filter(|p| p.ty == crate::builtins::Ty::Group).map(|p| p.name.clone());
        groups.chain(self.input.clone()).collect()
    }
}

/// The `Def` an `App` calls, and its body with the name arguments in place of the name
/// parameters. The `App`'s arguments are one per parameter, as its type reads it: a name as
/// `Pipe::Name`, a group variable of the caller (passed by value) as its read, a pipeline,
/// or an expression evaluated once at the call on the caller's candidates.
#[derive(Debug)]
pub struct Call {
    pub def: std::sync::Arc<Def>,
    pub body: std::sync::Arc<Pipe>,
}

/// The body is made from the function and the arguments (an `@inline` one with an input
/// binds it under a name of its own for each call); the `App` compares the arguments.
impl PartialEq for Call {
    fn eq(&self, o: &Call) -> bool {
        self.def == o.def
    }
}

impl Call {
    /// The call of `def` without arguments.
    pub fn bare(def: &std::sync::Arc<Def>) -> Pipe {
        Pipe::App(Fun::Def(std::sync::Arc::new(Call { def: def.clone(), body: def.body.clone() })), Vec::new().into())
    }
}

impl Pipe {
    /// The built-in function `name` applied to `args`; `name` must be declared.
    pub fn app(name: &str, args: Vec<Pipe>) -> Pipe {
        let b = crate::pipe::builtin(name).unwrap_or_else(|| panic!("no built-in {name}"));
        match b.imp {
            crate::pipe::Impl::Operator(o) => Pipe::App(Fun::Op(o, b), args.into()),
            _ => Pipe::App(Fun::Builtin(b), args.into()),
        }
    }

    /// The step `id`.
    pub fn id() -> Pipe {
        Pipe::app("id", Vec::new())
    }

    /// Whether this is the step `id`.
    pub fn is_id(&self) -> bool {
        matches!(self, Pipe::App(Fun::Builtin(b), _) if b.name == "id")
    }

    /// The `Def` this calls, and the arguments.
    pub fn call(&self) -> Option<(&std::sync::Arc<Call>, &[Pipe])> {
        match self {
            Pipe::App(Fun::Def(c), args) => Some((c, args)),
            _ => None,
        }
    }

    /// Whether this is a function written as a value, without arguments, that gives
    /// candidates, or a function variable: `print` writes its signature.
    pub fn is_function_value(&self) -> bool {
        match self {
            Pipe::Var(Slot::Local(_, Holds::Fn(_))) => true,
            Pipe::App(Fun::Builtin(b), _) => !b.sig.is_number(),
            Pipe::App(Fun::Def(c), _) => c.def.value.is_none(),
            _ => false,
        }
    }

    /// Whether this gives a term? (`(main r)`, `(index i r)`): steps whose last picks one
    /// candidate of a group.
    pub fn picks(&self) -> bool {
        matches!(self, Pipe::Seq(ps) if matches!(ps.last(), Some(Pipe::App(Fun::Builtin(b), _)) if b.sig.kind() == crate::builtins::Kind::Pick))
    }

    /// The global variable at `i`, read.
    pub fn global(i: usize) -> Pipe {
        Pipe::Var(Slot::Global(i))
    }

    /// `x = e` for the global variable at `i`.
    pub fn assign(i: usize, e: Pipe) -> Pipe {
        Pipe::Bind(Slot::Global(i), std::sync::Arc::new(e))
    }
}

/// `a op b` for `+ - * /`, `none` as +∞: `+` and `*` give `none` on overflow or a `none`
/// operand, `-` stops at 0 (`n - none` is 0), `/` gives `none` for a 0 divisor and 0 for a
/// `none` one.
pub fn arith(op: char, a: u64, b: u64) -> u64 {
    match op {
        '+' if a != NONE && b != NONE => a.checked_add(b).unwrap_or(NONE),
        '*' if a != NONE && b != NONE => a.checked_mul(b).unwrap_or(NONE),
        '+' | '*' => NONE,
        '-' if b == NONE => 0,
        '-' if a == NONE => NONE,
        '-' => a.saturating_sub(b),
        _ if b == 0 => NONE,
        _ if b == NONE => 0,
        _ if a == NONE => NONE,
        _ => a / b,
    }
}

/// A comparison operator.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl Cmp {
    pub const ALL: [(Cmp, &'static str); 6] = [(Cmp::Lt, "<"), (Cmp::Le, "<="), (Cmp::Gt, ">"), (Cmp::Ge, ">="), (Cmp::Eq, "=="), (Cmp::Ne, "!=")];

    pub fn symbol(self) -> &'static str {
        Cmp::ALL.iter().find(|(c, _)| *c == self).unwrap().1
    }

    pub fn holds(self, a: u64, b: u64) -> bool {
        match self {
            Cmp::Lt => a < b,
            Cmp::Le => a <= b,
            Cmp::Gt => a > b,
            Cmp::Ge => a >= b,
            Cmp::Eq => a == b,
            Cmp::Ne => a != b,
        }
    }
}

impl fmt::Display for Pipe {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", lang::show(self))
    }
}

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

/// The polish `polish=a,b,...` writes: the polish passes `names` in turn, each kept when
/// smaller, repeated while one is, until `polish_wins` are, as the default in `default.pipe`.
pub fn polish(names: &[&str]) -> String {
    let step = |n: &&str| {
        let run = format!("polish/{n} | drop_identities");
        let run = if *n == "join_linear" { format!("(semi_leaves = 2 | {run})") } else { run };
        format!("(smaller polish/{n} {run})")
    };
    let steps: Vec<String> = names.iter().map(step).collect();
    let steps = if steps.len() == 1 { format!("(seq {})", steps[0]) } else { steps.join("\n  | ") };
    format!("(scope rewrites = polish_rewrites\n  | (wins polish_wins\n  {steps}))")
}

fn switch_index(name: &str) -> Option<usize> {
    INNER.iter().chain(&FLAGS).position(|k| *k == name)
}

/// Turns off the `INNER` pass or `FLAGS` switch `name` until the end of the scope under way
/// (`in_scope`: the enclosing sequence or pipeline run), also in the runs it starts (the
/// pass `(off NAME)`).
pub fn turn_off(name: &str) {
    if let Some(i) = switch_index(name) {
        bind(i, 0);
    }
}

/// `turn_off` the other way (the pass `(on NAME)`): the later of the two in a scope counts.
pub fn turn_on(name: &str) {
    if let Some(i) = switch_index(name) {
        bind(i, 1);
    }
}

/// Whether the `FLAGS` switch `name` is on on this thread.
pub fn is_on(name: &str) -> bool {
    FLAGS.iter().position(|k| *k == name).is_some_and(|i| read(FLAG0 + i) != 0)
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
    read(i) == 0
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
    /// Enabled entries of `PRE`.
    pub pre: Vec<&'static str>,
    /// The assignments (`Pipe::Bind` of globals, `on` and `off`) a run starts with, in order: the
    /// first `defaults` from `default.pipe`, the rest from `--passes` (`entry_steps`).
    pub entry: Vec<Pipe>,
    pub defaults: usize,
    /// `check_limits` of `default.pipe` (or of `--passes`, which may redefine it), run once
    /// after the entry assignments (`pipe::in_run`).
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
static DEFAULT: std::sync::LazyLock<(Passes, lang::Defs)> = std::sync::LazyLock::new(|| {
    crate::builtins::all();
    let mut p = Passes::base();
    let mut defs = lang::Defs::new();
    let mut globals = Vec::new();
    parsing(&mut globals, || p.apply_source(include_str!("default.pipe"), &mut defs, &mut Lets::default(), true)).and_then(|()| p.finish()).unwrap_or_else(|e| panic!("src/default.pipe: {e}"));
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
fn check_of(defs: &lang::Defs) -> Pipe {
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
            pre: PRE.to_vec(),
            entry: Vec::new(),
            defaults: 0,
            check: id.clone(),
            pipeline: id.clone(),
            prepass: id.clone(),
            polish: id.clone(),
            rewrite: id.clone(),
            simba: id,
            subs: SUBS.iter().map(|(_, d)| crate::pipe::resolve(d).unwrap()).collect(),
            defs: Vec::new(),
            default_defs: 0,
            globals: Vec::new(),
            default_globals: 0,
            defines: Vec::new(),
        }
    }

    /// Whether the pre-pass candidate `name` (an entry of `PRE`) is built.
    pub fn pre_on(&self, name: &str) -> bool {
        debug_assert!(PRE.contains(&name), "unknown pre-pass candidate {name}");
        self.pre.contains(&name)
    }

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
        let steps: Vec<String> = self.entry_steps(Some((m, i))).iter().map(lang::show).collect();
        format!("# A run: {} | check_limits | pipeline
{self:#}", steps.join(" | "))
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

    /// The default pipeline changed by `spec`: items `key=value`, and for the lists `pre`,
    /// `off` and `schedule` also `key+=names` and `key-=names` (names separated by `,`;
    /// schedule steps written `run:`, `once:` or `sat:` and a ruleset). `pipeline`,
    /// `prepass`, `polish`, `rewrite`, `simba` and `sub/NAME` (`SUBS`) take a pipeline
    /// (`crate::pipe_lang`), and `polish` also a list of polish pass names, run as
    /// `polish(names)`. Any other key is a variable that exists: the item is an entry
    /// assignment (`entry`), as are the `off` items.
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
        p.finish()?;
        // The Rust code runs `check_limits` (`Passes::check`).
        let unused = lets.defined.iter().filter(|(head, _)| head != "check_limits" && !lets.used.iter().any(|n| head.split(' ').next() == Some(n)));
        let mut notes: Vec<String> = unused
            .map(|(n, k)| match k {
                lang::DefKind::Let => format!("(let {n} ...) is never used: a name is expanded only where a later item writes it"),
                lang::DefKind::Inline => format!("(def @inline ({n}) ...) is never used: it is expanded only where a later item calls it"),
                lang::DefKind::Run => format!("(def ({n}) ...) is never used: it runs only where a later item calls it"),
            })
            .collect();
        notes.extend(lets.notes);
        notes.extend(p.warnings());
        notes.dedup();
        Ok((p, notes))
    }

    /// The items of `spec` applied in turn.
    fn apply(&mut self, spec: &str, defs: &mut lang::Defs, lets: &mut Lets) -> Result<(), String> {
        let p = self;
        let read = |val: &str, defs: &lang::Defs, used: &mut Vec<String>| {
            lang::parse_with(val, defs, used).map_err(|e| match lang::is_old_syntax(val) {
                true => format!("{e} (the old seq(a,b) syntax is no longer read: write a | b, (best 1 a b), (if c a))"),
                false => e,
            })
        };
        let spec: String = spec.lines().map(lang::code_part).collect::<Vec<_>>().join("\n");
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
            if let Some(val) = item.strip_prefix("polish=") {
                let names: Vec<&str> = val.split(',').filter(|s| !s.is_empty()).collect();
                let all_polish = names.iter().all(|n| crate::linear_mba::POLISH.iter().any(|(m, _)| m == n));
                p.polish = if all_polish { read(&polish(&names), defs, &mut lets.used)? } else { read(val, defs, &mut lets.used)? };
                continue;
            }
            if let Some((name, val)) = item.split_once('=').filter(|(k, _)| lang::defined_builtin(k) || k.starts_with("sub/")) {
                p.define(name, read(val, defs, &mut lets.used)?)?;
                continue;
            }
            let (key, op, val) = ["+=", "-=", "="]
                .iter()
                .find_map(|op| item.split_once(op).map(|(k, v)| (k, *op, v)))
                .ok_or_else(|| format!("expected key=value: {item}"))?;
            let names = |known: &[&'static str]| -> Result<Vec<&'static str>, String> {
                val.split(',').filter(|s| !s.is_empty()).map(|n| known.iter().find(|k| **k == n).copied().ok_or_else(|| format!("unknown {key} name {n}; known: {}", known.join(",")))).collect()
            };
            if key == "pre" {
                let ns = names(&PRE)?;
                match op {
                    "=" => p.pre = ns,
                    "+=" => p.pre.extend(ns),
                    _ => p.pre.retain(|n| !ns.contains(n)),
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
            p.entry.push(lang::parse_assign(key, val).map_err(|e| format!("{item}: {e}"))?);
        }
        Ok(())
    }

    /// A form of `--passes` or a source file: `(let ...)` or `(def ...)`.
    fn form(&mut self, item: &str, defs: &mut lang::Defs, lets: &mut Lets) -> Result<(), String> {
        if item.starts_with("(extern") {
            return Err(lang::NO_EXTERN.into());
        }
        if !(item.starts_with("(let") || item.starts_with("(def")) {
            return Err(format!("expected (let ...), (def ...) or NAME = VALUE: {item}"));
        }
        let d = lang::parse_definition(item, defs, &mut lets.used)?;
        lets.notes.extend(d.notes.iter().cloned());
        if d.kind == lang::DefKind::Run && lang::defined_builtin(&d.name) {
            self.define(&d.name, d.pipe)?;
            return Ok(());
        }
        let numeric = d.params.iter().any(|p| p.ty.is_expr());
        let head = std::iter::once(d.name.as_str()).chain(d.params.iter().map(|p| p.name.as_str())).collect::<Vec<_>>().join(" ");
        let inline = d.kind == lang::DefKind::Inline && (numeric || d.input.is_some());
        let (pipe, def) = if d.kind == lang::DefKind::Run || inline {
            let body = std::sync::Arc::new(d.value.clone().map_or(d.pipe, |v| Pipe::app("filter", vec![v])));
            let def = std::sync::Arc::new(Def { name: d.name.clone(), params: d.params.clone(), body, inline, flat: inline && d.flat, input: d.input.clone(), step: d.step, steps: d.value.as_ref().is_some_and(lang::has_steps), value: d.value.clone(), implicit: d.implicit.clone() });
            self.defs.push(def.clone());
            (Call::bare(&def), Some(def))
        } else {
            (d.pipe, None)
        };
        defs.insert(d.name.clone(), lang::Named { pipe, flat: d.flat, run: d.kind == lang::DefKind::Run, params: d.params, def });
        lets.defined.push((head, d.kind));
        Ok(())
    }

    /// The items of a source file (`default.pipe`, `file=PATH`) applied in turn: forms
    /// `(let ...)` and `(def ...)`, which may span lines, and `NAME = VALUE` lines
    /// (`assign_top`); `#` starts a comment to the end of the line.
    fn apply_source(&mut self, text: &str, defs: &mut lang::Defs, lets: &mut Lets, default: bool) -> Result<(), String> {
        let (mut form, mut depth, mut start) = (String::new(), 0i32, 0);
        for (n, line) in text.lines().enumerate() {
            let code = lang::code_part(line).trim_end();
            if depth == 0 && code.trim().is_empty() {
                continue;
            }
            if depth == 0 {
                start = n + 1;
            }
            let at = |e: String| format!("line {start}: {e}");
            depth += lang::depth_of(code);
            form = if form.is_empty() { code.trim().to_string() } else { format!("{form}\n{code}") };
            if depth > 0 && form.starts_with('(') {
                continue;
            }
            let item = std::mem::take(&mut form);
            depth = 0;
            if item.starts_with('(') {
                self.form(&item, defs, lets).map_err(at)?;
            } else {
                let (name, val) = top_assignment(&item).ok_or_else(|| at(format!("expected (let ...), (def ...) or NAME = VALUE: {item}")))?;
                self.assign_top(name, val, default, defs).map_err(|e| at(format!("{item}: {e}")))?;
            }
        }
        if !form.is_empty() {
            return Err(format!("line {start}: unclosed form: {form}"));
        }
        Ok(())
    }

    /// `name = val` as an item of a source file, or of `--passes` with spaces around `=`: the
    /// definition of the variable `name` when it is none yet, else an entry assignment to it.
    /// Every variable is `none` until assigned, so a definition of `default.pipe` as `none`
    /// adds no entry assignment.
    fn assign_top(&mut self, name: &str, val: &str, default: bool, defs: &lang::Defs) -> Result<(), String> {
        let defined = PARSED.with(|p| p.borrow().as_ref().is_some_and(|g| g.iter().any(|i| var(*i).name == name)));
        let new = match var_index(name) {
            _ if defined => false,
            Some(i) if i < FLAG0 => false,
            Some(i) if i < RUST_VARS => {
                PARSED.with(|p| p.borrow_mut().get_or_insert_with(Vec::new).push(i));
                true
            }
            Some(_) => false,
            None => {
                if lang::defined_builtin(name) || name.starts_with("sub/") {
                    return Err(format!("{name} is a function: a source file defines it as (def ({name}) ...)"));
                }
                if !lang::free_name(name) || defs.contains_key(name) {
                    return Err(format!("{name} names a function or a definition, not a variable"));
                }
                global_slot(name);
                true
            }
        };
        if new && default && val.trim() == "none" {
            return Ok(());
        }
        if new && !default {
            self.defines.push(self.entry.len());
        }
        self.entry.push(lang::parse_assign(name, val)?);
        Ok(())
    }

    /// The variables the Rust code reads that the source files do not define, as errors: a
    /// pass switch (`INNER`) is the name of an `extern @switch`, or has a `/` (a part of a pass).
    fn undefined(&self) -> Vec<String> {
        let sigs = crate::builtins::all();
        let switched = |n: &str| sigs.iter().any(|s| s.switch && s.name == n);
        let mut out: Vec<String> = (FLAG0..RUST_VARS).filter(|i| !self.globals.contains(i)).map(|i| format!("src/default.pipe: {} is read by the Rust code and not defined", var(i).name)).collect();
        out.extend(INNER.iter().filter(|n| !n.contains('/') && !switched(n)).map(|n| format!("src/builtins.pipe: {n} is a pass switch of the Rust code (sched::INNER) and no extern @switch")));
        out.extend(sigs.iter().filter(|s| s.switch && !INNER.contains(&s.name.as_str())).map(|s| format!("src/builtins.pipe: {} has @switch and is not in sched::INNER", s.name)));
        out
    }

    /// `(def (name) body)` for a defined function of the Rust code: `pipeline`, `prepass`,
    /// `polish`, `rewrite`, `simba` or `sub/NAME`.
    fn define(&mut self, name: &str, body: Pipe) -> Result<(), String> {
        let slot = match name {
            "pipeline" => &mut self.pipeline,
            "prepass" => &mut self.prepass,
            "polish" => &mut self.polish,
            "rewrite" => &mut self.rewrite,
            "simba" => &mut self.simba,
            _ => {
                let sub = name.strip_prefix("sub/").unwrap_or(name);
                let names: Vec<&str> = SUBS.iter().map(|(n, _)| *n).collect();
                let i = names.iter().position(|n| *n == sub).ok_or_else(|| format!("unknown sub/{sub}; known: {}", names.join(" ")))?;
                &mut self.subs[i]
            }
        };
        *slot = body;
        Ok(())
    }

    /// The lists in their canonical order, then `check`.
    fn finish(&mut self) -> Result<(), String> {
        self.pre.sort_by_key(|n| PRE.iter().position(|k| k == n));
        self.pre.dedup();
        self.check()
    }

    /// Rejects pipelines that cannot run: an egglog round or `reprint` outside `pipeline`
    /// (only a `simplify` run has them), also in a function they call, and a function that
    /// reaches itself through other functions. The rebuilds of one term (`rewrite`, `simba`,
    /// `sub/NAME`: one node `rewrite`, which any pass over one term may run) recurse on
    /// subterms, and so may the functions they call that call them again.
    fn check(&self) -> Result<(), String> {
        let mut reach: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
        let mut needs = std::collections::HashMap::new();
        for (name, node, uses) in self.uses() {
            if let Some(r) = &uses.unsaved {
                let how = match uses.kind(r) {
                    GROUP => format!("{r} = ... or (save {r})"),
                    FUNCTION => format!("{r}:TYPE = ..."),
                    _ => format!("{r} = ..."),
                };
                return Err(format!("{name} reads {} {r} before it is bound ({how})", uses.kind(r)));
            }
            if let Some((what, sig)) = uses.needs_run.first() {
                match node.as_str() {
                    "pipeline" => {}
                    "prepass" | "polish" | "rewrite" => return Err(format!("{what} needs a simplify run and cannot be in {name}: {}", sig.decl())),
                    _ => {
                        needs.insert(node.clone(), (what.clone(), *sig));
                    }
                }
            }
            reach.entry(node).or_default().extend(uses.calls);
        }
        let reached = |start: &str| {
            let (mut seen, mut todo) = (Vec::<String>::new(), reach.get(start).cloned().unwrap_or_default());
            while let Some(n) = todo.pop() {
                if !seen.contains(&n) {
                    todo.extend(reach.get(&n).cloned().unwrap_or_default());
                    seen.push(n);
                }
            }
            seen
        };
        let inner = reached("rewrite");
        let starts = ["prepass", "polish"].into_iter().chain(self.defs.iter().map(|d| d.name.as_str()));
        for start in starts {
            if reached(start).iter().any(|n| n == start) && !(self.defs.iter().any(|d| d.name == start) && inner.iter().any(|n| n == start)) {
                return Err(format!("{start} reaches itself"));
            }
        }
        for start in ["prepass", "polish", "rewrite"] {
            if let Some((n, (what, sig))) = reached(start).iter().find_map(|n| needs.get(n).map(|w| (n, w))) {
                return Err(format!("{what} needs a simplify run and cannot be in {n}, which {start} calls: {}", sig.decl()));
            }
        }
        Ok(())
    }

    /// Parts of the pipelines that do nothing: a `(save R)` never read in its pipeline or
    /// saved over before any read on every path, an assignment (also `(on NAME)`, `(off
    /// NAME)`) that ends its sequence, and one assigned again in its sequence before any
    /// read of it or any other step.
    pub fn warnings(&self) -> Vec<String> {
        let mut out = Vec::new();
        let globals = var_names();
        for (name, _, uses) in self.uses() {
            let mut unread: Vec<&String> = uses.saved.iter().filter(|r| !uses.reads.contains(r)).collect();
            unread.dedup();
            out.extend(unread.into_iter().map(|r| format!("{name}: {} {r} is bound and never read", uses.kind(r))));
            let mut dead = uses.dead.clone();
            dead.dedup();
            out.extend(dead.iter().map(|r| format!("{name}: {} {r} is bound again before its value is read", uses.kind(r))));
            out.extend(uses.idle_assign.iter().map(|t| format!("{name}: {t} ends its sequence and changes nothing")));
            out.extend(uses.reassigned.iter().map(|v| format!("{name}: {v} is assigned again before anything reads it")));
            out.extend(uses.dropping.iter().map(|v| format!("{name}: {v} drops its input: a group value after | gives its own candidates")));
            let params = self.defs.iter().find(|d| d.name == name).map_or_else(Vec::new, |d| d.bound());
            let mut locals: Vec<&String> = uses.saved.iter().filter(|r| !params.contains(r)).collect();
            locals.sort();
            locals.dedup();
            for r in locals {
                if let Some(g) = globals.iter().find(|g| near(r, g)) {
                    out.push(format!("{name}: {} {r} is a new local variable; did you mean {g}?", uses.kind(r)));
                }
            }
        }
        out.extend(self.unread_globals().into_iter().map(|n| format!("{n} is defined and never read")));
        out
    }

    /// The variables the `--passes` source files define that neither the Rust code nor any
    /// pipeline or entry assignment reads.
    fn unread_globals(&self) -> Vec<&'static str> {
        let mut text: Vec<String> = self.entry.iter().map(|e| if let Pipe::Bind(Slot::Global(_), v) = e { lang::show(v) } else { lang::show(e) }).collect();
        let main = [&self.pipeline, &self.prepass, &self.polish, &self.rewrite, &self.simba];
        text.extend(main.into_iter().chain(&self.subs).map(lang::show));
        text.extend(self.defs.iter().map(|d| lang::show_def(d)));
        let words: std::collections::HashSet<&str> = text.iter().flat_map(|t| t.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '/'))).collect();
        self.globals[self.default_globals..].iter().filter(|i| **i >= RUST_VARS).map(|i| var(*i).name).filter(|n| !words.contains(n)).collect()
    }

    /// Each pipeline by name, with its node in `check` (`rewrite` for `simba` and
    /// `sub/NAME`) and what it uses.
    fn uses(&self) -> Vec<(String, String, Uses)> {
        let main = [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)];
        let builtin = main.into_iter().chain(SUBS.iter().map(|(n, _)| *n).zip(&self.subs)).map(|(name, p)| {
            let node = if ["pipeline", "prepass", "polish"].contains(&name) { name } else { "rewrite" };
            (name.to_string(), node.to_string(), p)
        });
        let plain = self.defs.iter().filter(|d| !d.has_names() && !d.inline).map(|d| (d.name.clone(), d.name.clone(), &*d.body));
        let roots: Vec<(String, String, &Pipe)> = builtin.chain(plain).collect();
        let mut called = Vec::new();
        roots.iter().for_each(|(_, _, p)| instances(p, &mut called));
        let bound = |name: &str| self.defs.iter().find(|d| d.name == name).map_or_else(Vec::new, |d| d.bound());
        let of = |p: &Pipe, name: &str| {
            let mut uses = Uses::default();
            let bound = bound(name);
            uses.saved.extend(bound.iter().cloned());
            uses.reads.extend(bound);
            uses.walk(p);
            if binds(p) {
                uses.idle_assign.push(lang::show(p));
            }
            uses
        };
        let mut out: Vec<(String, String, Uses)> = roots.iter().map(|(name, node, p)| (name.clone(), node.clone(), of(p, name))).collect();
        out.extend(called.iter().map(|(name, _, body)| (name.clone(), name.clone(), of(body, name))));
        out
    }
}

/// Whether the new local variable `r` is close enough to the variable `g` to be a typo of it:
/// an edit distance of 1 for names of 3 or 4 characters, 1 or 2 for longer ones.
fn near(r: &str, g: &str) -> bool {
    let most = match r.len() {
        0..=2 => return false,
        3 | 4 => 1,
        _ => 2,
    };
    if r.contains('#') || r.len().abs_diff(g.len()) > most {
        return false;
    }
    let (a, b): (Vec<char>, Vec<char>) = (r.chars().collect(), g.chars().collect());
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, ca) in a.iter().enumerate() {
        let mut prev = row[0];
        row[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cur = row[j + 1];
            row[j + 1] = (prev + usize::from(ca != cb)).min(row[j] + 1).min(cur + 1);
            prev = cur;
        }
    }
    (1..=most).contains(&row[b.len()])
}

/// `NAME = VALUE` split into its name and value.
fn top_assignment(item: &str) -> Option<(&str, &str)> {
    let (name, val) = item.split_once('=')?;
    let name = name.trim_end();
    (is_name(name) && !val.starts_with('=')).then_some((name, val.trim()))
}

/// Whether `s` is a name a variable can have.
fn is_name(s: &str) -> bool {
    s.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '/')
}

/// The calls in `p` of functions with name parameters, and those in the bodies they run, each
/// once per function and name arguments: the function's name, the name arguments, the body.
fn instances(p: &Pipe, out: &mut Vec<(String, Vec<String>, std::sync::Arc<Pipe>)>) {
    p.each(&mut |q| instances(q, out));
    if let Some((c, _)) = p.call()
        && c.def.inline
    {
        instances(&c.body, out);
    } else if let Some((c, args)) = p.call()
        && c.def.has_names()
    {
        let names: Vec<String> = args.iter().filter_map(|a| if let Pipe::Name(n) = a { Some(n.clone()) } else { None }).collect();
        if !out.iter().any(|(n, ns, _)| *n == c.def.name && *ns == names) {
            out.push((c.def.name.clone(), names, c.body.clone()));
            instances(&c.body, out);
        }
    }
}

/// Whether `p` only binds globals: an assignment, `(on NAME)` or `(off NAME)`.
fn binds(p: &Pipe) -> bool {
    match p {
        Pipe::Bind(x, _) => matches!(x, Slot::Global(_)),
        Pipe::Expanded(m) => m.switch_names().is_some(),
        _ => false,
    }
}

impl Pipe {
    /// `f` on each pipeline directly inside `self`, also inside its expressions: the
    /// pipeline arguments, the steps of a sequence and the inputs written of calls, the
    /// pipeline arguments of a call (not the body it calls).
    pub fn each<'p>(&'p self, f: &mut dyn FnMut(&'p Pipe)) {
        match self {
            Pipe::App(fun, args) => {
                for (i, a) in args.iter().enumerate() {
                    match fun.param_ty(args, i) {
                        Some(t) if !t.is_step() => a.each_in_expr(f),
                        _ => f(a),
                    }
                }
            }
            Pipe::Seq(ps) => ps.iter().for_each(f),
            Pipe::Expanded(m) => m.args.iter().filter(|a| !matches!(a, Pipe::Name(_))).for_each(f),
            Pipe::Bind(Slot::Local(_, Holds::Group), p) => f(p),
            Pipe::Bind(Slot::Local(_, Holds::Fn(t)), p) if t.is_step() => f(p),
            Pipe::Bind(_, e) => e.each_in_expr(f),
            Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::Var(_) => {}
        }
    }

    /// `each` for the expression `self`, where a sequence gives a number: its steps before the
    /// last are pipelines, the last an expression.
    fn each_in_expr<'p>(&'p self, f: &mut dyn FnMut(&'p Pipe)) {
        match self {
            Pipe::Seq(ps) => {
                let (e, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
                steps.iter().for_each(&mut *f);
                e.each_in_expr(f);
            }
            e => e.each(f),
        }
    }
}

/// The `let` and `def` names a spec defines and those its items use, for
/// `Passes::parse_noting`.
#[derive(Default)]
struct Lets {
    defined: Vec<(String, lang::DefKind)>,
    used: Vec<String>,
    /// The warnings of reading the definitions.
    notes: Vec<String>,
}

/// What a pipeline uses, for `Passes::check` and `Passes::warnings`.
#[derive(Default)]
struct Uses {
    /// The passes in it that need a `simplify` run (`@simplify_only`), by the name they are
    /// counted as.
    needs_run: Vec<(String, &'static crate::builtins::Sig)>,
    /// The functions it runs: `prepass`, `polish`, `rewrite` (also for `simba` and
    /// `sub/NAME`, which any pass over one term may run) and those `def` defines.
    calls: Vec<String>,
    /// The group variables a `(save R)` or `R = p` may have bound by now, in run order; each
    /// pipeline has its own.
    saved: Vec<String>,
    /// The first group variable read where nothing can have bound it before.
    unsaved: Option<String>,
    /// Every group variable read, also by `pre_done` (`t0`, which it may find unbound).
    reads: Vec<String>,
    /// The assignments that end their sequence, so change nothing.
    idle_assign: Vec<String>,
    /// The variables assigned twice in a sequence with no read or other step between.
    reassigned: Vec<String>,
    /// The group variables bound and not read since on every path that reaches this point,
    /// from bindings at the same level of `if`s and other parts that may not run.
    pending: Vec<String>,
    /// The group variables bound again where they are `pending`: the earlier value is never
    /// read.
    dead: Vec<String>,
    /// The stages after a `|` that start with a group value, so drop the candidates before.
    dropping: Vec<String>,
    /// The local variables bound or read as numbers or function values; the others are
    /// group variables.
    kinds: Vec<(String, &'static str)>,
}

const GROUP: &str = "group variable";
const NUMBER: &str = "number variable";
const FUNCTION: &str = "function variable";

impl Uses {
    fn walk(&mut self, p: &Pipe) {
        match p {
            Pipe::App(Fun::Builtin(b), args) => self.app(b, args),
            Pipe::Bind(Slot::Local(r, Holds::Group), p) => {
                self.walk(p);
                self.bound(r);
                if binds(p) {
                    self.idle_assign.push(lang::show(p));
                }
            }
            Pipe::Var(Slot::Local(r, Holds::Group)) => self.read(r),
            Pipe::Var(Slot::Local(r, Holds::Fn(_))) => self.read_as(r, FUNCTION),
            Pipe::Bind(Slot::Local(r, Holds::Fn(t)), p) => {
                match &**p {
                    Pipe::Seq(_) if !t.is_step() => self.expr(p),
                    p => self.walk(p),
                }
                self.bound_as(r, FUNCTION);
            }
            Pipe::Bind(Slot::Local(r, Holds::Num), e) => {
                self.expr(e);
                self.bound_as(r, NUMBER);
            }
            Pipe::Bind(_, v) => self.expr(v),
            Pipe::Seq(ps) => self.seq(ps),
            Pipe::Expanded(m) if m.switch_names().is_some() => {}
            Pipe::Expanded(m) => m.args.iter().for_each(|a| self.walk(a)),
            // An `@inline` body is checked as written out where it is called.
            Pipe::App(Fun::Def(c), args) if c.def.inline => {
                args.iter().zip(&c.def.params).for_each(|(a, p)| if p.ty.is_expr() { self.expr(a) });
                self.walk(&lang::expand(c, args));
            }
            // A pipeline argument runs with the caller's group variables, at any point of the call
            // and any number of times.
            Pipe::App(Fun::Def(c), args) => {
                self.calls.push(c.def.name.clone());
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Param(..)) => {}
            e => self.expr(e),
        }
    }

    /// The steps `ps` of a sequence.
    fn seq(&mut self, ps: &[Pipe]) {
        let flat: Vec<Pipe>;
        let ps = match ps.iter().any(|p| p.call().is_some_and(|(c, _)| c.def.inline)) {
            true => {
                flat = ps.iter().flat_map(flat_stages).collect();
                &flat
            }
            false => ps,
        };
        let mut pending: Vec<usize> = Vec::new();
        for p in ps {
            match p {
                Pipe::Bind(Slot::Global(i), v) => {
                    if reads_var(v, *i) {
                        pending.retain(|j| j != i);
                    }
                    self.assigned(&mut pending, *i);
                }
                Pipe::Expanded(m) if m.switch_names().is_some() => m.switch_names().unwrap().1.into_iter().filter_map(var_index).for_each(|i| self.assigned(&mut pending, i)),
                _ => pending.clear(),
            }
        }
        ps.iter().for_each(|p| self.walk(p));
        for p in ps.iter().skip(1).filter(|p| lang::starts_with_value(p)) {
            let s = lang::show_stage(p);
            if !s.contains('#') {
                self.dropping.push(s);
            }
        }
        if let Some(a) = ps.last().filter(|p| binds(p)) {
            self.idle_assign.push(lang::show(a));
        }
    }

    fn app(&mut self, b: &crate::pipe::Builtin, args: &[Pipe]) {
        if b.sig.simplify_only {
            self.needs_run.push((crate::pipe::step_name(b.name, args), b.sig));
        }
        let name = |i: usize| match &args[i] {
            Pipe::Name(n) => n.as_str(),
            a => unreachable!("{a:?} is not a name"),
        };
        match b.name {
            "prepass" | "polish" => self.calls.push(b.name.into()),
            "pre_done" => self.seen("t0"),
            "save" => self.bound(name(0)),
            "load" | "label" => self.read(name(0)),
            "union" => args.iter().for_each(|p| self.walk(p)),
            "first" => {
                self.walk(&args[0]);
                args[1..].iter().for_each(|p| self.maybe(p));
            }
            "best" => {
                args[1..].iter().for_each(|p| self.walk(p));
                self.expr(&args[0]);
            }
            "fix" | "wins" => {
                self.expr(&args[0]);
                self.repeated(&args[1]);
            }
            "if" => {
                self.expr(&args[0]);
                let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
                self.walk(&args[1]);
                let after_a = std::mem::take(&mut self.pending);
                self.walk(&args[2]);
                let both: Vec<String> = self.pending.drain(..).filter(|r| after_a.contains(r)).collect();
                self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
                for r in both {
                    if !self.pending.contains(&r) {
                        self.pending.push(r);
                    }
                }
            }
            "retry" => {
                self.walk(&args[1]);
                self.expr(&args[0]);
                self.maybe(&args[2]);
            }
            "cand" => self.maybe(&args[1]),
            "filter" | "assert" => self.expr(&args[0]),
            "print" => args.iter().for_each(|a| match a {
                Pipe::Var(Slot::Local(r, Holds::Group)) => self.read(r),
                Pipe::Name(_) | Pipe::Text(_) => {}
                f if f.is_function_value() => {}
                e => self.expr(e),
            }),
            "scope" => self.walk(&args[0]),
            "tag" | "smaller" => self.walk(&args[1]),
            // Both rebuild with `Passes::rewrite`.
            "regions" => {
                self.calls.push("rewrite".into());
                self.repeated(&args[0]);
            }
            "again" => {
                self.calls.push("rewrite".into());
                self.walk(&args[0]);
            }
            _ if b.over_term() => self.calls.push("rewrite".into()),
            _ => {}
        }
    }

    fn call_args(&mut self, c: &Call, args: &[Pipe]) {
        use crate::builtins::Ty;
        for (a, p) in args.iter().zip(&c.def.params) {
            match (&p.ty, a) {
                (t, e) if t.is_expr() => self.expr(e),
                (Ty::Group, Pipe::Var(Slot::Local(r, _))) => self.read(r),
                (Ty::Name | Ty::Group, _) => {}
                (_, p) => self.repeated(p),
            }
        }
    }

    fn assigned(&mut self, pending: &mut Vec<usize>, i: usize) {
        if pending.contains(&i) {
            self.reassigned.push(var(i).name.to_string());
        } else {
            pending.push(i);
        }
    }

    /// `p` run more than once: a read can see a save of an earlier run.
    fn repeated(&mut self, p: &Pipe) {
        let mut body = Uses::default();
        body.walk(p);
        self.saved.extend(body.saved);
        self.maybe(p);
    }

    /// `p` run or not. A save in `p` does not make an earlier one dead (`(save t) | (if c
    /// (save t))` keeps a default), and only what is pending either way stays pending.
    fn maybe(&mut self, p: &Pipe) {
        let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
        self.walk(p);
        self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
    }

    fn bound(&mut self, r: &str) {
        self.saved.push(r.to_string());
        if self.pending.iter().any(|s| s == r) {
            self.dead.push(r.to_string());
        } else {
            self.pending.push(r.to_string());
        }
    }

    fn seen(&mut self, r: &str) {
        self.reads.push(r.to_string());
        self.pending.retain(|s| s != r);
    }

    fn bound_as(&mut self, r: &str, kind: &'static str) {
        self.kinds.push((r.to_string(), kind));
        self.bound(r);
    }

    fn read_as(&mut self, r: &str, kind: &'static str) {
        self.kinds.push((r.to_string(), kind));
        self.read(r);
    }

    /// What `r` is, for messages: a group variable unless bound or read as another kind.
    fn kind(&self, r: &str) -> &'static str {
        self.kinds.iter().find(|(n, _)| n == r).map_or(GROUP, |(_, k)| k)
    }

    fn read(&mut self, r: &str) {
        self.seen(r);
        if self.unsaved.is_none() && !self.saved.iter().any(|s| s == r) {
            self.unsaved = Some(r.to_string());
        }
    }

    fn expr(&mut self, e: &Pipe) {
        match e {
            Pipe::App(Fun::Builtin(b), args) => {
                let args = match b.input_at(args) {
                    Some(k) => {
                        self.walk(&args[k]);
                        &args[..k]
                    }
                    None => &args[..],
                };
                if ["opaque", "rebuilds"].contains(&b.name) {
                    self.calls.push("prepass".into());
                }
                for a in args.iter() {
                    match a {
                        Pipe::Name(r) => self.read(r),
                        a => self.expr(a),
                    }
                }
            }
            Pipe::App(Fun::Op(..), args) => args.iter().for_each(|a| self.expr(a)),
            Pipe::Seq(ps) => {
                let (e, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
                match steps {
                    [p] => self.walk(p),
                    ps => self.seq(ps),
                }
                self.expr(e);
            }
            Pipe::App(Fun::Def(c), args) => {
                self.calls.push(c.def.name.clone());
                args.get(c.def.params.len()).iter().for_each(|p| self.walk(p));
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Local(r, Holds::Fn(_))) => self.read_as(r, FUNCTION),
            Pipe::Var(Slot::Local(r, Holds::Num)) => self.read_as(r, NUMBER),
            _ => {}
        }
    }
}

/// The stages `p` stands for in a sequence, for `Uses`: those of an `@inline` body written
/// out, after a `filter` of each numeric argument (read at the call, a step there).
fn flat_stages(p: &Pipe) -> Vec<Pipe> {
    match p {
        Pipe::App(Fun::Def(c), args) if c.def.inline => {
            let num = args.iter().zip(&c.def.params).filter(|(_, p)| p.ty.is_expr());
            let filters = num.map(|(e, _)| Pipe::app("filter", vec![e.clone()]));
            let body = match lang::expand(c, args) {
                Pipe::Seq(ps) if c.def.flat => ps.iter().flat_map(flat_stages).collect(),
                q => flat_stages(&q),
            };
            filters.chain(body).collect()
        }
        _ => vec![p.clone()],
    }
}

/// Whether `e` reads the variable at `i`.
fn reads_var(e: &Pipe, i: usize) -> bool {
    let group = |p: &Pipe| matches!(p, Pipe::Var(Slot::Local(_, Holds::Group)));
    match e {
        Pipe::Var(Slot::Global(j)) => *j == i,
        Pipe::App(Fun::Builtin(b), cs) => match b.input_at(cs) {
            Some(k) => !group(&cs[k]) && (!cs[k].picks() || reads_var(&cs[k], i)) || cs[..k].iter().any(|c| reads_var(c, i)),
            None => cs.iter().any(|c| reads_var(c, i)),
        },
        Pipe::App(Fun::Op(..), cs) => cs.iter().any(|c| reads_var(c, i)),
        Pipe::Seq(ps) => !matches!(&ps[..ps.len() - 1], [p] if group(p)) || reads_var(&ps[ps.len() - 1], i),
        Pipe::App(Fun::Def(c), args) => {
            let num = args.iter().zip(&c.def.params).filter(|(_, p)| p.ty.is_expr());
            c.def.steps || args.get(c.def.params.len()).is_some_and(|p| !group(p)) || num.into_iter().any(|(e, _)| reads_var(e, i))
        }
        _ => false,
    }
}

/// The spec `Passes::parse` reads back to these passes; `{:#}` puts each pipeline on its own
/// lines.
impl fmt::Display for Passes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let steps: Vec<String> = self.schedule.iter().map(|(s, rs)| format!("{}:{rs}", STEPS.iter().find(|(k, _)| k == s).unwrap().1)).collect();
        write!(f, "schedule={} pre={}", steps.join(","), self.pre.join(","))?;
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
                (Pipe::Bind(Slot::Global(_), _), _) if self.defines.contains(&(self.defaults + i)) => write!(f, " {}", lang::show(&spec[i]))?,
                (Pipe::Bind(Slot::Global(v), val), _) => write!(f, " {}={}", var(*v).name, lang::show_assigned(val))?,
                (p, _) => unreachable!("entry step {p:?}"),
            }
            i += 1;
        }
        let show = if f.alternate() { lang::pretty } else { lang::show };
        let sep = if f.alternate() { "\n" } else { " " };
        for d in &self.defs[self.default_defs..] {
            if f.alternate() {
                write!(f, "\n# {}\n{}", lang::sig_of(d), lang::pretty_def(d))?;
            } else {
                write!(f, " {}", lang::show_def(d))?;
            }
        }
        for (name, p) in [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)] {
            write!(f, "{sep}{name}={}", show(p))?;
        }
        for ((name, default), p) in SUBS.iter().zip(&self.subs) {
            if Some(p) != crate::pipe::resolve(default).as_ref() {
                write!(f, "{sep}sub/{name}={}", show(p))?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> crate::pipe::Cand {
        crate::pipe::Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input")
    }

    /// `s` parsed with the names `default.pipe` defines.
    fn parse_default(s: &str) -> Pipe {
        lang::parse_with(s, &DEFAULT.1, &mut Vec::new()).unwrap()
    }

    /// The value of variable `name` after the entry assignments of `p`.
    fn after_entry(p: &Passes, name: &str) -> u64 {
        let i = parsing(&mut p.globals.clone(), || var_index(name)).unwrap();
        crate::pipe::in_run(p, None, x, || get(i))
    }

    #[test]
    fn off_ends_with_its_scope() {
        let p = Passes::parse("off+=relate").unwrap();
        crate::pipe::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("semi/peel_shapes"), "the entry assignments run first");
            in_scope(|| {
                turn_on("relate");
                crate::pipe::in_run(&p, None, x, || assert!(!is_off("relate"), "a run inside a run keeps the bindings of its caller"));
                turn_off("tfunc");
            });
            assert!(!is_off("tfunc") && is_off("relate"), "a pass turned off in a scope is on again after it");
        });
        assert!(!is_off("relate") && !is_off("semi/peel_shapes"), "the entry bindings end with the run");
    }

    #[test]
    fn entry_assignments() {
        let p = Passes::parse("extra=5 split_runs=vars*3 extra=extra+1 off=relate,tfunc off+=simba off-=tfunc").unwrap();
        assert_eq!(after_entry(&p, "extra"), 6, "items run in order, a later one reading an earlier");
        assert_eq!(after_entry(&p, "split_runs"), 6, "a value is evaluated on the input");
        assert_eq!(after_entry(&p, "keep"), 2, "default.pipe comes first");
        crate::pipe::in_run(&p, None, x, || {
            assert!(is_off("relate") && is_off("simba") && !is_off("tfunc"));
            assert!(!is_off("semi/peel_shapes"), "off= turns every other pass on");
        });
        assert!(!is_off("relate") && get(var_index("extra").unwrap()) == NONE, "nothing leaks out of a run");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(p.to_string().contains(" extra=5 split_runs=vars * 3 extra=extra + 1 off=relate,tfunc off+=simba off-=tfunc "), "{p}");
        let p = Passes::parse("off-=semi/peel_shapes keep=0 prove_minimal=0 restarts=7 match_limit=9").unwrap();
        assert!(crate::pipe::in_run(&p, None, x, || !is_off("semi/peel_shapes")));
        assert_eq!([after_entry(&p, "keep"), after_entry(&p, "prove_minimal"), after_entry(&p, "restarts")], [0, 0, 7]);
        assert!(crate::pipe::in_run(&p, None, x, || p.egglog_schedule().contains(":match-limit 9 :ban-length 3")));
        let p = Passes::parse("off=").unwrap();
        assert_eq!(p.entry[p.defaults..], [Expanded::switches(true, &INNER)]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let cli = crate::Cli { max_restarts: 5, iter_limit: 3, passes: Passes::parse("iter_limit=iter_limit*2").unwrap(), ..Default::default() };
        let (m, i) = crate::pipe::in_run(&cli.passes, Some(&cli), x, || (get(RESTARTS), get(ITER_LIMIT)));
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
        let unset: Vec<&str> = crate::pipe::in_run(&p, None, x, || all().filter(|&i| var(i).kind != VarKind::Pass && get(i) == NONE).map(|i| var(i).name).collect());
        assert_eq!(unset, ["rewrites", "bit_split_budget", "restarts", "iter_limit", "time_limit"]);
        let unset: Vec<&str> = crate::pipe::in_run(&p, Some(&cli), x, || all().filter(|&i| get(i) == NONE && var(i).kind != VarKind::Pass).map(|i| var(i).name).collect());
        assert_eq!(unset, ["rewrites", "bit_split_budget", "time_limit"], "-m and -i set restarts and iter_limit");
        assert_eq!(get(var_index("max_leaves").unwrap()), NONE, "outside a run every variable is none");
    }

    #[test]
    fn source_defines_every_variable_rust_reads() {
        let p = Passes::default();
        assert_eq!(p.undefined(), Vec::<String>::new(), "every name the Rust code reads is defined, every extern @switch is in INNER");
        let defined: Vec<&str> = p.globals.iter().map(|i| var(*i).name).collect();
        for i in FLAG0..RUST_VARS {
            assert!(defined.contains(&var(i).name), "{}", var(i).name);
        }
        let only_pipelines: Vec<&str> = p.globals.iter().filter(|i| **i >= RUST_VARS).map(|i| var(*i).name).collect();
        assert_eq!(only_pipelines, ["extra", "printed", "unclustered_relate_leaves", "unclustered_rewrites", "unified_rewrites", "polish_rewrites", "polish_wins"]);
        let mut all = p.clone();
        all.default_globals = 0;
        assert_eq!(all.unread_globals(), Vec::<&str>::new(), "a pipeline reads each variable the Rust code does not");
        assert_eq!(Passes::parse_noting("").unwrap().1, Vec::<String>::new(), "default.pipe gives no warnings");
        let kinds = [("relate", VarKind::Pass), ("semi/shapes", VarKind::Pass), ("cut", VarKind::Flag), ("max_leaves", VarKind::Limit), ("memo_contexts", VarKind::Unread), ("wide_blocks_cache_size", VarKind::Unread), ("semi_leaves", VarKind::Setting), ("keep", VarKind::Setting), ("rewrites", VarKind::Budget), ("bit_split_budget", VarKind::Budget), ("time_limit", VarKind::Deadline), ("extra", VarKind::Global)];
        for (n, k) in kinds {
            assert_eq!(kind(var_index(n).unwrap()), k, "{n}");
        }
        let r = crate::pipe::in_run(&p, None, x, || {
            swap_read(ReadSet::EMPTY);
            let e = Pipe::global(var_index("memo_contexts").unwrap());
            let env = crate::pipe::Env::prepass(&p, 64, None, false, x().term());
            crate::pipe::run(&Pipe::app("filter", vec![e]), vec![x()], &env).unwrap();
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
            crate::pipe::run(&p.prepass, vec![x()], &crate::pipe::Env::prepass(&p, 64, None, false, x().term())).err().map(|e| e.to_string())
        };
        for (name, cap) in caps {
            let msg = format!("{name} is at most {cap}");
            assert!(include_str!("default.pipe").contains(&format!("(assert ({name} <= {cap}) \"{msg}\")")), "{name}");
            assert_eq!(prepass(&format!("{name}={cap}")), None, "{name}");
            for bad in [(cap + 1).to_string(), "none".into()] {
                assert_eq!(prepass(&format!("{name}={bad}")).as_deref(), Some(msg.as_str()), "{name}={bad}");
            }
        }
        let input = crate::pipe::Cand::new("(Sub (Var \"x\") (Var \"y\"))", "input");
        let cli = crate::Cli { passes: Passes::parse("max_leaves=7").unwrap(), ..crate::Cli::default() };
        assert_eq!(crate::simplify(input.term(), &cli).err().map(|e| e.to_string()).as_deref(), Some("max_leaves is at most 6"), "checked when the run starts");
        let p = Passes::parse("prepass=(max_leaves = 7 | id)").unwrap();
        let r = crate::pipe::run(&p.prepass, vec![input.clone()], &crate::pipe::Env::prepass(&p, 64, None, false, input.term()));
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
        let r = crate::pipe::in_run(&p, None, x, || crate::pipe::run(&p.prepass, vec![x()], &crate::pipe::Env::prepass(&p, 64, None, false, x().term())).unwrap());
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
        let t = || crate::pipe::Cand::new("(Add (And (Var \"x\") (Var \"y\")) (Or (Var \"x\") (Var \"y\")))", "input");
        let r = crate::pipe::in_run(&p, None, t, || crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(&p, 64, None, false, t().term())).unwrap());
        assert_eq!(r[0].term(), "(Add (Var \"x\") (Var \"y\"))", "the rewrite memoized with pick = 0 is not reused with pick = 1");
    }

    #[test]
    fn moved_constants_bind_in_their_scope() {
        let input = "(Mul (Var \"x\") (Mul (Var \"x\") (Var \"x\")))";
        let t = || crate::pipe::Cand::new(&format!("(And (Add {input} (Var \"x\")) (Num 1))"), "input");
        let plain = Passes::parse("prepass=(scope lowbits)").unwrap();
        let scoped = Passes::parse("prepass=(scope (lowbits_max_try = 1 | lowbits) | lowbits)").unwrap();
        let none = Passes::parse("prepass=(scope (lowbits_max_try = 1 | id) | lowbits)").unwrap();
        let run = |p: &Passes| crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(p, 8, None, false, t().term())).unwrap()[0].term().to_string();
        assert_eq!(run(&plain), "(Num 0)", "x*x*x + x is even");
        assert_eq!(run(&none), "(Num 0)", "the assignment ends with its sequence");
        let inner = Passes::parse("prepass=(scope lowbits_max_try = 1 | lowbits)").unwrap();
        assert_ne!(run(&inner), "(Num 0)", "with nothing enumerated nothing folds");
        assert_eq!(run(&scoped), "(Num 0)");
        crate::pipe::in_run(&plain, None, t, || {
            assert_eq!(limit(Limit::LowbitsMaxTry), 256);
            crate::pipe::run(&lang::parse("lowbits_max_try = 1 | id").unwrap(), vec![t()], &crate::pipe::Env::prepass(&plain, 8, None, false, t().term())).unwrap();
            assert_eq!(limit(Limit::LowbitsMaxTry), 256, "a run ends the bindings made in it");
        });
    }

    #[test]
    fn moved_poly_constants_bind_in_their_scope() {
        let (x, y) = ("(Var \"x\")", "(Var \"y\")");
        let input = format!("(Sub (Mul (Add {x} {y}) (Add {x} {y})) (Add (Mul {x} {x}) (Mul (Num 2) (Mul {x} {y}))))");
        let t = || crate::pipe::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(&p, 8, None, false, t().term())).unwrap()[0].term().to_string()
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
        let t = || crate::pipe::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            let r = crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(&p, 32, None, false, t().term())).unwrap();
            crate::eval::size(&crate::eval::parse(r[0].term()))
        };
        let before = crate::eval::size(&crate::eval::parse(&input));
        let plain = run("prepass=(scope polish/join_linear)");
        assert!(plain < before, "a move makes it smaller");
        assert_eq!(run("prepass=(scope join_linear_max_groups = 0 | polish/join_linear)"), before, "no region is moved in");
        assert_eq!(run("prepass=(scope (join_linear_max_groups = 0 | id) | polish/join_linear)"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (join_linear_max_groups = 0 | polish/join_linear) | polish/join_linear)"), plain, "the memo keeps the scopes apart");
    }

    #[test]
    fn tfunc_constants_bind_in_their_scope() {
        let input = crate::expr_convert::infix_to_egglog("x & -(x & -(x & y))", true);
        let t = || crate::pipe::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(&p, 64, None, false, t().term())).unwrap()[0].term().to_string()
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
        let t = || crate::pipe::Cand::new(&input, "input");
        let run = |spec: &str| {
            let p = Passes::parse(spec).unwrap();
            crate::pipe::run(&p.prepass, vec![t()], &crate::pipe::Env::prepass(&p, 64, None, false, t().term())).unwrap()[0].term().to_string()
        };
        let plain = run("prepass=(scope (best 1 id wide_blocks))");
        assert_ne!(plain, input, "a block form is smaller");
        assert_eq!(run("prepass=(scope wide_blocks_max_block = 2 | (best 1 id wide_blocks))"), input, "no block is small enough");
        assert_eq!(run("prepass=(scope (wide_blocks_max_block = 2 | id) | (best 1 id wide_blocks))"), plain, "the assignment ends with its sequence");
        assert_eq!(run("prepass=(scope (wide_blocks_max_block = 2 | (best 1 id wide_blocks)) | (best 1 id wide_blocks))"), plain, "the cache keeps the scopes apart");
    }

    #[test]
    fn time_limit_zero_is_a_deadline() {
        let at = |spec: &str| crate::pipe::in_run(&Passes::parse(spec).unwrap(), None, x, || (get(DEADLINE), epoch_ns()));
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
        assert!(!p.pre_on("unified") && p.pre_on("no_wide"));
        assert_eq!(p.polish, parse_default(&polish(&["factor", "push_not", "factor"])));
        assert_eq!(lang::parse(&Passes::default().polish.to_string()).unwrap(), Passes::default().polish);
        let p = Passes::parse("rewrite=(regions (best 1 simba poly_mba))").unwrap();
        assert_eq!(p.rewrite.to_string(), "(regions (best 1 simba poly_mba))");
        assert_eq!(lang::parse(&Passes::default().simba.to_string()).unwrap(), Passes::default().simba);
        let p = Passes::parse("sub/cluster=(regions simba) sub/split_bits=rewrite").unwrap();
        assert_eq!(p.subs[sub_index("cluster")].to_string(), "(regions simba)");
        assert!(p.to_string().contains(" sub/cluster=(regions simba) sub/split_bits=rewrite"));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("sub/nope=rewrite").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("polish+=factor").is_err() && Passes::parse("polish=nope").is_err());
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(Passes::parse("pre+=nope").is_err() && Passes::parse("keep+=1").is_err());
        let p = Passes::parse("off=semi/bit_split,relate").unwrap();
        assert_eq!(p.entry[p.defaults..], [Expanded::switches(true, &INNER), Expanded::switches(false, &["semi/bit_split", "relate"])]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert!(crate::pipe::in_run(&p, None, x, || is_off("relate") && !is_off("simba")));
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
        let got = crate::pipe::in_run(&p, None, x, || (limit(Limit::SplitRuns), limit(Limit::PolyBuilds), limit(Limit::SplitDepth)));
        assert_eq!(got, (4, 64, 2));
        assert_eq!(limit(Limit::SplitRuns), usize::MAX);
        let p = Passes::parse("keep=1 pipeline=lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish/factor extra=0").unwrap();
        assert_eq!(p.pipeline.to_string(), "lowbits | (best 2 rewrite ((off relate tfunc) | rebuild)) | (fix 3 egglog) | polish/factor");
        assert_eq!((after_entry(&p, "keep"), after_entry(&p, "extra")), (1, 0));
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        let p = Passes::parse("pipeline=(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish) id))").unwrap();
        assert_eq!(p.pipeline.to_string(), "(smallest (fix restarts (retry (mixed && !minimal) prepass (egglog later))) | (if !input (tag t polish)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(lang::parse(&Passes::default().pipeline.to_string()).unwrap(), Passes::default().pipeline);
        assert_eq!(lang::parse(&Passes::default().prepass.to_string()).unwrap(), Passes::default().prepass);
        let d = Passes::default();
        assert_eq!(Passes::parse(&d.to_string()).unwrap(), d);
        assert_eq!(Passes::parse(&format!("{d:#}")).unwrap(), d);
        let p = Passes::parse("extra=0 prepass=lowbits | (if mixed rewrite) # a comment\n| polish keep=3;pipeline=(fix 2 prepass | egglog)").unwrap();
        assert_eq!((after_entry(&p, "extra"), after_entry(&p, "keep")), (0, 3));
        assert_eq!(p.prepass, lang::parse("(seq lowbits (if mixed rewrite id) polish)").unwrap());
        assert_eq!(p.pipeline, lang::parse("(fix 2 (seq prepass egglog))").unwrap());
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let p = Passes::parse("prepass=(scope (save t) | (rewrites = unified_rewrites | semi_leaves = 2 | rewrite) | (filter (size < (size (main t)) || size <= (size (main t)) * 3 / 4 && !tiny)) | (cand halve_input (load t)))").unwrap();
        assert_eq!(p.prepass.to_string(), "(scope (save t) | (rewrites = unified_rewrites | semi_leaves = 2 | rewrite) | (filter (size < (size (main t)) || size <= (size (main t)) * 3 / 4 && !tiny)) | (cand halve_input (load t)))");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        for bad in ["prepass=(filter lt)", "prepass=(filter (size <=))", "prepass=(rewrites = x | id)", "prepass=(save)", "prepass=(scope id id)"] {
            assert!(Passes::parse(bad).is_err(), "{bad}");
        }
        assert_eq!(Passes::default().check(), Ok(()));
        assert_eq!(Passes::default().polish, parse_default(&polish(&crate::linear_mba::POLISH.map(|(n, _)| n))));
        let p = Passes::parse("(let twice (fix 2 rewrite)) rewrite=twice | (best 1 twice simba) pipeline=(fix 1 first_round) | polish").unwrap();
        assert_eq!(p.rewrite, lang::parse("(fix 2 rewrite) | (best 1 (fix 2 rewrite) simba)").unwrap());
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
        assert_eq!(lang::show(&p.prepass), "lowbits | rewrite | rewrite | (fix times rewrite)");
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
        for bad in ["prepass=egglog", "simba=reprint", "sub/cluster=(egglog first)", "prepass=lowbits | prepass", "polish=polish", "rewrite=(again polish)", "prepass=(if rebuilds id)"] {
            let e = Passes::parse(bad).unwrap_err();
            assert!(e.contains("simplify run") || e.contains("reaches itself"), "{bad}: {e}");
        }
        assert!(Passes::parse("pipeline=(fix restarts prepass | egglog | polish)").is_ok());
        assert!(Passes::parse("prepass=(egglog x)").unwrap_err().contains("(extern @pipe @simplify_only (egglog label:name? g:group) group)"));
        assert!(Passes::parse("polish=(if mixed reprint)").unwrap_err().contains("reprint needs a simplify run and cannot be in polish"));
        for bad in ["(extern (x g:group) group)", "keep=1 (extern (x g:group) group)", "pipeline=extern"] {
            assert!(Passes::parse(bad).unwrap_err().contains(lang::NO_EXTERN), "{bad}");
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
        Passes::base().apply(include_str!("default.pipe"), &mut lang::Defs::new(), &mut lets).unwrap();
        assert!(lets.defined.iter().all(|(n, _)| n == "check_limits" || lets.used.contains(n)), "{:?} {:?}", lets.defined, lets.used);
        let (_, w) = Passes::parse_noting("(let foo rewrite) (let bar lowbits) prepass=bar | (save t) | (save q) | (load t) | ((off relate) | (save x) | id) | (rewrite | (off relate))").unwrap();
        assert_eq!(w.len(), 4, "{w:?}");
        assert!(w[0].contains("let foo") && w[1].contains("group variable q") && w[2].contains("group variable x") && w[3].contains("(off relate) ends"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=(save t) | rewrite | (save t) | (load t)").unwrap();
        assert!(w.len() == 1 && w[0].contains("bound again"), "{w:?}");
        let (_, w) = Passes::parse_noting("prepass=t = (off relate) | (load t)").unwrap();
        assert!(w.len() == 1 && w[0].contains("(off relate) ends"), "the right side of a group assignment is a scope: {w:?}");
        let (_, w) = Passes::parse_noting("prepass=t = id | t = rewrite | (load t) | u = rewrite | id").unwrap();
        assert!(w.len() == 2 && w[0].contains("group variable u is bound and never read") && w[1].contains("group variable t is bound again"), "{w:?}");
        for ok in ["prepass=(save t) | (if mixed (save t)) | (load t)", "prepass=(save t) | (cand unified (save t)) | (load t)", "prepass=(fix 3 (save t) | rewrite) | (load t)", "prepass=(save t) | (filter (size < (size (main t)))) | (save t) | (load t)", "prepass=(save t) | (first rewrite (save t)) | (load t)", "prepass=(if mixed (save t) (save t)) | (load t)"] {
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
            assert!(crate::pipe::in_run(&Passes::default(), None, x, || is_off("relate")));
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
        for name in ["pipeline", "prepass", "polish", "rewrite", "simba", "sub/cluster"] {
            let short = Passes::parse(&format!("{name}=lowbits | rewrite")).unwrap();
            assert_eq!(Passes::parse(&format!("(def ({name}) lowbits | rewrite)")).unwrap(), short, "{name}");
            assert_ne!(short, d);
        }
        assert_eq!(Passes::parse("polish=factor,push_not").unwrap().polish, parse_default(&polish(&["factor", "push_not"])));
        let p = Passes::parse("(def (twice) rewrite | rewrite) (def (more) twice | relate) prepass=lowbits | more | twice").unwrap();
        assert_eq!(p.defs.len(), 2);
        assert_eq!(p.prepass.to_string(), "lowbits | more | twice");
        assert_eq!(p.defs[1].body.to_string(), "twice | relate");
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
            ("(def (sub/nope) id)", "unknown sub/NAME"),
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
        for ok in ["(def (f) egglog) pipeline=f | polish", "(def (f) rewrite | relate) sub/cluster=f", "(def @inline (g) id) (def @inline (g) rewrite) prepass=g", "(def (f) (save t) | (load t)) prepass=(save t) | f | (load t)"] {
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
        let sigs: Vec<String> = p.defs.iter().map(|d| lang::sig_of(d).decl()).collect();
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
        let sigs: Vec<String> = p.defs.iter().map(|d| lang::sig_of(d).decl()).collect();
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
        let sigs: Vec<String> = p.defs.iter().map(|d| lang::sig_of(d).to_string()).collect();
        assert_eq!(sigs, ["(try_without name:name p:pipe g:group) group", "(hold r:group p:pipe g:group) group"]);
        assert_eq!(p.prepass.to_string(), "(try_without relate rewrite) | (save t) | (hold t (lowbits | rewrite))");
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
            "(def (f r) (tag r id) | (cand r id) | (smaller r id) | (egglog r)) pipeline=(f x)",
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
        let sigs: Vec<String> = p.defs.iter().map(|d| lang::sig_of(d).to_string()).collect();
        assert_eq!(sigs[0], "(with_budget n:num p:pipe g:group) group");
        assert_eq!(sigs[3], "(f n:num g:group) group");
        assert_eq!(sigs[4], "(lim n:num p:pipe g:group) group", "an @inline function with a numeric parameter is a function too");
        assert_eq!(p.prepass.to_string(), "(f 3) | (lim none id) | (lim2 (size - 1) (with_budget 8 rewrite))");
        assert!(p.to_string().contains(" (def @inline (lim n p) split_runs = n | p) (def @inline (lim2 n p) (split_runs = n | p)) "), "{p}");
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p);
        assert_eq!(Passes::parse(&format!("{p:#}")).unwrap(), p);
        let plain = Passes::parse("(def @inline (g p) p | relate) prepass=(g rewrite)").unwrap();
        assert!(plain.defs.is_empty(), "an @inline function without a numeric parameter is expanded");
    }
}
