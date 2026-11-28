//! The variables the Rust code of the passes reads, at fixed positions below `RUST_VARS`:
//! the pass switches `INNER`, the `FLAGS`, the numeric `LIMITS`, the `SETTINGS`, the `RUN`
//! settings and the deadline; and the accessors the passes read them by.

use crate::lang::vars::{VarKind, bind, get, in_scope, read};

/// Passes inside a rebuild that `off` can turn off: one in a chain then returns its input,
/// one of several alternatives gives no form. Each is an `extern @switch` of `builtins.pipe`
/// or a step inside one, a switch `default.pipe` defines (`DEFAULT` checks both).
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
    "poly_masked",
    "rebuild_values",
    "common_multiple",
    "related_leaves",
    "one_wide_term",
    "semi_linear",
    "drop_unused",
    "clustered",
    "peel",
    "peel_clustered",
    "semi_grouped",
    "semi_peel_grouped",
    "semi_shapes",
    "semi_pairs",
    "semi_peel_shapes",
    "semi_split",
    "semi_scaled",
    "semi_bit_split",
    "semi_short_consts",
];

/// Switches besides the `INNER` passes: `cut` (off unless turned on: a step skipped past a
/// `time_limit` makes the run cut, `crate::builtin_passes::cut`), `rerun_input` (rerun the first round
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
    /// Largest bitwise expression with free constants `semi_shapes` and `semi_pairs` search;
    /// the table of level 15 takes about 100 MB.
    ShapesMaxSize "shapes_max_size";
    /// `semi_pairs`: most bit groups of a region.
    PairsMaxGroups "pairs_max_groups";
    /// `semi_pairs`: most shape entries checked per call.
    PairsBudget "pairs_budget";
    /// `semi_pairs`: largest total size of the two shapes.
    PairsMaxSize "pairs_max_size";
    /// `semi_pairs`: most coefficients tried, the smallest first.
    PairsMaxScales "pairs_max_scales";
    /// `semi_pairs`: most carries per bit of the carry DP before it gives up.
    PairsMaxCarries "pairs_max_carries";
    /// `semi_semi_split`: most combinations of the other sets' constants per set.
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
/// egglog round), `restarts` (`-m`), `iter_limit` (`-i`, schedule repetitions of an egglog
/// round), `num_type` (the numeric type, a position in `NUM_TYPES`; `none` is `i64`) and
/// `trace` (`--trace`: candidates and round sizes to stderr).
pub const RUN: [&str; 7] = ["keep", "match_limit", "ban_length", "restarts", "iter_limit", "num_type", "trace"];

/// The numeric types, the values of `num_type` by position.
pub const NUM_TYPES: [&str; 8] = ["i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8"];

pub(crate) const FLAG0: usize = INNER.len();
pub(crate) const LIMIT0: usize = FLAG0 + FLAGS.len();
pub(crate) const SETTING0: usize = LIMIT0 + LIMITS.len();
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
pub const NUM_TYPE: usize = RUN0 + 5;
pub const TRACE: usize = RUN0 + 6;
pub const DEADLINE: usize = RUN0 + RUN.len();
/// The variables the Rust code reads; those the source files define besides follow them.
pub const RUST_VARS: usize = DEADLINE + 1;

pub(crate) const fn is_unread(i: usize) -> bool {
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
pub(crate) const fn rust_var(i: usize) -> (&'static str, VarKind) {
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

/// The name of the numeric type `num_type` holds on this thread.
pub fn num_type() -> &'static str {
    NUM_TYPES.get(get(NUM_TYPE) as usize).copied().unwrap_or(NUM_TYPES[0])
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

/// `f` after the program `(import "default")`, for code called outside any pipeline: there
/// every variable is `none`.
#[cfg(test)]
pub(crate) fn in_default_run<R>(f: impl FnOnce() -> R) -> R {
    crate::lang::run::within(&crate::passes::Passes::default(), f)
}

/// `f` with the `INNER` passes `names` turned off, as `((off NAMES) | f)` would run it.
pub fn with_off<R>(names: &[&str], f: impl FnOnce() -> R) -> R {
    in_scope(|| {
        names.iter().for_each(|n| turn_off(n));
        f()
    })
}

/// Whether the `INNER` switch `name` is defined by an `extern @switch` of `builtins.pipe`, not
/// by `default.pipe`.
pub(crate) fn is_extern_switch(name: &str) -> bool {
    crate::lang::builtins::get(name).is_some_and(|s| s.switch)
}

pub(crate) fn switch_index(name: &str) -> Option<usize> {
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

const fn same_name(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut j = 0;
    while j < a.len() && a[j] == b[j] {
        j += 1;
    }
    j == a.len()
}

/// The position of `name` in `INNER`, for `is_off_at`.
pub const fn inner_index(name: &str) -> usize {
    let mut i = 0;
    while i < INNER.len() {
        if same_name(name, INNER[i]) {
            return i;
        }
        i += 1;
    }
    panic!("not an INNER pass")
}

/// `is_off` of the `INNER` pass at position `i`.
pub fn is_off_at(i: usize) -> bool {
    read(i) == 0
}
