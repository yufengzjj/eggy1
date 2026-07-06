use eggy1::expr_convert::{ac_canon_infix, infix_to_egglog};
use eggy1::{Cli, magic_div_s, magic_div_u, magic_s, magic_u, make_egg, pow2_div, simplify, simplify_round};

/// Accept `r` if it matches any expected form exactly, or is
/// associativity/commutativity-equivalent to one of them.
fn matches_expected(expect: &[&str], r: &str, ok: bool) -> bool {
    if expect.contains(&r) {
        return true;
    }
    if !ok {
        return false;
    }
    let rc = ac_canon_infix(r);
    expect.iter().any(|e| ac_canon_infix(e) == rc)
}

/// Run a batch of `(expr, [acceptable outputs], iter_limit)` cases at the given
/// numeric type, accepting any AC-equivalent of an expected form.
fn check(num_type: &str, cases: &[(&str, &[&str], usize)]) {
    let mut cli = Cli {
        rule_compile: false,
        expr_compile: false,
        num_type: num_type.to_string(),
        iter_limit: 10,
        max_restarts: 2,
        expr: String::new(),
    };
    for (case, expect, iter) in cases {
        cli.iter_limit = *iter;
        let egg_expr = infix_to_egglog(case, true);
        let result = simplify(&egg_expr, &cli);
        let ok = result.is_ok();
        let r = match &result {
            Ok(v) => v.clone(),
            Err(e) => e.to_string(),
        };
        println!("{case} -> {r}");
        assert!(
            matches_expected(expect, &r, ok),
            "{}\n{}\n{} != {:?}\n{}",
            case,
            egg_expr,
            r,
            expect,
            make_egg(num_type)
        );
    }
}

/// Run a batch of `(num_type, expr, expected)` cases requiring an *exact* output
/// match (used for magic-number division recognition).
fn check_exact(cases: &[(&str, &str, &str)]) {
    let mut cli = Cli {
        rule_compile: false,
        expr_compile: false,
        num_type: "i32".to_string(),
        iter_limit: 12,
        max_restarts: 2,
        expr: String::new(),
    };
    for (nt, case, expected) in cases {
        cli.num_type = nt.to_string();
        let egg_expr = infix_to_egglog(case, true);
        let r = simplify(&egg_expr, &cli).unwrap();
        println!("{case} -> {r}");
        assert_eq!(&r, expected, "case: {case}");
    }
}

// ===========================================================================
// Formal simplification (i64): identities, folding, term collection.
// ===========================================================================

#[test]
fn formal_identity_and_absorption() {
    check(
        "i64",
        &[
            ("a + 0", &["a"], 10),
            ("0 + a", &["a"], 10),
            ("a + 0 + b", &["(a + b)"], 10),
            ("a * 1", &["a"], 10),
            ("1 * a", &["a"], 10),
            ("a * 0", &["0"], 10),
            ("0 * a", &["0"], 10),
            ("a - 0", &["a"], 10),
            ("0 - a", &["-a"], 10),
            ("a & a", &["a"], 10),
            ("a | a", &["a"], 10),
            ("a ^ a", &["0"], 10),
            ("a & 0", &["0"], 10),
            ("a | 0", &["a"], 10),
            ("a ^ 0", &["a"], 10),
            ("a & -1", &["a"], 10),
            ("a | -1", &["-1"], 10),
            ("a ^ -1", &["~a"], 10),
            ("~(~a)", &["a"], 10),
            ("a & ~a", &["0"], 10),
            ("a | ~a", &["-1"], 10),
            ("a & (a | b)", &["a"], 10),
            ("a | (a & b)", &["a"], 10),
            ("x & (x | y)", &["x"], 10),
            ("(x | y) & x", &["x"], 10),
            ("a + b * 0", &["a"], 10),
            ("a * (1 + 0)", &["a"], 10),
            ("a * (b - b)", &["0"], 10),
            ("0 * (a + b + c)", &["0"], 10),
            ("1 * (a + b + c)", &["((a + b) + c)"], 10),
            ("(a + b) - (a + b)", &["0"], 10),
        ],
    );
}

#[test]
fn formal_cancellation() {
    check(
        "i64",
        &[
            ("a - a", &["0"], 10),
            ("a - a + b", &["b"], 10),
            ("a + b - a", &["b"], 10),
            ("a + b - b - a", &["0"], 10),
            ("a + 5 - 5", &["a"], 10),
            ("a - b + c - a + b - c", &["0"], 10),
            ("a + (~a + 1)", &["0"], 10),
            ("a + -a", &["0"], 10),
        ],
    );
}

#[test]
fn formal_constant_folding() {
    check(
        "i64",
        &[
            ("5 + 3", &["8"], 10),
            ("17 - 8", &["9"], 10),
            ("4 * 6", &["0x18"], 10),
            ("6 / 2", &["3"], 10),
            ("10 % 3", &["1"], 10),
            ("~0", &["-1"], 10),
            ("~-1", &["0"], 10),
            ("a + 1 + 3", &["(4 + a)"], 10),
            ("a + b + 0 + c + 0", &["((a + b) + c)"], 10),
        ],
    );
}

#[test]
fn formal_term_collection() {
    check(
        "i64",
        &[
            ("a + a", &["(a + a)", "(2 * a)"], 10),
            ("a + a + a", &["(3 * a)"], 10),
            ("2 * a + 3 * a", &["(5 * a)"], 10),
            ("3 * a + 5 * a + 2 * a", &["(0xa * a)"], 10),
            ("(2 * a) + (3 * a) + a", &["(6 * a)"], 10),
            ("(x << 2) + x", &["(5 * x)", "(x * 5)"], 10),
            ("12 + a + 8 + b - 20", &["(a + b)"], 10),
        ],
    );
}

#[test]
fn formal_polynomial() {
    check(
        "i64",
        &[
            ("((a + b) * c - d) + (d - a * c)", &["(b * c)"], 10),
            (
                "a * b + a * c + b * a + b * c",
                &[
                    "((((b + c) + b) * a) + (b * c))",
                    "(((b + a) * c) + (2 * (a * b)))",
                ],
                10,
            ),
            (
                "(a + b + c) * (a + b + c)",
                &["(((a + b) + c) * ((a + b) + c))"],
                10,
            ),
        ],
    );
}

#[test]
fn formal_negation_and_xor() {
    check(
        "i64",
        &[
            ("-(a - b)", &["(b - a)"], 10),
            ("a * -1", &["-a"], 10),
            ("-1 * a", &["-a"], 10),
            ("a ^ b ^ a", &["b"], 10),
            ("a ^ a ^ b ^ b", &["0"], 10),
            ("a ^ a ^ a", &["a"], 10),
            ("(a ^ b) ^ b", &["a"], 10),
            ("a ^ (b ^ a)", &["b"], 10),
            ("a ^ (a ^ b ^ c) ^ b ^ c", &["0"], 10),
            ("(a & b) ^ (a & ~b)", &["a"], 10),
        ],
    );
}

#[test]
fn formal_shift() {
    check(
        "i64",
        &[
            ("(x << 2) ^ (4 * x)", &["0"], 10),
            (
                "(x & 0xffff) << 8",
                &["((x & 0xffff) << 8)", "((x & 0xffff) * 0x100)"],
                10,
            ),
            ("x >> 3 << 3", &["((x >> 3) << 3)", "((x >> 3) * 8)"], 10),
            ("(a + 1) & ~1", &["((a + 1) & -2)"], 10),
            ("(a * 2) >> 1", &["((a * 2) >> 1)"], 10),
            ("a + (b & 1)", &["(a + (b & 1))"], 10),
            (
                "(a << 3) + (b & 7)",
                &["((a << 3) + (b & 7))", "((a * 8) + (b & 7))"],
                10,
            ),
        ],
    );
}

#[test]
fn formal_division() {
    check(
        "i64",
        &[
            ("6 / 2", &["3"], 10),
            ("a / 2 + (b - b)", &["(a / 2)"], 10),
            ("(x / y) * y + x % y", &["x"], 10),
            ("x - (x / y) * y", &["(x % y)"], 10),
            ("x % 1", &["0"], 10),
            ("a / a", &["(a / a)"], 10),
            ("1 + (b - b) / (b - b)", &["1"], 10),
            ("(a | 4) / (a | 4)", &["1"], 10),
            ("(3 * (b | 1)) / (3 * (b | 1))", &["1"], 10),
            ("(x | 2) % (x | 2)", &["0"], 10),
        ],
    );
}

/// Soundness regressions (signed i64): rules that were removed/gated during the
/// wrapping-arithmetic audit must fold correctly and not over-simplify.
#[test]
fn formal_soundness_regressions() {
    check(
        "i64",
        &[
            // `a*b/b` does NOT simplify to `a` (a*8 can overflow, truncating
            // division won't recover a). Stays as-is.
            ("a * 8 / 8", &["((a * 8) / 8)", "((a << 3) / 8)"], 10),
            ("(a << 3) / 8", &["((a * 8) / 8)", "((a << 3) / 8)"], 10),
            // `b*d/d` does NOT collapse to `b` (b*d can overflow; odd/nonzero
            // divisor does not prevent it).
            ("b * (a | 1) / (a | 1)", &["((b * (a | 1)) / (a | 1))"], 10),
            // `-(x/y) <=> -x/y` was removed (it merged distinct constants);
            // must now fold correctly. `a/-1 => -a` kept for signed only.
            ("0 - (0 - 128) / 3", &["0x2a"], 10),
            ("x / -1", &["-x"], 10),
        ],
    );
}

/// XNOR identities (secret.club eqsat article appendix). Low iter_limit checks
/// the direct rules fire without the long indirect route through the
/// or-decomposition birewrites.
#[test]
fn formal_xnor_direct() {
    check(
        "i64",
        &[
            (
                "(a & b) | ~(a | b)",
                &["~(a ^ b)", "(a ^ ~b)", "(~a ^ b)"],
                3,
            ),
            (
                "(a & b) | (~a & ~b)",
                &["~(a ^ b)", "(a ^ ~b)", "(~a ^ b)"],
                3,
            ),
            ("((a & b) | ~(a | b)) ^ ~(a ^ b)", &["0"], 5),
        ],
    );
}

// ===========================================================================
// Magic-number division recognition.
// ===========================================================================

#[test]
fn magic_numbers() {
    // Known magic pairs from Hacker's Delight ch. 10 (W=32).
    assert_eq!(magic_s(3, 32), Some((0x55555556, 0, false)));
    assert_eq!(magic_s(5, 32), Some((0x66666667, 1, false)));
    assert_eq!(magic_s(7, 32), Some((0x92492493, 2, true)));
    // Unsigned: magic_u returns the *true* multiplier (may exceed 2^W).
    let (mu3, s3, a3) = magic_u(3, 32).unwrap();
    assert_eq!((mu3 & 0xffffffff, s3, a3), (0xAAAAAAAB, 1, false));
    let (mu7, s7, a7) = magic_u(7, 32).unwrap();
    assert_eq!((mu7 & 0xffffffff, s7, a7), (0x24924925, 3, true));
    // Round-trip: divisor recovery from (M, s).
    assert_eq!(magic_div_s(0x55555556, 0, 32, false), Some(3));
    assert_eq!(magic_div_s(0x66666667, 1, 32, false), Some(5));
    assert_eq!(magic_div_s(0x92492493u32 as i32 as i64, 2, 32, true), Some(7));
    assert_eq!(magic_div_u(0xAAAAAAABu32 as i32 as i64, 1, 32, false), Some(3));
    // Unsigned add-variant: true multiplier 0x1_24924925, stored low = 0x24924925.
    assert_eq!(magic_div_u(0x24924925, 3, 32, true), Some(7));
    // A non-magic pair must not resolve to any divisor.
    assert_eq!(magic_div_s(0x12345678, 1, 32, false), None);
    assert_eq!(magic_div_u(0x12345678, 3, 32, true), None);
    // Signed pow-of-2 division guard.
    assert_eq!(pow2_div(7, 3, 32), Some(8));
    assert_eq!(pow2_div(6, 3, 32), None); // mask != 2^k-1
    assert_eq!(pow2_div(0x7fffffff, 31, 32), None); // k=W-1 excluded
}

#[test]
fn magic_division_signed() {
    check_exact(&[
        ("i32", "mulhi(0x55555556, n) + ((n >> 31) & 1)", "(n / 3)"),
        ("i32", "(mulhi(0x66666667, n) >> 1) + ((n >> 31) & 1)", "(n / 5)"),
        (
            "i32",
            "((mulhi(0x92492493, n) + n) >> 2) + ((n >> 31) & 1)",
            "(n / 7)",
        ),
        // Signed division by power of 2 (HD 10-1).
        ("i32", "(n + ((n >> 31) & 1)) >> 1", "(n / 2)"),
        ("i32", "(n + ((n >> 31) & 7)) >> 3", "(n / 8)"),
        ("i8", "(n + ((n >> 7) & 63)) >> 6", "(n / 0x40)"),
        // Wrong correction mask (must be 2^k-1): must NOT collapse.
        (
            "i32",
            "(n + ((n >> 31) & 6)) >> 3",
            "((n + ((n >> 0x1f) & 6)) >> 3)",
        ),
        // Non-magic multiplier: must NOT collapse to a division.
        (
            "i32",
            "mulhi(0x12345678, n) + ((n >> 31) & 1)",
            "(mulhi(0x12345678, n) + ((n >> 0x1f) & 1))",
        ),
    ]);
}

#[test]
fn magic_division_unsigned() {
    check_exact(&[
        ("u32", "mulhi(0xAAAAAAAB, n) >> 1", "(n / 3)"),
        // Unsigned add-variant (Granlund-Montgomery overflow-free form).
        (
            "u32",
            "(((n - mulhi(0x24924925, n)) >> 1) + mulhi(0x24924925, n)) >> 2",
            "(n / 7)",
        ),
        (
            "u16",
            "(((n - mulhi(0x2493, n)) >> 1) + mulhi(0x2493, n)) >> 2",
            "(n / 7)",
        ),
    ]);
}

// ===========================================================================
// Unsigned (u8): power-of-2 div/mod and shift soundness regressions.
// ===========================================================================

#[test]
fn unsigned_pow2_div_mod() {
    check(
        "u8",
        &[
            ("(x / 8) ^ (x >> 3)", &["0"], 10),
            ("(x % 8) ^ (x & 7)", &["0"], 10),
            ("x / 4 * 4 + x % 4", &["x"], 10),
        ],
    );
}

/// Soundness regressions (unsigned): these must NOT collapse to the wrong form.
/// `0` is also accepted where the true value is 0, in case a future rule
/// reduces the over-shift fully.
#[test]
fn unsigned_soundness_regressions() {
    check(
        "u8",
        &[
            ("(a * 4) / 4", &["((a * 4) / 4)", "((a << 2) / 4)"], 10), // NOT a
            ("x / 255", &["(x / 0xff)"], 10),                         // NOT -x (0xff != -1)
            ("(a >> 255) >> 1", &["((a >> 0xff) >> 1)", "0"], 10),    // NOT a
            ("(a << 255) << 1", &["((a << 0xff) * 2)", "0"], 10),     // NOT a
            ("(a >> 2) >> 3", &["(a >> 5)"], 10),                     // in-range combine still works
        ],
    );
}

// ===========================================================================
// Complex MBA identities (i8), grouped by the rule / result form exercised.
// ===========================================================================

#[test]
fn complex_to_sub() {
    check(
        "i8",
        &[
            ("x + (~y + 1)", &["(x - y)"], 10),
            ("(x ^ y) - 2*(~x & y)", &["(x - y)"], 10),
            ("(x & ~y) - (~x & y)", &["(x - y)"], 10),
            ("2*(x & ~y) - (x ^ y)", &["(x - y)"], 10),
            ("~x - ~y", &["(y - x)", "(y + -x)"], 10),
        ],
    );
}

#[test]
fn complex_to_add() {
    check(
        "i8",
        &[
            ("x - (~y + 1)", &["(x + y)"], 10),
            ("(x ^ y) + 2*(x & y)", &["(x + y)"], 10),
            ("(x | y) + (x & y)", &["(x + y)"], 10),
            ("2*(x | y) - (x ^ y)", &["(x + y)"], 10),
            ("2*(x | y | z) - (x ^ (y | z))", &["((y | z) + x)"], 10),
            ("(a ^ 5) + 2*(a & 5)", &["(a + 5)"], 10),
            (
                "((a & 0xff) ^ 0x12) + 2*(a & 0x12)",
                &["((a & 0xff) + 0x12)", "(a + 0x12)", "(0x12 + a)"],
                10,
            ),
            ("(a ^ 0xfe) + 2*(a | 0x01)", &["a"], 10),
        ],
    );
}

#[test]
fn complex_off_by_one() {
    check(
        "i8",
        &[
            (
                "2*(x | y) + (x ^ ~y)",
                &[
                    "(~-y + x)",
                    "(~-x + y)",
                    "((x + y) + -1)",
                    "~(-y - x)",
                    "~(-x - y)",
                ],
                10,
            ),
            ("(x | ~y) + y", &["((x & y) + -1)", "~-(x & y)"], 10),
            (
                "(x + y) + ~(x & y)",
                &["((x | y) + -1)", "((y | x) + -1)", "~-(x | y)", "~-(y | x)"],
                10,
            ),
            (
                "~(x ^ y) + 2*(x | y)",
                &[
                    "((y + x) - 1)",
                    "((x + y) - 1)",
                    "~-(x + y)",
                    "~(-y - x)",
                    "~(-x - y)",
                    "((x + y) + -1)",
                    "((y + x) + -1)",
                ],
                10,
            ),
            (
                "~(x ^ y) - (-2 * (x | y))",
                &[
                    "((y + x) - 1)",
                    "((x + y) - 1)",
                    "~-(x + y)",
                    "~(-x - y)",
                    "~(-y - x)",
                    "((-1 + x) + y)",
                    "((x + y) + -1)",
                    "((y + x) + -1)",
                ],
                10,
            ),
        ],
    );
}

#[test]
fn complex_decrement() {
    check(
        "i8",
        &[
            (
                "(-x - 1) - (-2 * x)",
                &["(-1 + x)", "~-x", "(x + -1)"],
                10,
            ),
            ("2*x + ~x", &["~-x", "(-1 + x)", "(x + -1)"], 10),
            (
                "(~x | 1) + x",
                &[
                    "((1 & x) + -1)",
                    "-(~x & 1)",
                    "-(1 & ~x)",
                    "~-(1 & x)",
                    "((-2 | x) + 1)",
                ],
                10,
            ),
        ],
    );
}

#[test]
fn complex_to_and() {
    check(
        "i8",
        &[
            ("(~x | y) - ~x", &["(x & y)"], 10),
            ("(x + y) - (x | y)", &["(x & y)"], 10),
            ("(x | y) - (x ^ y)", &["(x & y)"], 10),
            ("(x | y) & ~(x ^ y)", &["(x & y)", "(y & x)"], 10),
            ("(x & y) & ~(x ^ y)", &["(x & y)"], 10),
            ("x & ~(x ^ y)", &["(x & y)"], 10),
            ("(~x | y) + (x + 1)", &["(x & y)"], 10),
            ("(x | y) & (x ^ ~y)", &["(x & y)"], 10),
            (" (x ^ ~y) & y", &["(x & y)", "(y & x)"], 10),
            ("a & ~(a ^ b)", &["(a & b)", "(b & a)"], 10),
        ],
    );
}

#[test]
fn complex_to_andnot() {
    check(
        "i8",
        &[
            ("(x | y) - y", &["(x & ~y)"], 10),
            ("x - (x & y)", &["(x & ~y)"], 10),
            ("x ^ (x & y)", &["(x & ~y)"], 10),
            ("x & (x ^ y)", &["(x & ~y)"], 10),
            ("(x | y) ^ y", &["(x & ~y)"], 10),
            ("(x | y) - x", &["(~x & y)", "(y & ~x)"], 10),
        ],
    );
}

#[test]
fn complex_to_or() {
    check(
        "i8",
        &[
            ("(x + y) - (x & y)", &["(x | y)", "(y | x)"], 10),
            ("(x - y) - (x & -y)", &["(x | -y)"], 10),
            ("(x & y) + (x ^ y)", &["(x | y)", "(y | x)"], 10),
            ("(x ^ y) + (x & y)", &["(x | y)", "(y | x)"], 10),
            ("((x + y) + 1) + ~(x & y)", &["(x | y)", "(y | x)"], 10),
            ("(x + (x ^ y)) - (x & ~y)", &["(x | y)", "(y | x)"], 10),
            ("(x & y) | (x ^ y)", &["(x | y)", "(y | x)"], 10),
            (
                "(x & (y ^ z)) | ((x ^ y) ^ z)",
                &["(x | (y ^ z))", "((y ^ z) | x)"],
                10,
            ),
            ("(x ^ y) | y", &["(x | y)", "(y | x)"], 10),
            ("(x & y) ^ (x ^ y)", &["(x | y)", "(y | x)"], 10),
            ("x ^ (~x & y)", &["(x | y)", "(y | x)"], 10),
            ("(x & ~y) + y", &["(x | y)", "(y | x)", "(y | x)"], 10),
            ("(x | y) | (~x ^ ~y)", &["(x | y)", "(y | x)"], 10),
            ("(x & y) | ~(~x ^ y)", &["(x | y)", "(y | x)"], 10),
            ("(~x & y) | x", &["(x | y)", "(y | x)"], 10),
            ("~(~x | ~y) | (x ^ y)", &["(x | y)", "(y | x)"], 10),
            ("a + (~a & b)", &["(a | b)", "(b | a)"], 10),
            ("a ^ (~a & b)", &["(a | b)", "(b | a)"], 10),
        ],
    );
}

#[test]
fn complex_to_or_not() {
    check(
        "i8",
        &[
            ("~x ^ (x & y)", &["(~x | y)"], 10),
            ("(x - y) + (~x | y)", &["(x | ~y)", "(~y | x)"], 10),
            ("(~x | y) ^ (x ^ y)", &["(x | ~y)", "(~y | x)"], 10),
        ],
    );
}

#[test]
fn complex_to_xor() {
    check(
        "i8",
        &[
            ("~x ^ ~y", &["(x ^ y)"], 10),
            ("(x | y) - (x & y)", &["(x ^ y)"], 10),
            ("2*(x | y) - (x + y)", &["(x ^ y)"], 10),
            ("(x + y) - 2*(x & y)", &["(x ^ y)"], 10),
            ("((x - y) - 2*(x | ~y)) - 2", &["(x ^ y)"], 10),
            ("x - (2*(x & y) - y)", &["(x ^ y)"], 10),
            ("x - (2*(y & ~(x ^ y)) - y)", &["(x ^ y)"], 10),
            ("x - (2*(x & y) - y)", &["(x ^ y)"], 10),
            ("(x & ~y) | (~x & y)", &["(x ^ y)"], 10),
            ("(~x & y) ^ (x & ~y)", &["(x ^ y)"], 15),
            ("(x & y) ^ (x | y)", &["(x ^ y)"], 10),
            ("(x - y) + 2*(~x & y)", &["(x ^ y)"], 10),
            ("~x + (2*x | 2)", &["(x ^ 1)", "(1 ^ x)"], 20),
            ("((y ^ z) ^ (x ^ z))", &["(x ^ y)", "(y ^ x)"], 10),
            (
                "((x ^ z) & (y ^ ~z)) | ((x ^ ~z) & (y ^ z))",
                &["(x ^ y)", "((y ^ z) ^ (x ^ z))"],
                10,
            ),
        ],
    );
}

#[test]
fn complex_to_xor_variants() {
    check(
        "i8",
        &[
            (
                "(x & ~y) - (x & y)",
                &["((x ^ y) - y)", "((x ^ y) + -y)"],
                20,
            ),
            ("x - 2*(x & y)", &["((x ^ y) - y)", "((x ^ y) + -y)"], 10),
            ("(x - y) - 2*(x | ~y)", &["((x ^ y) + 2)"], 10),
            ("(x - y) - 2*(~(~x & y))", &["((x ^ y) + 2)"], 10),
            ("(x + y) - (x ^ y)", &["(2 * (x & y))", "(2 * (y & x))"], 10),
            (
                "2 + 2*(y + (x | ~y))",
                &[
                    "(2 * (x & y))",
                    "(2 * (y & x))",
                    "((x & y) * 2)",
                    "((y & x) * 2)",
                ],
                10,
            ),
            ("-(x & y) - (x & y)", &["(-2 * (x & y))"], 10),
        ],
    );
}

#[test]
fn complex_to_not() {
    check(
        "i8",
        &[
            ("-x - 1", &["~x"], 10),
            ("~(x | y) | ~y", &["~y"], 10),
            ("(x - 1) - 2*x", &["~x"], 10),
            ("~(x ^ y) ^ y", &["~x"], 10),
            ("~(x - 1)", &["-x"], 10),
            ("(x & y) ^ (x | ~y)", &["~y"], 10),
            ("(x & ~y) | ~(x | y)", &["~y"], 10),
        ],
    );
}

#[test]
fn complex_to_nand_nor_xnor() {
    check(
        "i8",
        &[
            ("(x ^ y) | ~(x | y)", &["~(x & y)", "~(y & x)"], 10),
            ("~x | ~y", &["~(x & y)", "~(y & x)"], 10),
            ("~x & ~y", &["~(x | y)", "~(y | x)"], 10),
            ("(~x | ~y) | (x ^ y)", &["~(x & y)"], 10),
            ("~x | (x ^ y)", &["~(x & y)", "~(y & x)"], 10),
            (
                "(x & y) | ~(x | y)",
                &["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x & y) | (~x & ~y)",
                &["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x | y) ^ (~x | ~y)",
                &["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x | ~y) & (~x | y)",
                &["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x ^ ~y) - 2*(x & y)",
                &["~(x + y)", "(~x - y)", "(~y - x)"],
                10,
            ),
            (
                "((x ^ z) & (y ^ z)) | ((x ^ ~z) & (y ^ ~z))",
                &[
                    "(~x ^ y)",
                    "(x ^ ~y)",
                    "~(x ^ y)",
                    "((y ^ z) ^ (x ^ ~z))",
                    "((y ^ ~z) ^ (x ^ z))",
                ],
                10,
            ),
            ("((y ^ z) ^ (x ^ ~z))", &["(~x ^ y)", "~(y ^ x)"], 10),
        ],
    );
}

#[test]
fn complex_to_neg() {
    check(
        "i8",
        &[
            ("(x ^ y) - 2*(x | y)", &["-(x + y)", "-(y + x)"], 10),
            (
                "(-2 * (x | y)) + (x ^ y)",
                &["-(x + y)", "(-y - x)", "(-x - y)"],
                10,
            ),
            (
                "(x ^ (y | z)) - 2*((x | y) | z)",
                &[
                    "-(x + (y | z))",
                    "-((y | z) + x)",
                    "(-(y | z) - x)",
                    "(-x - (y | z))",
                ],
                10,
            ),
            ("(x & y) - (x + y)", &["-(x | y)"], 10),
            ("(x & y) - (x | y)", &["-(x ^ y)", "-(y ^ x)"], 10),
            ("(x + y) - 2*(x | y)", &["-(x ^ y)", "-(y ^ x)"], 10),
        ],
    );
}

#[test]
fn complex_to_x() {
    check(
        "i8",
        &[
            ("(x & y) + (x & ~y)", &["x"], 10),
            ("(x & y) ^ (x & ~y)", &["x"], 10),
            ("x & (x | y)", &["x"], 10),
            ("(x | y) - (~x & y)", &["x"], 10),
        ],
    );
}

#[test]
fn complex_multiply() {
    check(
        "i8",
        &[
            ("(x | y)*(x & y) + (x & ~y)*(y & ~x)", &["(x * y)"], 10),
            ("(x | y)*(x & y) + ~(x | ~y)*(x & ~y)", &["(x * y)"], 10),
        ],
    );
}

#[test]
fn complex_distributivity() {
    check(
        "i8",
        &[
            (
                "(x & z) | (y & z)",
                &["((x | y) & z)", "(z & (y | x))", "(z & (x | y))"],
                10,
            ),
            (
                "(x & z) ^ (y & z)",
                &["((x ^ y) & z)", "(z & (y ^ x))", "(z & (x ^ y))"],
                10,
            ),
            (
                "(x | y) + (x & ~y)",
                &["((x ^ y) + x)", "((y ^ x) + x)", "(x + (y ^ x))"],
                10,
            ),
        ],
    );
}

#[test]
fn complex_three_variable_or() {
    check(
        "i8",
        &[
            (
                "(~x | (~y & z)) + (x + (y & z)) - z",
                &[
                    "(x | (y | ~z))",
                    "(x | (~z | y))",
                    "(y | (x | ~z))",
                    "(y | (~z | x))",
                    "(~z | (x | y))",
                    "(~z | (y | x))",
                    "((y | ~z) | x)",
                    "((~z | y) | x)",
                    "((x | ~z) | y)",
                    "((~z | x) | y)",
                    "((x | y) | ~z)",
                    "((y | x) | ~z)",
                    "((((~y & z) & x) + -1) + -(~y & z))",
                    "(-(~y & z) + (((~y & z) & x) + -1))",
                    "((((~y & z) & x) + -1) - (~y & z))",
                ],
                10,
            ),
            (
                "((((~y & z) & x) + -1) + -(~y & z))",
                &[
                    "(x | (y | ~z))",
                    "((y | ~z) | x)",
                    "((~z | y) | x)",
                    "((x | y) | ~z)",
                    "(x | (~z | y))",
                ],
                10,
            ),
        ],
    );
}

#[test]
fn complex_full_adder() {
    check(
        "i8",
        &[
            ("(x^y^z) + 2*((x&y)|(x&z)|(y&z))", &["((x + y) + z)"], 10),
            ("(x^y^z) + 2*((x&y)|((x^y)&z))", &["((x + y) + z)"], 10),
        ],
    );
}

#[test]
fn complex_annihilation() {
    check(
        "i8",
        &[
            ("(a - 1) & (-a)", &["0"], 10),
            ("(a - 1) | (-a)", &["-1"], 10),
            ("(a - 1) ^ (-a)", &["-1"], 10),
        ],
    );
}

#[test]
fn complex_shift_distribution() {
    check(
        "i8",
        &[
            (
                "(x >> z) & (y >> z)",
                &["((x & y) >> z)", "((y & x) >> z)"],
                10,
            ),
            ("(x >> 3) ^ (y >> 3)", &["((x ^ y) >> 3)", "((y ^ x) >> 3)"], 10),
            ("(x << 3) | (y << 3)", &["((x | y) * 8)", "((y | x) * 8)"], 10),
            ("(x << 2) + (y << 2)", &["((x + y) * 4)", "((y + x) * 4)"], 10),
            ("(a - a) << b", &["0"], 10),
        ],
    );
}

#[test]
fn complex_constant_masks() {
    check(
        "i8",
        &[
            ("a & 0xff", &["a"], 10),
            ("a ^ 0xff", &["~a"], 10),
            ("a * 0x100", &["0"], 10),
            ("a | 0xff", &["-1"], 10),
            ("(x * x) & 3", &["(x & 1)"], 10),
        ],
    );
}

/// Batch E: constant-gated identities (sign-bit / disjoint / Mersenne mask).
#[test]
fn complex_constant_gated() {
    check(
        "i8",
        &[
            ("(x & 0xf0) + (x & 0x0f)", &["x"], 10),
            ("(x & 0xf0) | (x & 0x0f)", &["x"], 10),
            ("(x & 0xf0) ^ (x & 0x0f)", &["x"], 10),
            ("(x + 0x80) ^ 0x80", &["x"], 10),
            ("(x ^ 0x80) - 0x80", &["x"], 10),
            ("(x & 0x0f) + (x & 0x30)", &["(x & 0x3f)", "(0x3f & x)"], 10),
            (
                "((x & 7) * (y & 7)) & 7",
                &["((x * y) & 7)", "((y * x) & 7)"],
                10,
            ),
        ],
    );
}

#[test]
fn complex_demorgan_add_to_zero() {
    check(
        "i8",
        &[
            ("(~x - y) ^ ~(x + y)", &["0"], 10),
            ("(~x + y) ^ ~(x - y)", &["0"], 10),
            ("(0 - ~x) ^ (x + 1)", &["0"], 10),
        ],
    );
}

#[test]
fn complex_masked_merge() {
    check(
        "i8",
        &[
            (
                "((x ^ 0x12) & 1) | ((x ^ 8) & 0xfe)",
                &["((x ^ 8) | (1 & x))", "(x ^ 8)"],
                15,
            ),
            ("((x ^ 8) | (1 & x))", &["(x ^ 8)"], 15),
        ],
    );
}

#[test]
fn complex_misc() {
    check(
        "i8",
        &[
            (
                "(x - 7) + 11*(x - 8)",
                &[
                    "(-0x5f + (0xc * x))",
                    "((x * 0xc) + -0x5f)",
                    "((0xc * x) + -0x5f)",
                ],
                10,
            ),
            ("2*x - (x & ~y)", &["(x + (x & y))", "((x & y) + x)"], 10),
            (
                "(x & ~y) - 2*x",
                &["-(x + (x & y))", "(-(x & y) - x)", "-((x & y) + x)"],
                10,
            ),
            ("~x & (~x ^ c)", &["(x & ~c) ^ ~c", "~(x | c)"], 10),
            ("(x + y) - 2*(x | (y - 1))", &["((x ^ -y) + 2)"], 10),
        ],
    );
}

// ===========================================================================
// Extract-and-restart driver.
// ===========================================================================

/// The extract-and-restart driver keeps rewriting past what a single
/// saturation round achieves: each round reseeds a fresh e-graph with the
/// previous extraction, so a deliberately tiny iter_limit still converges.
/// The input is the motivating example from
/// https://secret.club/2022/08/08/eqsat-oracle-synthesis.html (at the time
/// of writing, one round at iter_limit=2 only reaches
/// `2*(x+y) - (x+y) + z`).
#[test]
fn extract_restart() {
    let cli = Cli {
        rule_compile: false,
        expr_compile: false,
        num_type: "i64".to_string(),
        iter_limit: 2,
        max_restarts: 2,
        expr: "".to_string(),
    };
    let case = "~(((x + y) + (~(((x + y) + x) + y))) + (-z))";
    let egg_expr = infix_to_egglog(case, true);
    let result = simplify(&egg_expr, &cli).unwrap();
    assert!(
        matches_expected(&["((x + y) + z)"], &result, true),
        "restart loop should fully reduce {case}, got {result}"
    );
    // The final answer must be a fixpoint: one more round on a fresh
    // e-graph seeded with it extracts the same term again.
    let seed = infix_to_egglog(&result, true);
    let again = simplify_round(&make_egg(&cli.num_type), &seed, &cli).unwrap();
    assert_eq!(seed, again, "simplify result is not a fixpoint");
}
