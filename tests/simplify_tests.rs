use eggy1::expr_convert::{ac_canon_infix, egglog_to_infix, infix_to_egglog};
use eggy1::{
    Cli, kz_add, kz_low, kz_mul, kz_shl, kz_shr, magic_div_s, magic_div_u, magic_s, magic_u, make_egg, pow2_div,
    simplify, simplify_round,
};

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
    // Expected forms written as `a + -k` print as `a - k`.
    expect.iter().any(|e| {
        ac_canon_infix(e) == rc || ac_canon_infix(&egglog_to_infix(&infix_to_egglog(e, true), &|n| n)) == rc
    })
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
        ..Default::default()
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
        ..Default::default()
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
            ("x >> 3 << 3", &["(x & -8)"], 10),
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
    // Shift amounts past the width must be rejected without overflowing `1u128 << p`.
    assert_eq!(magic_div_s(5, 100, 64, false), None);
    assert_eq!(magic_div_u(5, 64, 64, false), None);
    assert_eq!(magic_div_u(5, i64::MAX, 64, true), None);
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
        // Compiler form: constant second, sign mask subtracted.
        ("i32", "(mulhi(n, 0x66666667) >> 2) - (n >> 31)", "(n / 0xa)"),
        ("i32", "n - ((mulhi(n, 0x66666667) >> 2) - (n >> 31)) * 10", "(n % 0xa)"),
        // Remainder after the linear pass distributes the product.
        ("i32", "(n + (-10 * (mulhi(0x66666667, n) >> 2))) + ((n >> 31) * 10)", "(n % 0xa)"),
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
        ("u64", "mulhi(n, 0xcccccccccccccccd) >> 3", "(n / 0xa)"),
        ("u64", "n - (mulhi(n, 0xcccccccccccccccd) >> 3) * 10", "(n % 0xa)"),
    ]);
}

#[test]
fn shifts_in_multiply_form() {
    check_exact(&[
        ("u64", "(x >> 1) * 2", "(x & -2)"),
        ("i8", "(x >> 3) * 8", "(x & -8)"),
        ("u8", "(2 * x) >> 1", "(x & 0x7f)"),
        // Arithmetic `>>` copies bit 62 into the sign bit: no mask form.
        ("i64", "(2 * x) >> 1", "((2 * x) >> 1)"),
        ("u64", "(x & 0xffffffffffffffe0) >> 5", "(x >> 5)"),
        ("u8", "(x & 0x3f) * 4", "(4 * x)"),
        ("u8", "(x & 0x1f) * 4", "(4 * (x & 0x1f))"),
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
            ("(a * 4) / 4", &["(a & 0x3f)"], 10), // NOT a
            ("x / 255", &["(x / 0xff)"], 10),                         // NOT -x (0xff != -1)
            ("(a >> 255) >> 1", &["((a >> 0xff) >> 1)", "0"], 10),    // NOT a
            ("(a << 255) << 1", &["((a << 0xff) * 2)", "0"], 10),     // NOT a
            ("(a >> 2) >> 3", &["(a >> 5)"], 10),                     // in-range combine still works
            ("5 / 256", &["(5 / 0)"], 10),                            // 256 is 0 in u8: no fold, no panic
            ("5 % 256", &["(5 % 0)"], 10),
        ],
    );
}

/// Every bit a kz-* result marks as zero must be zero in the real result, for
/// any input masks that are themselves correct (exact `!a`, or a subset of it).
#[test]
fn known_zero_transfer_functions() {
    fn check_width(w: i64, values: &[(i64, i64)], subsets: &[i64]) {
        let m = if w == 64 { -1 } else { (1i64 << w) - 1 };
        let sext = |v: i64| (v << (64 - w)) >> (64 - w);
        let ok = |z: i64, v: i64, what: &str| assert_eq!(z & v & m, 0, "w={w} {what}: kz={z:#x} value={v:#x}");
        for &(a, b) in values {
            let (a, b) = (sext(a), sext(b));
            for &sa in subsets {
                for &sb in subsets {
                    let (za, zb) = (!a & sa, !b & sb);
                    ok(kz_add(za, zb, w), a.wrapping_add(b), "add");
                    ok(kz_add(za, zb, w), a.wrapping_sub(b), "sub");
                    ok(kz_mul(za, zb, w), a.wrapping_mul(b), "mul");
                }
                let za = !a & sa;
                ok(kz_low(za, w), a.wrapping_neg(), "neg");
                ok(kz_low(za, w), a.wrapping_mul(b), "mul one side");
                for k in 0..w {
                    ok(kz_shl(za, k, w).unwrap(), a << k, "shl");
                    ok(kz_shr(za, k, w, true).unwrap(), a >> k, "ashr");
                    ok(kz_shr(za, k, w, false).unwrap(), ((a as u64 & m as u64) >> k) as i64, "lshr");
                }
            }
        }
        assert_eq!(kz_shl(0, w, w), None);
        assert_eq!(kz_shr(0, -1, w, false), None);
    }
    let subsets = [-1, 0, 0x0f, 0xf0, 0x55, -2, 0x7f, -0x80, 0x3c];
    let all8: Vec<(i64, i64)> = (0..256).flat_map(|a| (0..256).map(move |b| (a, b))).collect();
    check_width(8, &all8, &subsets);
    let mut r = 0x9e3779b97f4a7c15u64;
    let mut next = || {
        r ^= r << 13;
        r ^= r >> 7;
        r ^= r << 17;
        let x = r as i64;
        match r % 4 {
            0 => x & !(1i64 << (r >> 58)).wrapping_sub(1),
            1 => x & 0xff,
            _ => x,
        }
    };
    let pairs: Vec<(i64, i64)> = (0..4000).map(|_| (next(), next())).collect();
    for w in [16, 32, 64] {
        check_width(w, &pairs, &subsets);
    }
}

#[test]
fn known_bits() {
    check(
        "u32",
        &[
            ("((x << 8) + (y & 0xff)) ^ ((x << 8) | (y & 0xff))", &["0"], 10),
            ("((x << 8) + (y & 0xff)) - ((x << 8) ^ (y & 0xff))", &["0"], 10),
            ("((x & 0xff) << 8) & 0xff00", &["((x & 0xff) << 8)", "((x & 0xff) * 0x100)"], 10),
            ("(x & 0xff) >> 8", &["0"], 10),
            ("((x & 0xf0) * 16) & 0xf", &["0"], 10),
            ("(x * 4 + y * 8) & 3", &["0"], 10),
        ],
    );
    check(
        "i32",
        &[
            ("(x & 0xff) >> 8", &["0"], 10),
            // Sign bit not known zero: arithmetic `>>` keeps it, must NOT fold to 0.
            ("(x & -0x100) >> 8", &["(x >> 8)"], 10),
        ],
    );
    check("i8", &[("(x << 4) & 15", &["0"], 10)]);
}

/// Linear MBA rebuilt from its values on {0,1}^n (src/linear_mba.rs); none of
/// these match a hand-written rule.
#[test]
fn linear_mba() {
    check(
        "i64",
        &[
            ("(x ^ y) + 3*(x & y) + (~x & y)", &["(x + (2 * y))"], 10),
            ("7*(x & y) - 5*(x | y) + 3*(x ^ y) + 2*(~x | y) - 2*~x + 2*x", &["((-2 * y) + (8 * (x & y)))", "((8 * (x & y)) - (2 * y))"], 10),
            (
                "(x | y) + (z & u) - (x & ~y) + 2*((z ^ u) & x) - 2*(x & (z | u)) + 2*(x & z & u)",
                &["(y + (z & u))"],
                10,
            ),
            // The hidden zero spans 5 and 6 leaves, so no smaller sub-region removes it.
            (
                "u + v + ((x ^ y) & (z | u | v)) + ((x ^ y) & ~(z | u | v)) - (x ^ y)",
                &["(u + v)"],
                10,
            ),
            (
                "w + ((x ^ y) & (z | u | v)) + ((x ^ y) & ~(z | u | v)) - (x & ~y) - (~x & y)",
                &["w"],
                10,
            ),
            // Overlapping terms (MBA-Obfuscator linear samples).
            (
                "7*(x|y)-5*~(x&~y)+5*(x|~y)+1*~y+1*y-3*~(x^y)+1*~x+1*~(x|y)+7*~(x|~y)-3*(x&~y)-6*(x&y)",
                &["((0xb * (x ^ y)) - x)"],
                10,
            ),
            // A term that is non-zero at 0.
            (
                "-7*~(x&y)+1*~(x&~x)-2*~x+1*y-1*~(x^y)-7*~(x&~y)-2*x-7*~y-1*(x|y)+20*~(x|~y)+21*(x&~y)+9*(x&y)",
                &[
                    "((5 * (x ^ y)) + (-0x17 * ~(x | y)))",
                    "((5 * (x ^ y)) - (0x17 * ~(x | y)))",
                    "((-0x17 * ~(x & y)) + (0x1c * (x ^ y)))",
                ],
                10,
            ),
            // Variables {x, y, z} and {a, t} do not interact, so they are rebuilt separately (NeuReduce).
            (
                "2*(~y|z)-(~x&y|~z)-3*(x&y^~z)-(x&~y&~z)+3*(y|~z)-2*(x&y|z)-(~x)-(x&y^z)-(a&~t)+a",
                &["((a & t) - ((y ^ z) + ((y ^ z) & ~x)))"],
                10,
            ),
            // 8 leaves: rebuilt per group of leaves that share a conjunction.
            (
                "(((((g & e) * 3) + ((((5 * ~(b | a)) + (-3 * ~a)) + (((((c | ~e) + (((b | a) * 5) + (-3 * a))) + (-2 * (f ^ ~d))) + (-3 * (g & e))) - c)) - h)) - (c | ~e)) - (b | e))",
                &["(((2 * (f ^ d)) - c) - ((b | e) + h))", "((((2 * (f ^ d)) - c) - h) - (b | e))", "((((2 * (f ^ d)) - (b | e)) - c) - h)"],
                10,
            ),
        ],
    );
    check(
        "i32",
        &[
            ("5*(x | y) - 3*(x ^ y) - 2*(x & ~y) + 7", &["(((2 * y) + (3 * (x & y))) + 7)"], 10),
            // `a*b` is not linear: it is treated as one opaque variable.
            ("((a*b) ^ c) + 3*((a*b) & c) + (~(a*b) & c)", &["((a * b) + (2 * c))"], 10),
        ],
    );
}

/// Polynomial MBA expanded in the conjunction basis and rebuilt
/// (src/poly_mba.rs). The first two are from the MBA-Obfuscator poly samples.
#[test]
fn poly_mba() {
    let cases: &[(&str, &[&str], usize)] = &[
        (
            "-8*~y*(x&y)-8*~y*(x&~y)+10*~y*x+3*~y*~(x|y)+8*(x^y)*(x&y)+8*(x^y)*(x&~y)-10*(x^y)*x-3*(x^y)*~(x|y)-3*~y*(x|~y)-1*~y*~x+3*(x^y)*(x|~y)+1*(x^y)*~x",
            &["((x ^ ~y) - y)", "((~x ^ y) - y)", "(~y - (x ^ y))", "(x + ~((x | y) * 2))"],
            10,
        ),
        (
            "-6*(x^y)*(x&y)-7*(x^y)*(x&~y)+5*(x^y)*(x|~y)-2*(x^y)*~(x|~y)+12*(x&~y)*(x&y)+14*(x&~y)*(x&~y)-10*(x&~y)*(x|~y)+4*(x&~y)*~(x|~y)+1*(x^y)*~(x&y)-7*(x^y)*~(x|y)-2*(x&~y)*~(x&y)+14*(x&~y)*~(x|y)",
            &["(y - x)"],
            10,
        ),
        // Common factor pulled out, then the linear cofactor rebuilt.
        (
            "(x|y)*(x^y) + (x&y)*(x^y) - y*(x^y) + 2*(x|y)*(x&y) + 2*(x&y)*(x&y) - 2*y*(x&y)",
            &["(x * (x + y))"],
            10,
        ),
        ("((x ^ y) + 2*(x & y)) * ((x | z) + (x & z)) - x*z", &["((x * (x + y)) + (y * z))"], 10),
        ("(x&y)*(x|y) + (x&~y)*(~x&y) - x*y + (x ^ z) + 2*(x & z)", &["(x + z)"], 10),
    ];
    check("i64", cases);
    check("u8", cases);
}

/// Semi-linear MBA: bitwise operations with constant operands, rebuilt per bit
/// position (src/linear_mba.rs, `semi_linear`). The last two are from
/// scripts/gen-semi-linear.py.
#[test]
fn semi_linear_mba() {
    let cases: &[(&str, &[&str], usize)] = &[
        ("3*(x | 0x5c) - 2*(x & 0x5c) - (x ^ 0x5c) - 2*(x & ~0x5c)", &["(0xb8 - (x & 0x5c))", "(0x5b - (-0x5d | x))"], 10),
        (
            "3*(x | y) - 2*(((z ^ 0xf0) + 0xf) - ((z ^ 0xf0) | 0xf)) - 3*(((y | 0x5e) | ~(x)) - ((y | 0x5e) & ~(x))) + 3*((y | 0x5e) ^ ~(x)) + 2*((z ^ 0xf0) & 0xf)",
            &["(3 * (x | y))"],
            10,
        ),
        (
            "-((z & 0xff00) | 0x71) - 3*~((y ^ x)) + 2*((x + y) - (x & y)) + ((((z + 0xff00) - (z | 0xff00)) + 0x71) - ((z & 0xff00) & 0x71)) + 3*(-((y ^ x)) - 0x1)",
            &["(2 * (x | y))"],
            10,
        ),
    ];
    check("i64", cases);
    check("u8", cases);
}

/// Semi-linear regions whose shortest form is one bitwise term with several constants.
#[test]
fn semi_linear_bitwise_shape() {
    check(
        "i64",
        &[
            (
                "((((((((x | y) & (z ^ z)) + (((x ^ 0x4d) | 0xf) | ((y & 0xf592) & 0x1253))) + (0x2 * (((y ^ z) | (x & 0xe65d)) - ((y ^ z) & (x & 0xe65d))))) - (0x3 * ((((x + 0xe1) - (x & 0xe1)) + ((y | y) - (y & y))) - ((x | 0xe1) & (y ^ y))))) - (0x2 * ((y ^ z) ^ (x & 0xe65d)))) - (((x | y) + (z ^ z)) - ((x | y) | (z ^ z)))) + (0x3 * ((x | 0xe1) | (y ^ y))))",
                &["(0x40 ^ (x | ((y & 0x1010) + 0xf)))", "(((x | y) & 0x101f) | (x ^ 0x4f))"],
                10,
            ),
            (
                "((((((-((0x2 * ~((z ^ z)))) + (0x2 * ((((z | 0xf0) ^ (y & x)) + (-((z ^ x)) - 0x1)) - (((z | 0xf0) ^ (y & x)) | ~((z ^ x)))))) - ((((y + 0x2156) - (y | 0x2156)) + 0x5c) - ((y & 0x2156) & 0x5c))) - (0x5 * ((((x + 0xbf) - (x & 0xbf)) + 0xff00) - ((x | 0xbf) & 0xff00)))) + ((y & 0x2156) | 0x5c)) + (0x5 * ((x | 0xbf) | 0xff00))) + (0x2 * (-(((z | z) - (z & z))) - 0x1)))",
                &["(2 * ((z ^ ~x) & ((z & (y ^ -0xf1)) ^ 0xf0)))", "(2 * (((z & (y ^ -0xf1)) ^ 0xf0) & ~(z ^ x)))", "(2 * ((~x ^ z) & ((z & y) ^ (z | 0xf0))))"],
                10,
            ),
        ],
    );
}

/// Linear MBA whose values share a factor `2^k` is rebuilt as `2^k·L`.
#[test]
fn linear_common_power_of_two() {
    check(
        "i64",
        &[
            ("2*x - 4*(x & y)", &["(2 * ((x ^ y) - y))"], 10),
            ("(x - (x & y)) * 8 - 8 * (y & ~x)", &["(8 * (x - y))"], 10),
        ],
    );
}

/// Shapes of size 15, leaves that cancel out, 4-variable bitwise functions split
/// as `g(A) & h(B)`, blocks that must change together, leaf sets rebuilt apart, and
/// constants cut to the bits that matter.
#[test]
fn semi_linear_large_shapes_and_splits() {
    check(
        "i64",
        &[
            (
                "((((((-(((((y | y) - (y & y)) + ((y + 0xe3) - (y & 0xe3))) - ((y ^ y) | (y | 0xe3)))) - (0x2 * (((y & 0xff00) | (x & 0xcc)) | ((y & x) ^ (z ^ 0x7f))))) + (0x2 * ((y | y) & (y | x)))) + ((y | 0x82) | ~(x))) - ((y | 0x82) | ~(x))) + ((y ^ y) & (y | 0xe3))) - (0x2 * ((((y + y) - (y & y)) + ((y + x) - (y & x))) - ((y | y) | (y | x)))))",
                &["(-2 * (((x & 0xcc) + (y & 0xff00)) | ((y & x) ^ (z ^ 0x7f))))"],
                10,
            ),
            (
                "((((((((0x2 * (((y & x) | 0xf0) - ((y & x) & 0xf0))) - (0x5 * ((((y | 0x2b09) - (y & 0x2b09)) + 0x1946) - ((y ^ 0x2b09) | 0x1946)))) - (0x2 * ((((y + 0xbf0f) - (y & 0xbf0f)) + ((z | 0xbae0) - (z & 0xbae0))) - ((y | 0xbf0f) | (z ^ 0xbae0))))) - (0x2 * ((y & x) ^ 0xf0))) + (0x3 * ((((w ^ 0x7660) & (y ^ w)) + (((x ^ 0xff00) | (w & y)) - ((x ^ 0xff00) & (w & y)))) - (((w ^ 0x7660) & (y ^ w)) & ((x ^ 0xff00) ^ (w & y)))))) + (0x5 * ((y ^ 0x2b09) & 0x1946))) + (0x2 * w)) + (0x2 * ((y | 0xbf0f) & (z ^ 0xbae0))))",
                &["((3 * (((x ^ 0xff00) ^ (w & y)) | ((w ^ 0x7660) & (y ^ w)))) + (2 * w))"],
                10,
            ),
            (
                "(((((((0x3 * ((((w + 0x4856) - (w | 0x4856)) + 0x28) - ((w & 0x4856) | 0x28))) + (0x2 * ((z | 0xff00) ^ 0xf6))) - ((((w ^ x) | (x & y)) + ~((y ^ z))) - (((w ^ x) | (x & y)) | ~((y ^ z))))) + (0x3 * ((((w + w) - (w & w)) + ((y | w) - (y & w))) - ((w | w) | (y ^ w))))) - (0x2 * (((z | 0xff00) | 0xf6) - ((z | 0xff00) & 0xf6)))) - (0x3 * ((w & 0x4856) & 0x28))) - (0x3 * ((w | w) & (y ^ w))))",
                &["-(((w ^ x) | (w & z)) & (~y ^ z))"],
                10,
            ),
            (
                "(((((((((0x2 * (-(((a + c) - (a & c))) - 0x1)) + (0x2 * ((((e + e) - (e | e)) + ((c + d) - (c & d))) - ((e & e) | (c | d))))) + (0x2 * (-(((e + g) - (e | g))) - 0x1))) + (0x2 * (((b | c) | (g | b)) - ((b | c) & (g | b))))) - (0x2 * ((b | c) ^ (g | b)))) + (0x2 * ((((d | d) - (d & d)) + ((f + f) - (f & f))) - ((d ^ d) & (f | f))))) - (0x2 * ((d ^ d) | (f | f)))) - ((((a | f) - (a & f)) + ((a + d) - (a & d))) - ((a ^ f) & (a | d)))) + ((a ^ f) | (a | d)))",
                &["(((((e & (c | d)) - (a | c)) - (e & g)) * 2) + -4)"],
                10,
            ),
            (
                "(((((((-((0x3 * (~(x) & 0xdcab))) + (0x3 * ((((y + 0xe45c) - (y | 0xe45c)) + 0x1c5f) - ((y & 0xe45c) | 0x1c5f)))) + (0x3 * (~(z) & 0x3b))) - (0x3 * (((-(z) - 0x1) + 0x3b) - (~(z) | 0x3b)))) - (0x3 * ((y & 0xe45c) & 0x1c5f))) + (0x3 * ((((v + 0xbb) - (v & 0xbb)) + ((v + v) - (v | v))) - ((v | 0xbb) & (v & v))))) - ((((z + 0xf0) - (z | 0xf0)) + ((w + 0xe734) - (w | 0xe734))) - ((z & 0xf0) & (w & 0xe734)))) + (0x3 * (((-(x) - 0x1) + 0xdcab) - (~(x) | 0xdcab))))",
                &["(((0xbb | v) * 3) - ((w & 0xe734) | (z & 0xf0)))"],
                10,
            ),
            (
                "((((((((((w ^ x) | 0x5c) - ((w ^ x) & 0x5c)) - ((w ^ x) ^ 0x5c)) - ((((z | 0xcc) - (z & 0xcc)) + 0x5e) - ((z ^ 0xcc) | 0x5e))) + ((~(v) | (v ^ 0x70)) - (~(v) & (v ^ 0x70)))) - (0x3 * ((((w + 0x85) - (w | 0x85)) + 0x72) - ((w & 0x85) & 0x72)))) - (~(v) ^ (v ^ 0x70))) + ((w ^ 0xa1) ^ 0x33)) + (0x3 * ((w & 0x85) | 0x72)))",
                &["((0x92 ^ w) - ((z ^ 0xcc) & 0x5e))", "((0x12 ^ (z | -0x5f)) - (w ^ -0x93))"],
                10,
            ),
        ],
    );
}

/// Carry and lowest-set-bit identities (`x & -(x & -(x & y)) = x & y`), proved bit by bit,
/// also with bitwise subterms as operands.
#[test]
fn t_function_identities() {
    check(
        "i64",
        &[
            ("(x & (- (x & ((- (x + (- (((x | (x | y)) | (((x | ((~ (x & (- (~ y)))) & y)) + (x | y)) + (- (x | y)))) + (- y))))) ^ (~ (y | (y | (~ y))))))))", &["(x & y)"], 10),
            ("((((x & (- x)) | ((x & (- x)) & (~ ((~ (x | y)) | ((~ (- (~ (x | y)))) & ((~ (x | y)) + (~ (x | y)))))))) | (~ ((~ (x | y)) | ((~ (- (~ (x | y)))) & ((~ (x | y)) + (~ (x | y))))))) | (~ ((~ (x | y)) | ((~ (- (~ (x | y)))) & ((~ (x | y)) + (~ (x | y)))))))", &["(x | y)"], 10),
            ("(~ ((((~ x) + (- y)) + y) + (- ((((~ x) + (- y)) + y) + (- ((((~ x) + (- y)) + y) ^ (~ (~ (y | (- ((- y) | (y + y))))))))))))", &["(x ^ y)"], 10),
            (
                "(((((-((0x2 * ((z & z) | (z | y)))) + ((x ^ z) & -(((x ^ z) & -(((x ^ z) & (y ^ z))))))) + (0x2 * (-(((z + z) - (z & -((z & -((z & z))))))) - 0x1))) + (0x2 * ((((z + z) - (z | z)) + ((z + y) - (z & y))) - ((z & z) & (z | y))))) - (0x2 * (~(z) | (x | x)))) + (0x2 * (((-(z) - 0x1) + ((x + x) - (x & x))) - (~(z) & (x | x)))))",
                &["((2 * ~z) + ((x ^ z) & (y ^ z)))"],
                10,
            ),
        ],
    );
}

/// Arithmetic leaves that are linear in the other leaves (`a - d`, `(b ^ d) - b`).
#[test]
fn related_arithmetic_leaves() {
    check(
        "i64",
        &[
            ("((b*b) & ~b) - ((((b ^ d) - b) & (b | (b * b))) - (b ^ d))", &["((b * b) | (b | ((b ^ d) - b)))"], 10),
            ("(3*a - (d | a) - ((a - d) & (a + (d & a))))", &["((a - d) | (a + (d & a)))"], 10),
        ],
    );
}

/// Related arithmetic leaves in regions of more than 6 leaves, where cancelling a leaf
/// of `L` needs `μ` other than ±1, ±2 (here -3), or the region has constant masks.
#[test]
fn related_leaves_in_wide_regions() {
    check(
        "i64",
        &[
            (
                "(((y + ((~(z ^ x) - u) - (u | w))) * 3) + (((((((z ^ x) + u) + v) - y) & ((u | w) + v)) - v) * 6))",
                &["(3 * (((u | w) + v) ^ (~u + ((y - v) - (z ^ x)))))"],
                10,
            ),
            (
                "((((v + 1) * y) + (((t & w) - (v | u)) + (-2 * ((y | z) & (((t & w) - (v | u)) + ((y & z) + (y | 0xdeadbeef))))))) + ((y | 0xdeadbeef) + z))",
                &["((y * v) + ((y | z) ^ (((t & w) - (v | u)) + ((y & z) + (y | 0xdeadbeef)))))"],
                10,
            ),
        ],
    );
}

/// Arithmetic leaves that are complements of a linear MBA written out in the region
/// (`c + ~b` = `~(b - c)`, `~h - e` = `~(h + e)`).
#[test]
fn complemented_arithmetic_leaves() {
    check(
        "u8",
        &[
            ("((f | a) & (c + ~b)) + b - c", &["((f | a) | (b - c))"], 10),
            ("(a & e) + (a & ~c) + ((f | a) & (c + ~b)) + b", &["(((a & e) + (a | c)) + (a | (f | (b - c))))"], 10),
        ],
    );
    check(
        "i64",
        &[
            ("p - ((~h - e) & (c ^ j)) - h", &["((p - ((c ^ j) | (h + e))) + e)"], 10),
            (
                "((((((c | f) * (b * a)) - (d & a)) - d) - a) - ((~d + c) & (d | e))) + ((~c ^ e) & (a + c))",
                &["(((((c | f) * (b * a)) - (d & a)) - (d | ((d - c) | e))) - ((e ^ c) & (a + c)))"],
                10,
            ),
        ],
    );
    // `L = (b | i) + 2*b` relates without dropping a leaf.
    check(
        "u32",
        &[(
            "((h + l) ^ ((i | (l ^ e)) ^ (b & (i ^ c)))) + b + (2 * (b | ((h + l) & i))) - (((b | i) + (2 * b)) & ~g)",
            &["((((b | i) + (2 * b)) & g) + ((h + l) ^ ((~i & (l ^ e)) ^ (b & c))))"],
            10,
        )],
    );
}

/// Related arithmetic leaves in regions of more than 16 leaves, on the terms around them.
#[test]
fn related_leaves_past_wide_limit() {
    check(
        "u32",
        &[(
            "(p1^q1)+(p2^q2)+(p3^q3)+(p4^q4)+(p5^q5)+(p6^q6)+(p7^q7)+(p8^q8) - b - (~(e + b) & y) - e",
            &["(((((((((p1 ^ q1) + (p2 ^ q2)) + (p3 ^ q3)) + (p4 ^ q4)) + (p5 ^ q5)) + (p6 ^ q6)) + (p7 ^ q7)) + (p8 ^ q8)) - ((e + b) | y))"],
            10,
        )],
    );
    check(
        "i64",
        &[(
            "(a+b+c+d+e+f+g+h+i) + (((p ^ q) | (r & (s ^ (t | (u & v))))) & (-1 - a - b - c - d - e - f - g - h - i))",
            &["(((((((((a + b) + c) + d) + e) + f) + g) + h) + i) | ((p ^ q) | (r & (s ^ (t | (u & v))))))"],
            10,
        )],
    );
    // The operand beside `~A` shares leaves with `A`.
    check(
        "i64",
        &[(
            "(a|b) - (c&d) + (e^f) - (g*h) + k + (m|n) - (o&p) + q + ((~(a|b) + (c&d) - (e^f) + (g*h) - k - (m|n) + (o&p) - q) & (((a - r) | (s ^ t)) ^ (b & u)))",
            &["(((q - (o & p)) + (((k - (g * h)) + (((a | b) - (c & d)) + (e ^ f))) + (m | n))) | (((a - r) | (s ^ t)) ^ (b & u)))"],
            10,
        )],
    );
}

/// The last extraction still holds a region the linear pre-pass rebuilds.
#[test]
fn extra_round_after_last_extraction() {
    check("i64", &[("(x & (- ((x | y) & (~ (~ (((x | y) & (- y)) | (- y)))))))", &["(x & y)"], 10)]);
}

/// Semi-linear rebuilds whose constant term is absorbed into a bitwise term.
#[test]
fn semi_linear_constant_absorbed() {
    check(
        "i64",
        &[
            ("-2*(x & ~0xe5) - 0x1ca", &["(-2 * (x | 0xe5))"], 10),
            ("-3*(x & 0xa3) + 0x1e9", &["(3 * (~x & 0xa3))"], 10),
            ("x + 2*(x & 0x95) - 0x95", &["((2 * x) - (x ^ 0x95))"], 10),
            ("((y & ~0x36) ^ 0x627e) - 0x34", &["((y & -0x37) ^ 0x624a)"], 10),
            ("3*z + (y & ~0xff3a) - (0xff00 & y) + 0xff3a", &["((0xff00 ^ (y | 0x3a)) + (3 * z))", "(((y & -0x3b) ^ 0xff3a) + (3 * z))"], 10),
        ],
    );
    // A multiple of a leaf added to one bitwise term splits its bits into
    // several tables; subtracting it first leaves one term.
    check(
        "i64",
        &[
            ("(0x7fffffffffff004f & x) + 0xffb0 + (x & 0x7fffffffffffc6ff)", &["((0x3900 ^ (x | 0xc6b0)) + x)"], 10),
            ("x + (-0x7ffffffffffffff8 & z) - ((0x7fffffffffffff47 & z) + 0xb8)", &["(x - ((z | 0xb0) ^ 8))"], 10),
            ("(~x | 0x5c00) - (0xa300 & x) + 0xfb72", &["((0x5871 - x) + ((x ^ 0xa378) & 0xff00))", "((0x5871 - x) + ((x & 0xff00) ^ 0xa300))"], 10),
        ],
    );
    // The top bits only matter modulo 2 or 4, so they fit more than one group.
    check(
        "u8",
        &[
            (
                "7*((((x | 0x61) - (x & 0x61)) + 0xd9f) - ((x ^ 0x61) | 0xd9f)) + ((x ^ 0xe6) & ~(x)) \
                 - ((((x | 0xe6) - (x & 0xe6)) + (-(x) - 0x1)) - ((x ^ 0xe6) | ~(x))) + 3*((y | 0x61) - (y & 0x61)) \
                 - 7*((x ^ 0x61) & 0xd9f)",
                &["(3 * (y ^ 0x61))"],
                10,
            ),
            (
                "-7*(~(y) ^ ~(y)) + 7*((~(y) | ~(y)) - (~(y) & ~(y))) + ~((y | x)) - (-(((y + x) - (y & x))) - 0x1) \
                 + y + ((y | 0xbf) - (y & 0xbf)) - 3*(-((-(x) - 0x1)) - 0x1) + 3*~(~(x))",
                &["((y ^ 0xbf) + y)"],
                10,
            ),
            (
                "5*((y ^ 0xf) & 0xb768) - (x ^ 0xa1) - 5*(((y ^ 0x1c) | 0x4b) - ((y ^ 0x1c) & 0x4b)) \
                 + 5*((y ^ 0x1c) ^ 0x4b) - 5*((((y | 0xf) - (y & 0xf)) + 0xb768) - ((y ^ 0xf) | 0xb768))",
                &["-(x ^ 0xa1)"],
                10,
            ),
        ],
    );
}

/// `c·b + c = -c·~b` drops the constant term.
#[test]
fn constant_into_not() {
    check(
        "i64",
        &[
            ("4*((x^z) & (y^z)) + 4", &["(-4 * ~((x ^ z) & (y ^ z)))"], 10),
            ("2 + x*2", &["(-2 * ~x)"], 10),
        ],
    );
}

/// Non-polynomial MBA: a linear MBA identity over A, B with arithmetic
/// expressions substituted for A and B (MBA-Obfuscator nonpoly samples). The
/// arithmetic operands of bitwise operations are leaves of the outer region.
#[test]
fn nonpoly_mba() {
    check(
        "i64",
        &[
            (
                "9*((-1*(x^y))&(-1*(x|y)))+19*((-1*(x^y))&~(-1*(x|y)))-11*((-1*(x^y))^(-1*(x|y)))-7*((-1*(x^y))|~(-1*(x|y)))+7*~((-1*(x^y))|(-1*(x|y)))+12*~((-1*(x^y))|~(-1*(x|y)))-3*(x&~y)-4*(x&y)",
                &["((-3 * x) + (-2 * (x | y)))", "((-3 * x) - (2 * (x | y)))"],
                10,
            ),
            (
                "-9*((5*y)&(1*~(x&~y)))-10*((5*y)&~(1*~(x&~y)))+11*~((5*y)&(1*~(x&~y)))+11*~((5*y)^(1*~(x&~y)))-22*~((5*y)|(1*~(x&~y)))-10*~((5*y)|~(1*~(x&~y)))-1*~(x|y)-17*~(x|~y)-17*(x&y)",
                &["(-0xb * y)"],
                10,
            ),
            (
                "-3*((3*(x|y))&(1*x))+5*~((3*(x|y))&~(1*x))-6*~((3*(x|y))|(1*x))-4*~((3*(x|y))|~(1*x))+1*~(1*x)-1*~(x&y)-4*(x&~y)-5*(x&y)",
                &["((3 * (y & ~x)) + 1)"],
                10,
            ),
        ],
    );
}

#[test]
fn lowest_set_bit_mask() {
    check("i8", &[("y + (x & -(x & -x))", &["(x + y)"], 10)]);
    check("u64", &[("(x & -(x & -x)) ^ x", &["0"], 10)]);
    let cases: &[(&str, &[&str], usize)] = &[
        ("(-y & ~(y & (2*y))) + y", &["0"], 10),
        ("x ^ ((2*y) & (y & -y))", &["x"], 10),
        ("((x - 1) | (x & (2*x))) - x", &["-1", "0xff"], 10),
        ("(((-2*x) & (x - 1)) | x) - x", &["0"], 10),
        ("-(y | -(x|y)) | y", &["(x | y)"], 10),
    ];
    check("i64", cases);
    check("u8", cases);
}

#[test]
fn trailing_zeros_of_multiple() {
    let cases: &[(&str, &[&str], usize)] = &[
        ("(x * y) & (-y | y)", &["(x * y)"], 10),
        ("2 - ((((2 - y*x) & ~k) & 1) | (((y | -y) & (-x*y)) + 2))", &["(x * y)"], 10),
        ("((x << z) * y + (y & k) * 3) & (y | ~(y - 1))", &["(((x << z) * y) + ((y & k) * 3))"], 10),
        ("(x * y) & -(y & -y)", &["(x * y)"], 10),
        ("(x + y) & (y | -y)", &["((x + y) & (y | -y))"], 10),
    ];
    check("i64", cases);
    check("u8", cases);
}

#[test]
fn square_parity() {
    check(
        "i8",
        &[
            ("(x*x) & 1", &["(x & 1)"], 10),
            ("(x*x) & 2", &["0"], 10),
            ("(x*(x+1)) & 1", &["0"], 10),
            ("(x*~x) & 1", &["0"], 10),
        ],
    );
}

#[test]
fn shift_then_mask() {
    check("i32", &[
        ("(x >> 4) << 4", &["(x & -0x10)"], 10),
        // Signed `>>` sign-extends, so this must NOT become a mask.
        ("(x << 4) >> 4", &["((x * 0x10) >> 4)", "((x << 4) >> 4)"], 10),
    ]);
    check("u32", &[("(x << 4) >> 4", &["(x & 0xfffffff)"], 10)]);
}

#[test]
fn disjoint_masks_two_vars() {
    check(
        "u32",
        &[
            ("((hi & 0xff00) + (lo & 0xff)) ^ ((hi & 0xff00) | (lo & 0xff))", &["0"], 10),
            ("((hi & 0xff00) ^ (lo & 0xff)) - ((hi & 0xff00) | (lo & 0xff))", &["0"], 10),
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
            ("(x ^ y) - 2*(x | y)", &["-(x + y)", "-(y + x)", "(-x - y)"], 10),
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
                    "((0xc * x) - 0x5f)",
                ],
                10,
            ),
            ("2*x - (x & ~y)", &["(x + (x & y))", "((x & y) + x)"], 10),
            (
                "(x & ~y) - 2*x",
                &["-(x + (x & y))", "(-(x & y) - x)", "-((x & y) + x)", "(-x - (x & y))"],
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
        ..Default::default()
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
    let again = simplify_round(&make_egg(&cli.num_type), &seed, &cli, true).unwrap();
    assert_eq!(seed, again, "simplify result is not a fixpoint");
}

/// A scaled semi-linear region, split sets that each absorb part of the constant,
/// two bitwise terms over shared leaves, and a T-function identity of size 7.
#[test]
fn semi_linear_scaled_pairs_and_tfunc() {
    check(
        "i64",
        &[
            ("(-((z | y) | (x & 0xff00)) - z) << 5", &["(-0x20 * (((z | y) | (x & 0xff00)) + z))"], 10),
            ("((((((((0x2 * (-(((u + y) - (u | y))) - 0x1)) - (0x3 * ((((v + v) - (v | v)) + 0xff00) - ((v & v) & 0xff00)))) + (0x3 * ((v & v) | 0xff00))) + (~(u) & 0xa95e)) - (((-(u) - 0x1) + 0xa95e) - (~(u) | 0xa95e))) - (0x2 * (((u ^ 0x5b34) + 0xf0) - ((u ^ 0x5b34) & 0xf0)))) - (0x2 * ~((u & y)))) + (0x3 * ((x | 0x30) ^ 0x438a)))", &["((3 * ((x & -0x31) ^ 0x43ba)) + (-2 * ((u & -0xf1) ^ 0x5bf4)))"], 10),
            ("(((((((-((0x7 * ((w | v) ^ 0x4114))) + (0x2 * ((w | 0x3c) | 0x16))) + ((z | y) & 0xb5)) + (0x7 * (((w | v) | 0x4114) - ((w | v) & 0x4114)))) + (((x & y) | 0x59) - ((x & y) & 0x59))) + (0x2 * (-(((x + 0x6) - (x | 0x6))) - 0x1))) - (0x2 * ((((w + 0x3c) - (w & 0x3c)) + 0x16) - ((w | 0x3c) & 0x16)))) - (0x2 * ~((x & 0x6))))", &["(((x & y) ^ 0x59) + ((z | y) & 0xb5))"], 10),
            ("((((((((0x5 * (~(y) | 0xcc)) + (0x3 * ~((y & w)))) + (-((y ^ 0xf)) - 0x1)) + (0x5 * ((v & u) | 0xcc))) - (0x5 * ((((v + u) - (v | u)) + 0xcc) - ((v & u) & 0xcc)))) + (0x3 * (((v & u) | 0x1b) - ((v & u) & 0x1b)))) - (0x5 * (((-(y) - 0x1) + 0xcc) - (~(y) & 0xcc)))) - (0x3 * ((v & u) ^ 0x1b)))", &["((3 * ~(y & w)) + (y ^ -0x10))"], 10),
            ("(((((-(((z ^ x) ^ (x & -((x & -((x & y))))))) - (((y | z) | (y & -((y & -((y & x)))))) - ((y | z) & -(((y | z) & -(((y | z) & (y & -((y & -((y & x)))))))))))) + ((y ^ y) | (y | y))) + (0x7 * ((((z + z) - (z | z)) + ((z | z) - (z & z))) - ((z & z) | (z ^ z))))) - ((((y | y) - (y & y)) + ((y + y) - (y & y))) - ((y ^ y) & (y | y)))) - (0x7 * ((z & z) & (z ^ z))))", &["(-(x ^ (z | y)) - z)", "(-z - (x ^ (z | y)))"], 10),
        ],
    );
}

#[test]
fn null_polynomials() {
    check(
        "u8",
        &[
            ("3*x + 0x80*x*x + 0x80*x", &["(3 * x)"], 10),
            ("y + 0x20*x*x*x*x + 0x40*x*x*x + 0x60*x*x + 0x40*x", &["y"], 10),
        ],
    );
    check(
        "i64",
        &[("x*y + 0x8000000000000000*x*x*y - 0x8000000000000000*x*y", &["(x * y)"], 10)],
    );
}

/// Variable left shifts whose low bits are fixed by the low bits of the operands:
/// `(y << (y & 63)) & 1` is 0, and `(1 << (x & 63)) & 1` is 1 only where `x` is even.
#[test]
fn variable_shift_low_bits() {
    check(
        "i64",
        &[
            ("-((x|~x)*(x+((y*y&2)+(y<<(y&63&63))&1))) + -y", &["(x - y)"], 10),
            ("(x - ((2 << (y & 0x3f)) & 1)) + y", &["(x + y)"], 10),
            ("x & (y | ((1 << (x & 0x3f)) & 1))", &["(x & y)"], 10),
            ("((~(~(x | y) << (0x3d & (x | y))) | -2) & x) | y", &["(x | y)"], 10),
            ("(x - y) << ((1 << (0x3f - (y & 1))) & 0x3f)", &["(x - y)"], 10),
            ("(x * y) + (-0x8000000000000000 * ((-y * x) << ((-y * x) & 0x3f)))", &["(x * y)"], 10),
        ],
    );
    check("u8", &[("x & (y | ((1 << (x & 7)) & 1))", &["(x & y)"], 10), ("x + ((y << (y & 15)) & 1)", &["x"], 10)]);
    check("i8", &[("x + ((y << (y & 7)) & 1)", &["x"], 10)]);
}

/// A leaf group of a wide region rebuilt on its own: `s - (z & (y | s)) + z` is
/// `(~y & z) | s`, beside a group that also uses `z`.
#[test]
fn leaf_group_rebuilt_alone() {
    check(
        "u32",
        &[(
            "(((s - (z & (y | s))) - ~w) + ((((u ^ x) ^ z) - ((x | v) + (0xfffffff9 * ((v ^ (x | t)) + ((v ^ t) & 0x3f))))) + z))",
            &["(((((7 * ((v ^ (x | t)) + ((v ^ t) & 0x3f))) - ~w) - (x | v)) + ((~y & z) | s)) + ((u ^ x) ^ z))", "((((((7 * (v ^ (x | t))) - ~w) - (x | v)) + (7 * ((v ^ t) & 0x3f))) + ((~y & z) | s)) + ((u ^ x) ^ z))"],
            10,
        )],
    );
}

/// Ensia's affine wrapper `A·(L ^ (y | M)) + D` with `L` linear in `y`: relating `L` with
/// `μ = A` cancels it, although `y` has another coefficient on the top bit.
#[test]
fn affine_wrapper_relate() {
    check("u32", &[("((0x7c58f033 * (((0xb5947505 * y) + 0x6274dc29) ^ (y | 0x7fffffff))) + 0xb21f3c5f)", &["((0x7fffffff & y) + 1)"], 10)]);
}

/// A bitwise function of 6 leaves split as `g(A) | h(B)`.
#[test]
fn six_leaf_decomposition() {
    check(
        "i64",
        &[("((y * s) | ((u & w) | (2 * v))) ^ ((v + t) & (w ^ (s | (u & w))))", &["((u & w) | (((y * s) | (2 * v)) ^ ((v + t) & (w ^ s))))"], 10)],
    );
}

/// Two moves between leaf groups, the first of which alone makes the sum larger:
/// `3·(t & ~x) + x` becomes `3·(t | x)` once `2·x` comes from the group of `x ^ y`.
#[test]
fn leaf_moves_two_steps() {
    check(
        "u64",
        &[(
            "((((((3 * (t & ~x)) + x) + (-2 * (y + (y & s)))) + (3 * ((v & -0xf0f0f0f0f0f0f10) | x))) + ((4 * (x & y)) + (-0xb * ((~x | u) ^ y)))) + (-2 * ((r ^ z) ^ x)))",
            &[
                "((((3 * (((v & -0xf0f0f0f0f0f0f10) | x) + (t | x))) - (2 * (((x + ((z ^ x) ^ r)) + y) + (y & s)))) - (0xb * ((~x | u) ^ y))) + (4 * (x & y)))", "(((((3 * ((v & -0xf0f0f0f0f0f0f10) | x)) - (2 * (y & s))) - (2 * ((r ^ z) ^ x))) + (3 * (t | x))) + ((-0xb * ((~x | u) ^ y)) - (2 * (x ^ y))))",
                "(((((3 * (t | x)) - (2 * (y & s))) - (2 * ((z ^ x) ^ r))) + (3 * ((-0xf0f0f0f0f0f0f10 & v) | x))) + ((-0xb * ((~x | u) ^ y)) - (2 * (x ^ y))))",
            ],
            10,
        )],
    );
}

/// A second move into a group the first one grew: `-3·~y` from the group of `t ^ y`, then
/// `-3·v` from that of `v & (~z | u)`, rebuild the group of `v ^ (s & y)` as
/// `3·(v ^ y) + 7·((v ^ s) & y)`.
#[test]
fn leaf_moves_into_moved_group() {
    check(
        "u64",
        &[(
            "((((((((v & (~z | u)) + ~y) * -3) + (t ^ y)) + (7 * (v ^ (s & y)))) - (~y & v)) + (-3 * (~w | (t | x)))) + w)",
            &["((((3 * (((v ^ y) - (~w | (t | x))) - (~(v & z) | u))) + w) + (t ^ y)) + (7 * ((v ^ s) & y)))", "((((w - (3 * (~w | (t | x)))) + (t ^ y)) + (-3 * (~(v & z) | u))) + ((3 * (v ^ y)) + (7 * ((v ^ s) & y))))"],
            10,
        )],
    );
}

/// Loki: proved by cases of the shift amount, whose low bits of `c` or `y` also fix the
/// other uses of it.
#[test]
fn shift_amount_cases() {
    check("i64", &[("((x - 2*y - 3) | (~c & (((x - 2*y - 3) << (c & 63)) & 1))) + y + 3", &["(x - y)"], 10)]);
    check(
        "u32",
        &[("x * ((((x + 1) << (~y & 31)) & 2) - (((x + 1) << (~y & 31)) ^ ((x + 1) << (~(((x + 1) << (~y & 31)) | y) & 31))) | y)", &["(x * y)"], 10)],
    );
}


/// A split-off constant of a set that is a leaf keeps the leaf whole: `L + 0` with
/// `L = x >> 32` is not cut to `x >> 32` outside the leaf.
#[test]
fn semi_split_keeps_leaf_constant() {
    check(
        "i64",
        &[
            ("((((x >> 32) + 0) ^ 5) + ((((x >> 32) + 0) & 5) * 2)) - x", &["((5 - x) + (x >> 0x20))"], 10),
            ("(((((((7 * (x >> 32)) << 32) + (7 * (x & 4294967295))) + 0) ^ 5) + ((((((7 * (x >> 32)) << 32) + (7 * (x & 4294967295))) + 0) & 5) * 2)) - x)", &["((6 * x) + 5)"], 10),
        ],
    );
}

/// Ensia noise: polynomials whose low bits are fixed, under a small mask.
#[test]
fn product_low_bits() {
    check(
        "i64",
        &[
            ("(x - y) + (-0x1f88d2cab8273600 * (1 & ((x * (x + 3)) + 2)))", &["(x - y)"], 10),
            ("((z - 1) | (2 * x)) - x - 0x2ba6503ce8e84137 * (1 & ((x * ((-0x65c105c26804167 * x) + -0x4c6db1b60f12763)) + -0x5479651dde4c58b4))", &["(((z + -1) | (2 * x)) - x)"], 10),
            ("(~(6 * y) + (0x4d6ff48b4444e1b5 * ((y * ((0x56538a7d55b73729 * y) + -0x3cc405088511d04d)) & 1))) * (y + (2 * x))", &["((y + (2 * x)) * ~(6 * y))"], 10),
            ("y + (((x*(x+1))*((x+2)*(x+3))) & 7)", &["y"], 10),
        ],
    );
}

/// A low-bits candidate `P` that also occurs inside another candidate `P | 0`: replacing
/// `P` by a value is proved only for the occurrences outside `P | 0`.
#[test]
fn product_low_bits_nested_candidate() {
    check(
        "i64",
        &[(
            "(((~x & 1) * (x & 4)) - ((~x | -5) * (x & 1))) + ((x & ((((~x & 1) * (x & 4)) - ((~x | -5) * (x & 1))) | 0)) ^ (((~x & 1) * (x & 4)) - ((~x | -5) * (x & 1))))",
            &["(x & 5)"],
            10,
        )],
    );
}

/// `c·(a >> s)` with `2^s | c` is `(c >> s)·(a & -2^s)`, which joins the semi-linear rebuild.
#[test]
fn multiple_of_right_shift() {
    check(
        "i64",
        &[
            ("(5 * (x & 0xffffffff)) + (0x500000000 * (x >> 0x20))", &["(5 * x)"], 10),
            ("(3 * (y | -0xfffffffe)) + (-0x300000000 * ~((y | 2) >> 0x20))", &["(3 * (y | 2))"], 10),
        ],
    );
    check(
        "u32",
        &[
            ("(7 * ((z + x) & 0xffff)) + (0x70000 * ((z + x) >> 0x10))", &["(7 * (z + x))"], 10),
            ("((x & 0xffff) * ((3 * z) + 0xfffffffa)) + ((x >> 0x10) * ((0x30000 * z) + 0xfffa0000))", &["(x * ((3 * z) + 0xfffffffa))", "(((3 * z) + 0xfffffffa) * x)"], 10),
        ],
    );
}

/// Tigress EncodeData: bitwise operations of even operands are halved, so
/// `x - ((2*x) | ~(2*K)) - K - 1` becomes the semi-linear `x ^ K`.
#[test]
fn halved_bitwise_operands() {
    check(
        "i64",
        &[
            ("(x - ((2 * x) | -0x1bd5b7ddf)) + -0xdeadbef0", &["(x ^ 0xdeadbeef)"], 10),
            ("((y - x) - (((y - x) * 2) & 0x1fe)) + 0xff", &["((y - x) ^ 0xff)"], 10),
            ("(0xb * x) + (2 * y) - ((4 * y) & (0x16 * x))", &["((2 * y) ^ (0xb * x))"], 10),
        ],
    );
    check(
        "u32",
        &[
            ("(y - ((2 * y) & 0x2468)) + 0x1234", &["(y ^ 0x1234)"], 10),
            ("(z - ((2 * z) | 0xffffdb97)) + 0xffffedcb", &["(z ^ 0x1234)"], 10),
        ],
    );
}

/// An arithmetic or product leaf of a bitwise operation that depends on other leaves
/// is replaced by a placeholder `v`, adding `μ·(v - L)`, so the rest cancels.
#[test]
fn related_leaves_by_placeholder() {
    check(
        "i64",
        &[
            (
                "(((z ^ y) - ((z & 0x80000000) ^ (y * 5))) + (2 * (((y * z) - (z ^ y)) | ((z & 0x80000000) ^ (y * 5))))) - (y * z)",
                &["(((y * 5) ^ ((y * z) - (z ^ y))) ^ (z & 0x80000000))"],
                10,
            ),
            ("0xb * ((~(y & x) | (x + 0xff)) - ((y & x) | (-0x100 - x)))", &["(((x & ~y) + 0xff) * 0xb)", "((0xb * (~y & x)) + 0xaf5)"], 10),
            ("(y * (z + -1)) + (2 * (x - ((x - y) & (y * z))))", &["(x + ((x - y) ^ (y * z)))"], 10),
            (
                "(0x80000002 - ((x * x) + (~y * y))) + (2 * (((x * x) + ~(y * y)) | (-0x80000001 - y)))",
                &["(((y * y) - (x * x)) ^ (y + 0x80000000))", "(((y + x) * (y - x)) ^ (y + 0x80000000))"],
                10,
            ),
        ],
    );
    check("u32", &[("((2 * ((y | x) & ~((0xfffffffe * ~x) * y))) - (~y & x)) - (~(2 * x) * y)", &["((y | x) ^ ((0xfffffffe * ~x) * y))"], 10)]);
}

/// A region with more than six leaves is evaluated on {0,1}^n, and the leaves its
/// values do not depend on are set to 0, which removes opaque predicates.
#[test]
fn unused_leaves_of_wide_regions() {
    check(
        "i64",
        &[
            (
                "(((x + -0x4652fe91e34cde29) - y) + (-0x4652fe91e34cde29 * ((((y | ~aux1) | ((aux0 ^ x) & (aux0 ^ (~aux2 | aux3)))) | aux4) | (((aux1 ^ x) | (aux4 ^ (aux1 & (~(aux4 & aux3) | aux0)))) ^ (y & (~aux4 ^ (x | ((aux0 ^ aux3) & aux1))))))))",
                &["(x - y)"],
                10,
            ),
        ],
    );
    check("u32", &[("(x * (y + (0xbd05a805 * (((aux2 & ((~y & aux1) ^ aux4)) & (aux0 & (aux1 & (x & (~(aux3 & aux4) & y))))) & (aux4 ^ aux1)))))", &["(x * y)", "(y * x)"], 10)]);
}

/// A product with a factor that is 0 or `2^k` by bit `k` of a variable is rebuilt by cases on that bit.
#[test]
fn split_on_selecting_bit() {
    check(
        "i64",
        &[
            ("x + ((1 & ~y) * (-y & -2)) + ((-y | 1) * (y & 1))", &["(x - y)"], 10),
            ("(((x | -x) - ((~x & 1) * ((x | -x) | 1))) - ~((~(x | -x) & -2) * (x & 1)))", &["0"], 10),
            ("(((((y | 2) ^ 1) * (y & 2)) + (~(y | -3) * ((y & -3) ^ 1))) - (y ^ 1)) | 1", &["(y | 1)", "(1 | y)"], 10),
            (
                "(((-0x7affce5604f8bf5f - (~(x + 0x7affce5604f8bf5f) & y)) + (((~y & -2) & (x + 0x7affce5604f8bf5f)) * (1 & (y | x)))) + (((~y & (x + 0x7affce5604f8bf5f)) | 1) * (1 & ~(y | x))))",
                &["(x - y)"],
                10,
            ),
        ],
    );
    check("u32", &[("x - ((1 | -y) * (y & 1)) - ((1 & ~y) * (-y & 0xfffffffe))", &["(x + y)", "(y + x)"], 10)]);
}

#[test]
fn split_on_bits_of_subterm() {
    check(
        "u32",
        &[
            (
                "((3 | ((z + x) + 5)) * (3 & ((z + x) + 5))) + (((0xfffffffa - (z + x)) & 3) * (((z + x) + 5) & 0xfffffffc))",
                &["((3 * (z + x)) + 0xf)", "(((z + x) + 5) * 3)", "(0xf + (3 * (z + x)))"],
                10,
            ),
            (
                "(2*x) | ((x + z) - ((2 | (x & z)) * (2 & (x & z))) - (((x & z) & 0xfffffffd) * ~((x & z) | 0xfffffffd)))",
                &["((2 * x) | (x ^ z))", "((x + x) | (x ^ z))"],
                10,
            ),
            (
                "(((((2 | ((x & y) & z)) * (((x & y) & z) & 2)) - ((((x & y) & z) & 0xfffffffd) * (0xfffffffd | ((x & y) & z)))) + (z ^ (x & y))) + (z & ~((x & y) & 0xfffffffd)))",
                &["((2 * z) + (x & y))", "((z + z) + (x & y))"],
                10,
            ),
        ],
    );
    check(
        "i64",
        &[(
            "(y - (z + ((2 | ((y - x) & (x - z))) * (2 & ((y - x) & (x - z)))))) - (~(((y - x) & (x - z)) | -3) * (((y - x) & (x - z)) & -3))",
            &["((y - x) ^ (x - z))"],
            10,
        )],
    );
}

/// A bitwise operation of an arithmetic term and a constant that only touches known bits is an addition.
#[test]
fn bitwise_constant_on_known_bits() {
    check(
        "i64",
        &[
            ("(-0x6a79d978bdb719 * (((0xe646d4c5d6e4ad7 * (y | 3)) + 0x1a662449b3e750f5) ^ 1)) + 0x48dc610d0214c207", &["((y | 3) + 1)", "(1 + (y | 3))"], 10),
            ("((4 * x) + 8) | 3", &["((4 * x) + 0xb)", "(0xb + (4 * x))"], 10),
        ],
    );
}

/// A degree-2 polynomial is factored into two linear ones, `(v + r)·(a·v + s)`.
#[test]
fn quadratic_factors() {
    check(
        "i64",
        &[
            ("x*x - y*y + 3*x + 3*y", &["((x + y) * ((x + 3) - y))", "((x + y) * (3 + (x - y)))"], 10),
            ("(x&y)*(x|y) + 3*(x&y) + 2*(x|y) + 6", &["(((x & y) + 2) * ((x | y) + 3))"], 10),
        ],
    );
    check("u8", &[("3*x*x + 7*x*y + 2*y*y + x + 2*y", &["((x + (2 * y)) * ((3 * x) - ~y))", "((x + (2 * y)) * (((3 * x) + y) + 1))", "(((0xfe * y) - x) * (~y + (0xfd * x)))"], 10)]);
}

/// Squares have double roots `b/2a`; both factors may also be negated (`(x + 1)·…` as `~x·…`).
#[test]
fn square_factors() {
    check(
        "u32",
        &[
            ("((y&x)*(0xfffffffc*(y|x))) + y*(y+2*x) + x*x", &["((y ^ x) * (y ^ x))"], 10),
            ("(w^y)*y + (w^y)*w + (w&y)*(w&y)", &["((w | y) * (w | y))"], 10),
            ("x*(0xfffffffe*(z^w) + x) + (z&w)*(0xfffffffc*(z|w)) + z*(z + 2*w) + w*w", &["((x - (z ^ w)) * (x - (z ^ w)))", "(((z ^ w) - x) * ((z ^ w) - x))"], 10),
            ("(x + 1)*(x + 0xfffffffe*z)", &["(~x * ((2 * z) - x))"], 10),
        ],
    );
    check("u64", &[("z*(z + ~y*2) + ~y*~y", &["((z + ~y) * (z + ~y))"], 10)]);
}

/// A bitwise region with constants over 4 to 6 leaves is split into `P op Q` over smaller leaf sets.
#[test]
fn bitwise_split_with_constants() {
    check(
        "i64",
        &[(
            "((((a | (b | e)) & -0x2ff8) - (((b & (~e & (c & d))) & 0x807) - ((e | ((a | b) ^ (b & (c & d)))) & 0x2360))) + 0xc97)",
            &["(e | ((a | (b | 0xc97)) ^ (c & (b & (d & 0x2b67)))))"],
            10,
        )],
    );
}

/// `~x ^ (c - y)` is `x ^ (y + ~c)`.
#[test]
fn not_with_constant_operand() {
    check("i64", &[("~((y+x)*(y-x)) ^ (-0x80000001 - y)", &["(((y + x) * (y - x)) ^ (y + 0x80000000))"], 10)]);
}

/// A linear MBA whose values are all multiples of `2^k` is also rebuilt as `-2^k·L`.
#[test]
fn negative_power_of_two_scale() {
    check("u8", &[("(4 * (x & y)) + (0xf8 * x)", &["(0xfc * ((~y & x) + x))"], 10)]);
}

/// The low-bits context proof enumerates up to 18 leaf bits: 3 leaves of 6 bits here.
#[test]
fn low_bits_context_of_three_leaves() {
    check("i64", &[("(y ^ x) | (2 & ((2 * c) << ((~y ^ x) & 63)))", &["(y ^ x)", "(x ^ y)"], 10)]);
}

/// Bit 1 of a square is 0, and carries are tracked through known bits of a sum.
#[test]
fn square_low_bits() {
    check("u64", &[("((((((x - y) * (x - y)) ^ 0x6d13500) + 2) & 0xfffffffffffffffd) ^ 0x6d13500)", &["((x - y) * (x - y))"], 10)]);
    check("i32", &[("(((x * x) ^ 0x10) + 2) & -3", &["((x * x) ^ 0x10)"], 10)]);
    check("u8", &[("((x + 3) * (x + 3)) & 0xfd", &["((x + 3) * (x + 3))"], 10)]);
}

/// A factor with `t` trailing zeros only sees the low `w - t` bits of the other factor.
#[test]
fn product_with_trailing_zeros() {
    check(
        "i64",
        &[
            (
                "((((x & z) + 0x57c3382e1a728dbc) & -0x100000000) * ((x & z) + 0x1a728dbc)) + ((((x & z) + 0x57c3382e1a728dbc) & 0xffffffff) * ((x & z) + 0x57c3382e1a728dbc)) + (0x50798fa3cb1ae488 * (x & z)) - 0x5650a79cb9e8a210",
                &["((x & z) * (x & z))"],
                10,
            ),
            ("(((y & x) & 7) * ((y & x) | 7)) + (((y & x) & -8) * (-0x5ffffffffffffff9 ^ ((y & x) & 7)))", &["((y & x) * 7)", "(7 * (y & x))"], 10),
        ],
    );
}

/// `2^k·(a ^ K) + c` with `0 < c < 2^k` is `(2^k·a) ^ (2^k·K + c)`, since the low `k` bits of `2^k·a` are 0.
#[test]
fn shifted_xor_plus_low_constant() {
    check("i64", &[("2*(x ^ 0x2aaa) + 1", &["((x * 2) ^ 0x5555)"], 10)]);
    check("u8", &[("(x ^ 0x2a)*2 + 1", &["((x * 2) ^ 0x55)"], 10)]);
    check("i32", &[("(x ^ 0x55)*8 + 7", &["((x * 8) ^ 0x2af)"], 10)]);
    check("u16", &[("(y ^ 0x1234)*0x10 + 0xf", &["((y * 0x10) ^ 0x234f)"], 10)]);
    check("u32", &[("(x ^ 5)*8 + 8", &["(0xfffffff8 * (x ^ 0xfffffffa))", "(((x ^ 5) * 8) + 8)"], 10)]);
}

/// `c·P1·Q1 + c·P2·Q2` with `P1 = Q1 + P2 + Q2` is `c·(Q1 + P2)·(Q1 + Q2)`: `a·b` split as `(a | b)·(a & b) + (a & ~b)·(~a & b)`, also with a constant `a`.
#[test]
fn split_product_recombined() {
    check("u64", &[("(((x ^ y) | (y & 0xf)) * ((~x & y) & 0xf)) + ((y ^ ((y & 0xf) | x)) * ((x & y) & 0xf))", &["((x ^ y) * (y & 0xf))"], 10)]);
    check("u32", &[("(((~y & x) | 0xff) * (~(x | 0xff) & y)) + (((x & y) & 0xffffff00) * (x | (y | 0xff)))", &["((x | 0xff) * (y & 0xffffff00))"], 10)]);
    check("u64", &[("((0xb & ((s | t) ^ v)) * (0xb | ((s | t) ^ v))) + ((((s | t) ^ v) & -0xc) * ((~v ^ (s | t)) & 0xb)) - y", &["((0xb * ((s | t) ^ v)) - y)"], 10)]);
}

/// Beside a factor with `k` trailing zeros, the constants of the other factor are cut to `w - k` bits.
#[test]
fn product_constants_cut_below_trailing_zeros() {
    check("u32", &[("(y & 0xff00) * ((x + z) * 0x10000001)", &["((y & 0xff00) * (x + z))"], 10)]);
    check("u64", &[("(y & 0xff00) * (0x3800000000000001 * (z ^ x))", &["((y & 0xff00) * (z ^ x))"], 10)]);
    check("u64", &[("(y & 0xf0) * ((x & -0x1235) + -0x4fffffffffffedcc)", &["((y & 0xf0) * (x | 0x1234))"], 10)]);
}

/// Cubes and products of three affine factors are factored back, also beside a linear rest.
#[test]
fn cubes_factored() {
    check("u64", &[("((((z * 3) - y) * (y * y)) + ((z * (z + (-3 * y))) * z))", &["(((z - y) * (z - y)) * (z - y))", "(((y - z) * (y - z)) * (z - y))"], 10)]);
    check("u32", &[("~((3 + ((w + 3) * w)) * w)", &["((~w * ~w) * ~w)"], 10)]);
    check("u32", &[("((y * (((z + y) * (3 * z)) + (y * y))) + ((z * (z * z)) + (~y | z)))", &["((((y + z) * (y + z)) * (y + z)) + (~y | z))"], 10)]);
    check("u64", &[("((x * (x + (2 * y))) + ((y * y) + ~(y | w)))", &["(((x + y) * (x + y)) + ~(y | w))"], 10)]);
}

/// `2^k·(a ^ K) + c` is `(2^k·a) ^ (2^k·K + c)` for small `K` too, by the pre-pass.
#[test]
fn shifted_xor_small_constant() {
    check("u64", &[("2*(x ^ 3) + 1", &["((x * 2) ^ 7)"], 10)]);
    check("u32", &[("4*(x ^ 5) + 3", &["((x * 4) ^ 0x17)"], 10)]);
    check("i64", &[("8*(y ^ 0xa) + 7", &["((y * 8) ^ 0x57)"], 10)]);
}

/// A linear region over more than `MAX_LEAVES` leaves is rebuilt in groups of terms over the same leaves (Tigress, Ensia).
#[test]
fn wide_region_rebuilt_in_groups() {
    check("u32", &[("(13*(r & x ^ z) - 3*(s & (q ^ 4294967295) | u) - 11*(r ^ 4294967295) - 11*(t | y) + 13*(x | r | s) - (13*r ^ 4294967295) ^ 1) + (((13*(r & x ^ z) - 3*(s & (q ^ 4294967295) | u) - 11*(r ^ 4294967295) - 11*(t | y) + 13*(x | r | s) - (13*r ^ 4294967295) ^ 4294967295) & 1) + ((13*(r & x ^ z) - 3*(s & (q ^ 4294967295) | u) - 11*(r ^ 4294967295) - 11*(t | y) + 13*(x | r | s) - (13*r ^ 4294967295) ^ 4294967295) & 1) ^ 4294967295) + 1", &["(((((((x | r) | s) + ((r & x) ^ z)) * 0xd) + ((0xfffffff5 * (t | y)) + (0x18 * r))) + (0xfffffffd * ((~q & s) | u))) + 0xb)"], 10)]);
    check("u64", &[("(((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 1) + ((((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 18446744073709551615) & 1) + (((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 18446744073709551615) & 1) ^ 18446744073709551615) | 1) + (((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 1) + ((((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 18446744073709551615) & 1) + (((y & (x ^ 18446744073709551615)) + 5*(y ^ x) + (u | s | x) + (r ^ q ^ s) + 5*(y & v ^ w) + (2*t ^ 18446744073709551615) - 18446744073709551614 ^ 18446744073709551615) & 1) ^ 18446744073709551615) & 1)", &["(((((5 * ((y ^ x) + ((y & v) ^ w))) - (2 * t)) + (~x & y)) + ((u | s) | x)) + ((r ^ q) ^ s))", "((((((-2 * t) + (~x & y)) + (5 * (y ^ x))) + ((u | s) | x)) + ((r ^ q) ^ s)) + (5 * ((y & v) ^ w)))"], 10)]);
    check("u32", &[("2449234233*((1899545865*(2966763221*((4244918909*((0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) ^ 2775353207) - (1793198561*((2551708193*t + 1510895837 ^ 1814418326 ^ 1814418326) - 1510895837) ^ x ^ 2775353207) + (0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) & 2775353207)*2 - ((1793198561*((2551708193*t + 1510895837 ^ 1814418326 ^ 1814418326) - 1510895837) ^ x) & 2775353207)*2 + 4036517887*((0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z))*(0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) + 1) & 1 ^ (1917008638 ^ 1917008638) | (2551708193*t*(2551708193*t) + 2551708193*t & 1 | 1917008638 ^ 1917008638)) + (v + u + 2325249841 - (v & u) - 2325249841 - 1679021120*((v*v*v - v)*(1917008638 ^ 1917008638) | ((0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) & 2775353207)*2*((0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) & 2775353207)*2) + (0 - (y + s - (y & s)*2 + 2714978978*((y ^ s)*((y ^ s) + 1) & 1 | 1917008638 ^ 1917008638 | (u*(u - 1) & 1 | 1917008638 ^ 1917008638)) + 967722390*(s*s - s & 1 | 1917008638 ^ 1917008638 | ((y + s - (y & s)*2)*(y + s - (y & s)*2) + (y + s - (y & s)*2) & 1 | 1917008638 ^ 1917008638)) & z) & 2775353207)*2 & 1 | 1917008638 ^ 1917008638)) | z)) + 1385551065 ^ 716279712 ^ 716279712) - 1385551065) - (((s ^ 4294967295) & (w ^ 4294967295) ^ 4294967295) - 1737104981*((s*s + w*w + 257)*(1917008638 ^ 1917008638) | ((v & u)*(v & u) + (v & u) & 1 | 1917008638 ^ 1917008638)))) + 4047332889 ^ 2643333275 ^ 2643333275) - 4047332889) + 13*(s | y)", &["(((((v | u) | z) - (((y ^ s) & z) + (t ^ x))) - (s | w)) + (0xd * (s | y)))", "(((((z | (v | u)) ^ ((y ^ s) & z)) - (t ^ x)) - (s | w)) + (0xd * (s | y)))"], 10)]);
}

/// A wide linear region is rebuilt from its conjunction-basis expansion with one bitwise
/// term per maximal leaf set; overlapping sets split their shared part as the smallest
/// terms need, and one set may be a read-once function of more than 6 leaves.
#[test]
fn wide_region_rebuilt_by_blocks() {
    check("u64", &[("((((((((((((-((0x2 * ((((h ^ g) & a) | f) - (((h ^ g) & a) & f)))) - (0x3 * (((-(f) - 0x1) + (-(b) - 0x1)) - (~(f) | ~(b))))) + (0x2 * ((((b | h) - (b & h)) + ((g + d) - (g | d))) - ((b ^ h) | (g & d))))) - (0x7 * (~(f) ^ (a | a)))) - (0x2 * ((((c + c) - (c & c)) + ((i | i) - (i & i))) - ((c | c) | (i ^ i))))) - (0x7 * ((d | h) & (d & d)))) + (0x2 * (~(i) ^ (i | c)))) - (0x2 * ((~(i) | (i | c)) - (~(i) & (i | c))))) + (0x7 * ((~(f) | (a | a)) - (~(f) & (a | a))))) + (0x7 * ((((d + h) - (d & h)) + ((d + d) - (d | d))) - ((d | h) | (d & d))))) + (0x3 * (~(f) & ~(b)))) - (0x2 * ((((g + j) - (g & j)) + ((a | h) - (a & h))) - ((g | j) | (a ^ h))))) + (0x2 * ((c | c) & (i ^ i))))", &["((((g & ((h ^ b) & d)) - (f ^ (a & (h ^ g)))) - ((h ^ a) & (g | j))) * 2)"], 10)]);
    check("u64", &[("(((((((((((((-((0x3 * (((i & i) | ~(i)) - ((i & i) & ~(i))))) + (0x2 * ((((i | c) - (i & c)) + e) - ((i ^ c) | e)))) + (((g & e) | a) - ((g & e) & a))) + (0x2 * ((a + (i ^ e)) - (a & (i ^ e))))) + (0x2 * (((h ^ h) | (i & h)) - ((h ^ h) & (i & h))))) - (0x2 * ((e | e) & (g | g)))) + (0x2 * (((-(f) - 0x1) + ((~(a) | i) - (~(a) & i))) - (~(f) & (~(a) ^ i))))) - (0x5 * ((((c + e) - (c & e)) + ((e + e) - (e & e))) - ((c | e) & (e | e))))) + (0x3 * ((i & i) ^ ~(i)))) - (0x2 * ((h ^ h) ^ (i & h)))) - (0x3 * (((c | e) | (e & e)) - ((c | e) & (e & e))))) + (0x3 * ((c | e) ^ (e & e)))) + (0x2 * ((((e + e) - (e & e)) + ((g + g) - (g & g))) - ((e | e) | (g | g))))) + (0x5 * ((c | e) | (e | e))))", &["(((~((i ^ a) & f) + (((i ^ c) & e) + ((i ^ e) | a))) * 2) + ((e & g) ^ a))", "((2 * ~(((i ^ a) & f) - (((i ^ c) & e) + ((i ^ e) | a)))) + ((e & g) ^ a))"], 10)]);
    check("u8", &[("(((((((-(((g ^ g) & (g | g))) + ((((g | g) - (g & g)) + ((g + g) - (g & g))) - ((g ^ g) | (g | g)))) + (0x3 * (((-(a) - 0x1) + ((a + f) - (a | f))) - (~(a) | (a & f))))) + ((((((~((f ^ c)) + ((d | a) - (d & a))) - (~((f ^ c)) & (d ^ a))) + b) - ((~((f ^ c)) | (d ^ a)) & b)) + (((-(g) - 0x1) + e) - (~(g) & e))) - (((~((f ^ c)) | (d ^ a)) | b) | (~(g) | e)))) - ((d | b) | (b | d))) - g) - (0x3 * (~(a) & (a & f)))) + ((((d + b) - (d & b)) + ((b + d) - (b & d))) - ((d | b) & (b | d))))", &["(((~g | e) & (b | ((~c ^ f) | (a ^ d)))) - g)"], 10)]);
}

/// Two blocks of 5 leaves sharing 4: the rebuild without `wide_blocks` keeps `(j | e)` and
/// `i` in several terms, where the abstracted rebuild joins them.
#[test]
fn wide_region_rebuilt_without_blocks() {
    check("u64", &[("(((((((((((((((-((((-(((h + a) - (h & a))) - 0x1) + j) - (~((h | a)) & j))) + (0x3 * (((k ^ d) | ((b | i) | c)) - ((k ^ d) & ((b | i) | c))))) + ((i ^ (l | e)) | (j ^ k))) + (((((j | e) | i) - ((j | e) & i)) + ((d | k) - (d & k))) - (((j | e) ^ i) & (d ^ k)))) - (0x3 * (((((-(f) - 0x1) + g) - (~(f) | g)) + e) - ((~(f) & g) | e)))) + ((c + ((k | h) - (k & h))) - (c & (k ^ h)))) + (i ^ (f ^ l))) + (0x7 * ((((k + b) - (k & b)) + l) - ((k | b) | l)))) + (0x3 * (((-(((b | (~(f) & j)) - (b & (~(f) & j)))) - 0x1) + ((a + h) - (a & h))) - (~((b ^ (~(f) & j))) | (a | h))))) - (0x3 * (((-(c) - 0x1) + (((-(j) - 0x1) + f) - (~(j) | f))) - (~(c) | (~(j) & f))))) + (0x3 * (~(c) & (~(j) & f)))) + (0x3 * ((~(f) & g) & e))) - (c | (k ^ h))) - (0x7 * ((k | b) & l))) + (~((h | a)) | j)) - ((i | (f ^ l)) - (i & (f ^ l))))", &["(((3 * ((k ^ (d ^ (b | (i | c)))) + (((~j | f) ^ b) & (a | h)))) + (((j | e) ^ i) | (d ^ k))) + ((i ^ (l | e)) | (j ^ k)))"], 10)]);
}

/// The final result has the terms of one coefficient summed under it, and a constant `c`
/// absorbed into a term `c·a` as `-c·~a`, where the rules leave them apart.
#[test]
fn terms_of_one_coefficient_summed() {
    check("u32", &[("(~(v & t) | u) - 2*(u ^ x) - 3*(z ^ w) - (z | y) + ((~w & s) ^ y) - 2*s", &["(((((~(v & t) | u) - (2 * ((u ^ x) + s))) - (3 * (z ^ w))) - (z | y)) + ((~w & s) ^ y))"], 10)]);
    check("u64", &[("13*(z | w) + 13*x - 13*r - 13 + ((~t ^ y) | u) + ((x | t) & s) - 11*((r & x) ^ z)", &["((((0xd * (((z | w) + x) + ~r)) + ((~t ^ y) | u)) + ((x | t) & s)) - (0xb * ((r & x) ^ z)))"], 10)]);
}

/// Under a bitwise operation, `(a & M) + K` with `M & K = 0` is `(a & M) | K`.
#[test]
fn masked_add_under_bitwise() {
    check("u32", &[("(((x & 0x80000000) + 0x7fffffff) ^ z) + (y | t)", &["(((x | 0x7fffffff) ^ z) + (y | t))"], 10)]);
}

/// The rebuild without leaf clusters is unioned too: clusters can leave the rules a worse start (`11*(a & -6) + 0x37` for `11*(a | 5)`).
#[test]
fn unclustered_rebuild_kept() {
    check("u32", &[("1607393583*(4014867919*(0 + 1*(11*(489561285*(3953328653*(0 + 4294967294*(360995877*(757882797*(0 + 1*(133239947*(380089123*(0 + 1*(u ^ w)) + 2203993843) + 3733028367) + 4294967295*z) + 2381435286) + 895667538 & 4294967290) + 5 + 1*(360995877*(757882797*(0 + 1*(133239947*(380089123*(0 + 1*(u ^ w)) + 2203993843) + 3733028367) + 4294967295*z) + 2381435286) + 895667538 | 5) + 1*(360995877*(757882797*(0 + 1*(133239947*(380089123*(0 + 1*(u ^ w)) + 2203993843) + 3733028367) + 4294967295*z) + 2381435286) + 895667538 | 4294967290) + 4294967294*(360995877*(757882797*(0 + 1*(133239947*(380089123*(0 + 1*(u ^ w)) + 2203993843) + 3733028367) + 4294967295*z) + 2381435286) + 895667538 ^ 4294967295 | 5) + 1*(360995877*(757882797*(0 + 1*(133239947*(380089123*(0 + 1*(u ^ w)) + 2203993843) + 3733028367) + 4294967295*z) + 2381435286) + 895667538 & 5 ^ 4294967295)) + 3260401778) + 596920390)) + 4294967295*(3542032079*(2654414895*(0 + 1*(2221690517*(254741693*(0 + 1*(3537862899*(3114244155*(0 + 1*(y & u)) + 3628076277) + 1900950385) + 1*(4282639659*(3538792835*(0 + 1*(t & z)) + 361157139) + 3765876687)) + 2076426243) + 3310113857) + 4294967295*(1494561369*(704050665*(0 + 1*(496845885*(2606396181*(0 + 1*(z & (x ^ 4294967295)) + 1*z + 4294967295*(z | x)) + 2650300579) + 2804854057 & 2412070739*(2533397723*(0 + 1*(t & 4294967040) + 1*t + 1*((t ^ 4294967295) & 255) + 255 + 4294967295*(t ^ 255)) + 2701169845) + 424187473)) + 542178393) + 1312940815) + 4294967295*(2221690517*(254741693*(0 + 1*(3537862899*(3114244155*(0 + 1*(y & u)) + 3628076277) + 1900950385) + 1*(4282639659*(3538792835*(0 + 1*(t & z)) + 361157139) + 3765876687)) + 2076426243) + 3310113857 | 1494561369*(704050665*(0 + 1*(496845885*(2606396181*(0 + 1*(z & (x ^ 4294967295)) + 1*z + 4294967295*(z | x)) + 2650300579) + 2804854057 & 2412070739*(2533397723*(0 + 1*(t & 4294967040) + 1*t + 1*((t ^ 4294967295) & 255) + 255 + 4294967295*(t ^ 255)) + 2701169845) + 424187473)) + 542178393) + 1312940815) + 4294967295*((2221690517*(254741693*(0 + 1*(3537862899*(3114244155*(0 + 1*(y & u)) + 3628076277) + 1900950385) + 1*(4282639659*(3538792835*(0 + 1*(t & z)) + 361157139) + 3765876687)) + 2076426243) + 3310113857 | 1494561369*(704050665*(0 + 1*(496845885*(2606396181*(0 + 1*(z & (x ^ 4294967295)) + 1*z + 4294967295*(z | x)) + 2650300579) + 2804854057 & 2412070739*(2533397723*(0 + 1*(t & 4294967040) + 1*t + 1*((t ^ 4294967295) & 255) + 255 + 4294967295*(t ^ 255)) + 2701169845) + 424187473)) + 542178393) + 1312940815) ^ 4294967295) + 4294967295) + 1294413542) + 3321372678)) + 3153282652) + 3950459164", &["((((0xb * (((u ^ w) - z) | 5)) - (y & u)) - (t & z)) + ((z - x) & (t + 0xff)))"], 10)]);
    check("u32", &[("(((((2382531045 * (s & 21845)) | r) + ((0 + (1 * (s & 21845))) + 338261024)) + (((0 + (1 * (x & t))) + (1 * t)) + (2 * ((x | t) ^ 4294967295)))) + ((1 * (r | (y ^ 4294967295))) | u))", &["(((((((0x8e0289e5 * (s & 0x5555)) | r) + (s & 0x5555)) + (~x | t)) - (x ^ t)) + 0x1429741f) + ((r | ~y) | u))"], 10)]);
}

/// Bits known only by evaluating a product's low bits: `(x*w) & (x + w)` is even, so
/// `& -2` keeps it and a multiplier `0x80000001` acts as 1; `-(a ^ K)` is `a ^ -K` for `a`
/// with trailing zeros below the lowest set bit of `K`.
#[test]
fn low_bits_by_evaluation() {
    check(
        "u64",
        &[
            ("-(-((x * w) & (x + w)) & -2)", &["((x * w) & (x + w))"], 10),
            ("((((y - z) * ((x & z) * ~z)) + 1) ^ 1)", &["((y - z) * ((x & z) * ~z))"], 10),
        ],
    );
    check(
        "u32",
        &[
            ("(0x7fffffff * ((x * y) & (x + y))) + (2 * ((x * y) & (x + y)))", &["((x * y) & (x + y))"], 10),
            ("-((~x * ((0xfffffffe * z) - x)) & 0xfffffffe)", &["(~x * (x + (2 * z)))"], 10),
            ("-((y * 0x10000) ^ 0xcabd4815) ^ ((z & x) ^ 0x3542b7eb)", &["((y * 0x10000) ^ (z & x))"], 10),
            (
                "((((x | z) & 0xff) * (y ^ 0xdeadbeef)) + (z ^ x)) + (0xfffffffe * ((z ^ x) & ((0x80000001 * ((x | z) & 0xff)) * (y ^ 0xdeadbeef))))",
                &["((z ^ x) ^ (((x | z) & 0xff) * (y ^ 0xdeadbeef)))"],
                10,
            ),
            ("(((x | 3) * ((y | 3) + 0x7ffffffd)) + 0x80000000)", &["((y & 0xfffffffc) * (x | 3))"], 10),
        ],
    );
}

/// A product with a linear rest is also tried with its factors shifted by ±1 (`(z + 1)·(z + 1)`
/// is `~z·~z`), and a cubic without a cube term is divided by a factor of a coefficient.
#[test]
fn shifted_and_coefficient_factors() {
    check(
        "u32",
        &[
            ("(z * (z + 3)) - (~x | z)", &["((~z * ~z) + (z | x))"], 10),
            ("(((y * (z + 1)) + z) * (z + x)) + (z & x)", &["(((z + x) * (~y * ~z)) - (z | x))"], 10),
        ],
    );
    check(
        "u64",
        &[
            ("((y * (~w | z)) + (w & z)) + (-2 * (~y & w))", &["((~y * (~z & w)) - (y ^ w))"], 10),
            ("(((~z & w) + 2) * (~z & w)) - (~y & x)", &["(((~w | z) * (~w | z)) + (~x | y))"], 10),
            ("(z + (x ^ y)) * ((x - z) * ((-2 * z) + (0x7fffffffffffffff * y)))", &["(((z - x) * (z + (x ^ y))) * ((2 * z) + y))"], 10),
        ],
    );
}

/// Leaves whose coefficients are within 1 of a large `c` are rebuilt as `c·(x + y) + rest`.
#[test]
fn common_multiple_of_leaves() {
    check(
        "u32",
        &[
            ("(8 * y) + ((0xfffffffe * (z & x)) + (9 * z))", &["((8 * (y + z)) + ((z ^ x) - x))"], 10),
            ("((0x1fff * (y ^ x)) + (0x4000 * (y & x))) + ~z", &["((0x2000 * (y + x)) + ((y ^ ~x) - z))"], 10),
        ],
    );
}

/// Products selecting bits by constant masks cancel when bitwise terms are expanded per mask.
#[test]
fn masked_selection_products() {
    check(
        "u32",
        &[("(((z & x) & 1) * (((1 & z) | x) | 0x1234)) + (((~x & z) & 1) * (0x1234 | (x & ~(z & 0x1235))))", &["((1 & z) * (x | 0x1234))"], 10)],
    );
    check(
        "u64",
        &[(
            "((x | (y | 0x80000000)) * ((0x80000000 & x) | y)) + (((x & ~y) & -0x80000001) * ~(x | (y | -0x80000001)))",
            &["((y | 0x80000000) * (x | y))"],
            10,
        )],
    );
    check("u64", &[("(((x & 0xff00) ^ (x | z)) - ((~z | -4) * (x & 0xff00)))", &["(((z & 3) * (x & 0xff00)) + (x | z))"], 10)]);
}

/// Arithmetic leaves of a wide region equal up to complement cancel, and the region is rebuilt whole.
#[test]
fn complement_leaves_of_wide_region() {
    check(
        "u32",
        &[(
            "(((0xd * s) - ((u ^ z) ^ y)) + ((0xfffffffe * ((3 * (t | x)) & (((3 * ~((t & y) ^ u)) + (0xfffffffe * (~(z & w) | y))) + ((s & t) ^ v)))) + ((3 * (t | x)) ^ (((3 * ((t & y) ^ u)) + (0xfffffffe * (~y & (z & w)))) - ((s & t) ^ v)))))",
            &["(((0xd * s) - ((s & t) ^ v)) + ((((((t & y) ^ u) - (t | x)) * 3) - ((u ^ z) ^ y)) + (0xfffffffe * (~y & (z & w)))))", "(((((3 * (((t & y) ^ u) - (t | x))) + (0xd * s)) - ((z ^ y) ^ u)) - ((t & s) ^ v)) - (2 * (~y & (z & w))))", "(((((0xd * s) - ((u ^ z) ^ y)) - ((s & t) ^ v)) + ((((t & y) ^ u) - (t | x)) * 3)) + (0xfffffffe * (~y & (z & w))))"],
            10,
        )],
    );
}

/// Overlapping terms with a repeated coefficient: `-(y ^ z) - (x & (y ^ z))`.
#[test]
fn overlapping_terms_with_equal_coefficients() {
    check(
        "i64",
        &[("-(y ^ z) - (x & ~y & z) - (x & y & ~z) + (a | b) + 2", &["(((a | b) - ((y ^ z) + ((y ^ z) & x))) + 2)"], 10)],
    );
}

/// A wide region whose value is a bitwise function of its leaves has single leaves peeled off.
#[test]
fn leaves_peeled_off_wide_bitwise_region() {
    check("u64", &[("1*(x4) + 1*(x6) + 1*(x7) + 1*(x0 & x2) + 1*((x0 & x3) & 0x55) + 1*(x1 & x2) + 1*((x1 & x3) & 0x55) - 1*(x4 & x6) - 1*(x4 & x7) - 1*(x6 & x7) - 2*(x0 & x1 & x2) - 2*((x0 & x1 & x3) & 0x55) - 1*((x0 & x2 & x3) & 0x55) - 2*(x0 & x2 & x4) - 1*(x0 & x2 & x6) - 1*(x0 & x2 & x7) - 2*((x0 & x3 & x4) & 0x55) - 1*((x0 & x3 & x6) & 0x55) - 1*((x0 & x3 & x7) & 0x55) - 1*((x1 & x2 & x3) & 0x55) - 2*(x1 & x2 & x4) - 1*(x1 & x2 & x6) - 1*(x1 & x2 & x7) - 2*((x1 & x3 & x4) & 0x55) - 1*((x1 & x3 & x6) & 0x55) - 1*((x1 & x3 & x7) & 0x55) + 1*(x4 & x6 & x7) + 2*((x0 & x1 & x2 & x3) & 0x55) + 4*(x0 & x1 & x2 & x4) + 2*(x0 & x1 & x2 & x6) + 2*(x0 & x1 & x2 & x7) + 4*((x0 & x1 & x3 & x4) & 0x55) + 2*((x0 & x1 & x3 & x6) & 0x55) + 2*((x0 & x1 & x3 & x7) & 0x55) + 2*((x0 & x2 & x3 & x4) & 0x55) + 1*((x0 & x2 & x3 & x6) & 0x55) + 1*((x0 & x2 & x3 & x7) & 0x55) + 2*(x0 & x2 & x4 & x6) + 2*(x0 & x2 & x4 & x7) + 1*(x0 & x2 & x6 & x7) + 2*((x0 & x3 & x4 & x6) & 0x55) + 2*((x0 & x3 & x4 & x7) & 0x55) + 1*((x0 & x3 & x6 & x7) & 0x55) + 2*((x1 & x2 & x3 & x4) & 0x55) + 1*((x1 & x2 & x3 & x6) & 0x55) + 1*((x1 & x2 & x3 & x7) & 0x55) + 2*(x1 & x2 & x4 & x6) + 2*(x1 & x2 & x4 & x7) + 1*(x1 & x2 & x6 & x7) + 2*((x1 & x3 & x4 & x6) & 0x55) + 2*((x1 & x3 & x4 & x7) & 0x55) + 1*((x1 & x3 & x6 & x7) & 0x55) - 4*((x0 & x1 & x2 & x3 & x4) & 0x55) - 2*((x0 & x1 & x2 & x3 & x6) & 0x55) - 2*((x0 & x1 & x2 & x3 & x7) & 0x55) - 4*(x0 & x1 & x2 & x4 & x6) - 4*(x0 & x1 & x2 & x4 & x7) - 2*(x0 & x1 & x2 & x6 & x7) - 4*((x0 & x1 & x3 & x4 & x6) & 0x55) - 4*((x0 & x1 & x3 & x4 & x7) & 0x55) - 2*((x0 & x1 & x3 & x6 & x7) & 0x55) - 2*((x0 & x2 & x3 & x4 & x6) & 0x55) - 2*((x0 & x2 & x3 & x4 & x7) & 0x55) - 1*((x0 & x2 & x3 & x6 & x7) & 0x55) - 2*(x0 & x2 & x4 & x6 & x7) - 2*((x0 & x3 & x4 & x6 & x7) & 0x55) - 2*((x1 & x2 & x3 & x4 & x6) & 0x55) - 2*((x1 & x2 & x3 & x4 & x7) & 0x55) - 1*((x1 & x2 & x3 & x6 & x7) & 0x55) - 2*(x1 & x2 & x4 & x6 & x7) - 2*((x1 & x3 & x4 & x6 & x7) & 0x55) + 4*((x0 & x1 & x2 & x3 & x4 & x6) & 0x55) + 4*((x0 & x1 & x2 & x3 & x4 & x7) & 0x55) + 2*((x0 & x1 & x2 & x3 & x6 & x7) & 0x55) + 4*(x0 & x1 & x2 & x4 & x6 & x7) + 4*((x0 & x1 & x3 & x4 & x6 & x7) & 0x55) + 2*((x0 & x2 & x3 & x4 & x6 & x7) & 0x55) + 2*((x1 & x2 & x3 & x4 & x6 & x7) & 0x55) - 4*((x0 & x1 & x2 & x3 & x4 & x6 & x7) & 0x55)", &["(x6 | (x7 | (x4 ^ ((x0 ^ x1) & (x2 | (x3 & 0x55))))))"], 10)]);
    check("u64", &[("1*(x4 & x6) + 1*(x6 & x7) + 1*(x0 & x2 & x6) + 1*((x0 & x3 & x6) & 0x55) + 1*(x1 & x2 & x6) + 1*((x1 & x3 & x6) & 0x55) - 2*(x4 & x6 & x7) - 2*(x0 & x1 & x2 & x6) - 2*((x0 & x1 & x3 & x6) & 0x55) - 1*((x0 & x2 & x3 & x6) & 0x55) - 2*(x0 & x2 & x4 & x6) - 2*(x0 & x2 & x6 & x7) - 2*((x0 & x3 & x4 & x6) & 0x55) - 2*((x0 & x3 & x6 & x7) & 0x55) - 1*((x1 & x2 & x3 & x6) & 0x55) - 2*(x1 & x2 & x4 & x6) - 2*(x1 & x2 & x6 & x7) - 2*((x1 & x3 & x4 & x6) & 0x55) - 2*((x1 & x3 & x6 & x7) & 0x55) + 2*((x0 & x1 & x2 & x3 & x6) & 0x55) + 4*(x0 & x1 & x2 & x4 & x6) + 4*(x0 & x1 & x2 & x6 & x7) + 4*((x0 & x1 & x3 & x4 & x6) & 0x55) + 4*((x0 & x1 & x3 & x6 & x7) & 0x55) + 2*((x0 & x2 & x3 & x4 & x6) & 0x55) + 2*((x0 & x2 & x3 & x6 & x7) & 0x55) + 4*(x0 & x2 & x4 & x6 & x7) + 4*((x0 & x3 & x4 & x6 & x7) & 0x55) + 2*((x1 & x2 & x3 & x4 & x6) & 0x55) + 2*((x1 & x2 & x3 & x6 & x7) & 0x55) + 4*(x1 & x2 & x4 & x6 & x7) + 4*((x1 & x3 & x4 & x6 & x7) & 0x55) - 4*((x0 & x1 & x2 & x3 & x4 & x6) & 0x55) - 4*((x0 & x1 & x2 & x3 & x6 & x7) & 0x55) - 8*(x0 & x1 & x2 & x4 & x6 & x7) - 8*((x0 & x1 & x3 & x4 & x6 & x7) & 0x55) - 4*((x0 & x2 & x3 & x4 & x6 & x7) & 0x55) - 4*((x1 & x2 & x3 & x4 & x6 & x7) & 0x55) + 8*((x0 & x1 & x2 & x3 & x4 & x6 & x7) & 0x55)", &["(x6 & (x4 ^ (x7 ^ ((x0 ^ x1) & (x2 | (x3 & 0x55))))))"], 10)]);
}

/// `~` moved inward through `x + 1 = -~x`: `((X - 1) | Y) + 1` is `-(-X & ~Y)`.
#[test]
fn complement_pushed_inward() {
    check(
        "i64",
        &[(
            "~ (~ ((((~ b | e) + b) + 1) - 1) - (~ ((((~ b | e) + b) + 1) - 1) & ((b ^ b) + ((b & b) + (b & b))))) + 1",
            &["-(-(b & e) & ~(2 * b))", "-(-(b & e) & ~(b + b))"],
            10,
        )],
    );
    check("u32", &[("((x + 0xfffffffe) & ~y) + 1", &["-(~(x + 0xfffffffe) | y)", "-((1 - x) | y)"], 10)]);
}

/// A case split's constant difference is folded only when it has no signed operation:
/// `-1 % 2` is -1 in i32, not the unsigned remainder 1.
#[test]
fn split_difference_with_signed_constant() {
    check(
        "i32",
        &[
            ("(x & 1) * (-1 % 2)", &["-(x & 1)"], 10),
            ("(z & 1) * (-0x7fffffff % 0x4000)", &["((z & 1) * -0x3fff)", "(-0x3fff * (z & 1))"], 10),
        ],
    );
}

/// `polish` moves leaf terms between the groups of a wide semi-linear result and rewrites
/// every pair many times; with semi-linear groups of many leaves searched in full, this
/// input took tens of seconds there.
#[test]
fn polish_join_linear_stays_fast() {
    let start = std::time::Instant::now();
    check(
        "i8",
        &[(
            "((((4 * ((z & z) ^ (~v & z))) - (-0x40 * (~y | ((u & ~x) | (u | u))))) - (2 * ~((~u ^ (~z & w)) & (~z & ~x)))) - (1 * (w | (~0x3f | ~~z))))",
            &["((((4 * (z & v)) + (0x40 * (~y | u))) + (-2 * (z | ((u ^ w) | x)))) - ((w | -0x40) | z))"],
            10,
        )],
    );
    if !cfg!(debug_assertions) {
        assert!(start.elapsed().as_secs() < 5, "took {:?}", start.elapsed());
    }
}

/// A polish pass that rebuilds a sum can leave an addition of 0 behind.
#[test]
fn polish_drops_added_zero() {
    check(
        "u8",
        &[(
            "(((((((0x5 * ((c & f) | (f & c))) - (0x2 * ((h ^ h) & (b & h)))) + (0x2 * (((-(d) - 0x1) + ((((((~((((j | b) ^ g) | h)) | f) - (~((((j | b) ^ g) | h)) & f)) + ((e | i) - (e & i))) - ((~((((j | b) ^ g) | h)) ^ f) & (e ^ i))) + ((a + c) - (a | c))) - (((~((((j | b) ^ g) | h)) ^ f) | (e ^ i)) | (a & c)))) - (~(d) & (((~((((j | b) ^ g) | h)) ^ f) | (e ^ i)) & (a & c)))))) - (0x2 * ((((h + f) - (h & f)) + ((f + f) - (f | f))) - ((h | f) | (f & f))))) + (0x2 * ((((h | h) - (h & h)) + ((b + h) - (b | h))) - ((h ^ h) | (b & h))))) - (0x5 * ((((c + f) - (c | f)) + ((f + c) - (f | c))) - ((c & f) & (f & c))))) + (0x2 * ((h | f) & (f & f))))",
            &["(2 * (~d | ((((((j | b) ^ g) | h) ^ ~f) | (e ^ i)) & (a & c))))"],
            10,
        )],
    );
}

/// A `^` with an operand that has only the top bit is a `+`, so the obfuscated
/// permutation polynomial joins the linear region (u8).
#[test]
fn xor_with_top_bit_product() {
    check(
        "u8",
        &[("0xd * (((0x45*x) + (0xcf*y)) ^ (0x80*((y*y) ^ (x*x))))", &["(x + (3 * y))", "((3 * y) + x)"], 10)],
    );
}

/// Arithmetic operands of bitwise operations that are complements of each other
/// written differently share one leaf, so `(A & ~B) + (~A & B)` becomes `A ^ B`.
#[test]
fn complement_operands_written_differently() {
    check(
        "u32",
        &[
            ("((y + x) & (~(x*w) - z)) + ((~y - x) & ((x*w) + z))", &["((y + x) ^ ((x * w) + z))"], 10),
            ("((y - w) & (~x - z)) + ((w + ~y) & (x + z))", &["((y - w) ^ (x + z))"], 10),
            ("(((z ^ x) + y) & (~x + (w & z))) + (((z ^ ~x) - y) & (x - (w & z)))", &["(((z ^ x) + y) ^ (x - (w & z)))"], 10),
        ],
    );
}
