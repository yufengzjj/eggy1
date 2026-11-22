use eggy1::expr_convert::{ac_canon_infix, infix_to_egglog};
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
        ("u8", "(x & 0x1f) * 4", "((x & 0x1f) * 4)"),
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
            &["((x ^ ~y) - y)", "(~y - (x ^ y))", "(x + ~((x | y) * 2))"],
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
            ("(((((-(((z ^ x) ^ (x & -((x & -((x & y))))))) - (((y | z) | (y & -((y & -((y & x)))))) - ((y | z) & -(((y | z) & -(((y | z) & (y & -((y & -((y & x)))))))))))) + ((y ^ y) | (y | y))) + (0x7 * ((((z + z) - (z | z)) + ((z | z) - (z & z))) - ((z & z) | (z ^ z))))) - ((((y | y) - (y & y)) + ((y + y) - (y & y))) - ((y ^ y) & (y | y)))) - (0x7 * ((z & z) & (z ^ z))))", &["(-(x ^ (z | y)) - z)"], 10),
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
            ("0xb * ((~(y & x) | (x + 0xff)) - ((y & x) | (-0x100 - x)))", &["(((x & ~y) + 0xff) * 0xb)"], 10),
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
    check("u8", &[("3*x*x + 7*x*y + 2*y*y + x + 2*y", &["((x + (2 * y)) * ((3 * x) - ~y))", "((x + (2 * y)) * (((3 * x) + y) + 1))"], 10)]);
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
