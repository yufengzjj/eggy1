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
            // Sign bit not known zero: arithmetic `>>` keeps it, must NOT fold.
            ("(x & -0x100) >> 8", &["((x & -0x100) >> 8)"], 10),
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
                &["((5 * (x ^ y)) + (-0x17 * ~(x | y)))", "((5 * (x ^ y)) - (0x17 * ~(x | y)))"],
                10,
            ),
            // Variables {x, y, z} and {a, t} do not interact, so they are rebuilt separately (NeuReduce).
            (
                "2*(~y|z)-(~x&y|~z)-3*(x&y^~z)-(x&~y&~z)+3*(y|~z)-2*(x&y|z)-(~x)-(x&y^z)-(a&~t)+a",
                &["((((y ^ z) & x) + (-2 * (y ^ z))) + (a & t))"],
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
        ("3*(x | 0x5c) - 2*(x & 0x5c) - (x ^ 0x5c) - 2*(x & ~0x5c)", &["(0xb8 - (x & 0x5c))"], 10),
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
    let again = simplify_round(&make_egg(&cli.num_type), &seed, &cli).unwrap();
    assert_eq!(seed, again, "simplify result is not a fixpoint");
}
