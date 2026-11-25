use eggy1::expr_convert::*;


#[test]
fn test_simple() {
    assert_eq!(infix_to_prefix("a + b"), "(+ a b)");
    assert_eq!(infix_to_prefix("a - b"), "(- a b)");
    assert_eq!(infix_to_prefix("a * b"), "(* a b)");
    assert_eq!(infix_to_prefix("a / b"), "(/ a b)");
    assert_eq!(infix_to_prefix("a % b"), "(% a b)");
}

#[test]
fn test_precedence() {
    assert_eq!(infix_to_prefix("a + b + c"), "(+ (+ a b) c)");
    assert_eq!(infix_to_prefix("a + b * c"), "(+ a (* b c))");
    assert_eq!(infix_to_prefix("a * b + c"), "(+ (* a b) c)");
    assert_eq!(infix_to_prefix("a * b * c"), "(* (* a b) c)");
}

#[test]
fn test_parentheses() {
    assert_eq!(infix_to_prefix("(a + b)"), "(+ a b)");
    assert_eq!(infix_to_prefix("(a + b) * c"), "(* (+ a b) c)");
    assert_eq!(infix_to_prefix("a * (b + c)"), "(* a (+ b c))");
    assert_eq!(infix_to_prefix("(a + b) * (c - d)"), "(* (+ a b) (- c d))");
}

#[test]
fn test_complex() {
    assert_eq!(
        infix_to_prefix("(a + b) * (c - d) / e"),
        "(/ (* (+ a b) (- c d)) e)"
    );
    assert_eq!(
        infix_to_prefix("a + b * c - d / e"),
        "(- (+ a (* b c)) (/ d e))"
    );
}

#[test]
fn test_variables() {
    assert_eq!(infix_to_prefix("x1 + y2"), "(+ x1 y2)");
    assert_eq!(infix_to_prefix("alpha * beta"), "(* alpha beta)");
}

#[test]
fn test_numbers() {
    assert_eq!(infix_to_prefix("42 + 13"), "(+ 42 13)");
    assert_eq!(infix_to_prefix("2 * (3 + 4)"), "(* 2 (+ 3 4))");
}

#[test]
fn test_negated_literals_wrap() {
    assert_eq!(infix_to_egglog("-5", true), "(Num -5)");
    assert_eq!(infix_to_egglog("-9223372036854775808", true), "(Num -9223372036854775808)");
    assert_eq!(infix_to_egglog("-9223372036854775809", true), "(Num 9223372036854775807)");
    assert_eq!(infix_to_egglog("-0xffffffffffffffff", true), "(Num 1)");
}

#[test]
fn test_new_operators() {
    assert_eq!(infix_to_prefix("a & b"), "(& a b)");
    assert_eq!(infix_to_prefix("a | b"), "(| a b)");
    assert_eq!(infix_to_prefix("a ^ b"), "(^ a b)");
    assert_eq!(infix_to_prefix("a % b"), "(% a b)");

    assert_eq!(infix_to_prefix("a & b | c"), "(| (& a b) c)");
    assert_eq!(infix_to_prefix("a | b & c"), "(| a (& b c))");
    assert_eq!(infix_to_prefix("a ^ b & c"), "(^ a (& b c))");
    assert_eq!(infix_to_prefix("a & b % c"), "(& a (% b c))");

    assert_eq!(infix_to_prefix("a + b & c"), "(& (+ a b) c)");
    assert_eq!(infix_to_prefix("a & b * c"), "(& a (* b c))");

    assert_eq!(infix_to_prefix("-a"), "(- a)");
    assert_eq!(infix_to_prefix("~a"), "(~ a)");

    assert_eq!(infix_to_prefix("-a + b"), "(+ (- a) b)");

    assert_eq!(infix_to_prefix("-(a + b)"), "(- (+ a b))");

    assert_eq!(infix_to_prefix("~-a"), "(~ (- a))");
    assert_eq!(infix_to_prefix("-~a"), "(- (~ a))");
    assert_eq!(infix_to_prefix("~~a"), "(~ (~ a))");

    assert_eq!(infix_to_prefix("~a + b"), "(+ (~ a) b)");
    assert_eq!(infix_to_prefix("a & ~b"), "(& a (~ b))");

    assert_eq!(infix_to_prefix("~(a + b)"), "(~ (+ a b))");
    assert_eq!(infix_to_prefix("~(a & b)"), "(~ (& a b))");
}

#[test]
fn test_prefix_to_infix_simple() {
    assert_eq!(prefix_to_infix("(+ a b)"), "(a + b)");
    assert_eq!(prefix_to_infix("(- a b)"), "(a - b)");
    assert_eq!(prefix_to_infix("(* a b)"), "(a * b)");
    assert_eq!(prefix_to_infix("(/ a b)"), "(a / b)");
}

#[test]
fn test_prefix_to_infix_precedence() {
    assert_eq!(prefix_to_infix("(+ (+ a b) c)"), "((a + b) + c)");
    assert_eq!(prefix_to_infix("(+ a (* b c))"), "(a + (b * c))");
    assert_eq!(prefix_to_infix("(+ (* a b) c)"), "((a * b) + c)");
    assert_eq!(prefix_to_infix("(* (* a b) c)"), "((a * b) * c)");
}

#[test]
fn test_prefix_to_infix_parentheses() {
    assert_eq!(prefix_to_infix("(+ a b)"), "(a + b)");
    assert_eq!(prefix_to_infix("(* (+ a b) c)"), "((a + b) * c)");
    assert_eq!(prefix_to_infix("(* a (+ b c))"), "(a * (b + c))");
    assert_eq!(
        prefix_to_infix("(* (+ a b) (- c d))"),
        "((a + b) * (c - d))"
    );
}

#[test]
fn test_prefix_to_infix_complex() {
    assert_eq!(
        prefix_to_infix("(/ (* (+ a b) (- c d)) e)"),
        "(((a + b) * (c - d)) / e)"
    );
    assert_eq!(
        prefix_to_infix("(- (+ a (* b c)) (/ d e))"),
        "((a + (b * c)) - (d / e))"
    );
}

#[test]
fn test_prefix_to_infix_unary() {
    assert_eq!(prefix_to_infix("-a"), "-a");
    assert_eq!(prefix_to_infix("~a"), "~a");
    assert_eq!(prefix_to_infix("-(+ a b)"), "-(a + b)");
    assert_eq!(prefix_to_infix("~(+ a b)"), "~(a + b)");
    assert_eq!(prefix_to_infix("~(& a b)"), "~(a & b)");
    assert_eq!(prefix_to_infix("(+ -a b)"), "(-a + b)");
    assert_eq!(prefix_to_infix("(+ ~a b)"), "(~a + b)");
    assert_eq!(prefix_to_infix("(& a ~b)"), "(a & ~b)");
}

#[test]
fn test_prefix_to_infix_new_operators() {
    assert_eq!(prefix_to_infix("(& a b)"), "(a & b)");
    assert_eq!(prefix_to_infix("(| a b)"), "(a | b)");
    assert_eq!(prefix_to_infix("(^ a b)"), "(a ^ b)");
    assert_eq!(prefix_to_infix("(% a b)"), "(a % b)");
    assert_eq!(prefix_to_infix("(| (& a b) c)"), "((a & b) | c)");
    assert_eq!(prefix_to_infix("(| a (& b c))"), "(a | (b & c))");
    assert_eq!(prefix_to_infix("(^ a (& b c))"), "(a ^ (b & c))");
    assert_eq!(prefix_to_infix("(& a (% b c))"), "(a & (b % c))");
    assert_eq!(prefix_to_infix("(& (+ a b) c)"), "((a + b) & c)");
    assert_eq!(prefix_to_infix("(& a (* b c))"), "(a & (b * c))");
}

#[test]
fn test_prefix_to_infix_roundtrip() {
    let cases = [
        "(a + b)",
        "((a * b) + c)",
        "((a + b) * c)",
        "(a * (b + c))",
        "((a + (b * c)) - (d / e))",
        "-a",
        "~(a + b)",
        "((a & b) | c)",
    ];
    for case in cases {
        let prefix = infix_to_prefix(case);
        let infix = prefix_to_infix(&prefix);
        assert_eq!(infix, case, "Roundtrip failed for case: {}", case);
    }
}

#[test]
fn test_shift_operators() {
    assert_eq!(infix_to_prefix("a << b"), "(<< a b)");
    assert_eq!(infix_to_prefix("a >> b"), "(>> a b)");
    assert_eq!(prefix_to_infix("(<< a b)"), "(a << b)");
    assert_eq!(prefix_to_infix("(>> a b)"), "(a >> b)");

    // 位移运算符的优先级（低于 + - * / %）
    assert_eq!(infix_to_prefix("a << b + c"), "(<< a (+ b c))");
    assert_eq!(infix_to_prefix("a + b << c"), "(<< (+ a b) c)");
    assert_eq!(infix_to_prefix("a * b << c"), "(<< (* a b) c)");
    assert_eq!(infix_to_prefix("a << b * c"), "(<< a (* b c))");

    // 位移运算符的结合性（左结合）
    assert_eq!(infix_to_prefix("a << b >> c"), "(>> (<< a b) c)");

    // 与其他位运算符的优先级（高于 & ^ |）
    assert_eq!(infix_to_prefix("a << b & c"), "(& (<< a b) c)");
    assert_eq!(infix_to_prefix("a & b << c"), "(& a (<< b c))");
    assert_eq!(infix_to_prefix("a << b ^ c"), "(^ (<< a b) c)");
    assert_eq!(infix_to_prefix("a << b | c"), "(| (<< a b) c)");
}

#[test]
fn test_complex_nested_expressions() {
    assert_eq!(
        prefix_to_infix("(/ (- (* (+ a b) c) d) e)"),
        "((((a + b) * c) - d) / e)"
    );
    assert_eq!(
        infix_to_prefix("((((a + b) * c) - d) / e)"),
        "(/ (- (* (+ a b) c) d) e)"
    );

    assert_eq!(
        prefix_to_infix("(+ a (* b (- c (/ d (+ e f)))))"),
        "(a + (b * (c - (d / (e + f)))))"
    );
    assert_eq!(
        infix_to_prefix("(a + (b * (c - (d / (e + f)))))"),
        "(+ a (* b (- c (/ d (+ e f)))))"
    );

    assert_eq!(
        prefix_to_infix("(+ -(& a b) ~(* c d))"),
        "(-(a & b) + ~(c * d))"
    );
    assert_eq!(
        infix_to_prefix("(-(a & b) + ~(c * d))"),
        "(+ (- (& a b)) (~ (* c d)))"
    );

    assert_eq!(
        prefix_to_infix("(| (& a b) (% (* (+ c d) (^ e f)) g))"),
        "((a & b) | (((c + d) * (e ^ f)) % g))"
    );
    assert_eq!(
        infix_to_prefix("(((a & b) | (((c + d) * (e ^ f)) % g)))"),
        "(| (& a b) (% (* (+ c d) (^ e f)) g))"
    );

    assert_eq!(prefix_to_infix("(+ ~-a -~b)"), "(~-a + -~b)");
    assert_eq!(infix_to_prefix("(~-a + -~b)"), "(+ (~ (- a)) (- (~ b)))");

    assert_eq!(
        prefix_to_infix("(* (+ a b) (- c (/ d (* e f))))"),
        "((a + b) * (c - (d / (e * f))))"
    );
    assert_eq!(
        infix_to_prefix("(((a + b) * (c - (d / (e * f)))))"),
        "(* (+ a b) (- c (/ d (* e f))))"
    );

    let complex_cases = [
        "((((a + b) * c) - d) / e)",
        "(a + (b * (c - (d / (e + f)))))",
        "(-(a & b) + ~(c * d))",
        "((a & b) | (((c + d) * (e ^ f)) % g))",
        "(~-a + -~b)",
        "((a + b) * (c - (d / (e * f))))",
        "(((((a + b) * c) - d) / e) + f)",
        "(a * (b + (c * (d - (e / f)))))",
    ];
    for case in complex_cases {
        let prefix = infix_to_prefix(case);
        let infix = prefix_to_infix(&prefix);
        assert_eq!(infix, case, "Roundtrip failed for complex case: {}", case);
    }
}

#[test]
fn negative_constants_print_as_subtraction() {
    let show = |s: &str, norm: &dyn Fn(i64) -> i64| egglog_to_infix(&infix_to_egglog(s, true), &|n| norm(n));
    let id = |n| n;
    assert_eq!(show("z + -1", &id), "(z - 1)");
    assert_eq!(show("z - -1", &id), "(z + 1)");
    assert_eq!(show("(-4 * x) + y", &id), "(y - (4 * x))");
    assert_eq!(show("y - (x * -3)", &id), "(y + (3 * x))");
    assert_eq!(show("(-4 * x) + 5", &id), "((-4 * x) + 5)");
    let i8 = |n: i64| n as i8 as i64;
    assert_eq!(show("x + -128", &i8), "(x + -0x80)");
    let u32 = |n: i64| n as u32 as i64;
    assert_eq!(show("y + 0xfffffffe", &u32), "(y + 0xfffffffe)");
}
