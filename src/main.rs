mod expr_convert;

use crate::expr_convert::{egglog_to_infix, infix_to_egglog};
use clap::Parser;
use egglog_experimental::ast::Span;
use egglog_experimental::Error::ParseError;
use egglog_experimental::*;

macro_rules! rewrite {
    (
        $lhs:tt => $rhs:tt
        $(if $cond:expr)*
        ; $suffix:literal
    ) => {{
        format!(
            "(rewrite {} {} :ruleset {})\n",
            infix_to_egglog($lhs, false),
            infix_to_egglog($rhs, false),
            $suffix
        )
    }};
    (
        $lhs:tt => $rhs:tt
        $(if $cond:expr)*
    ) => {{
        rewrite! {
            $lhs => $rhs
            $(if $cond)*
            ; "default-ruleset"
        }
    }};
    (
        $lhs:tt <=> $rhs:tt
        $(if $cond:expr)*
        ; $suffix:literal
    ) => {{
        format!(
            "(birewrite {} {} :ruleset {})\n",
            infix_to_egglog($lhs, false),
            infix_to_egglog($rhs, false),
            $suffix
        )
    }};
    (
        $lhs:tt <=> $rhs:tt
        $(if $cond:expr)*
    ) => {{
        rewrite! {
            $lhs <=> $rhs
            $(if $cond)*
            ; "default-ruleset"
        }
    }};
}
fn make_egg(_num_type: &str) -> String {
    let datatype = r#"
(datatype Expr
    (Num i64)
    (Add Expr Expr)
    (Sub Expr Expr)
    (Mul Expr Expr)
    (Div Expr Expr)
    (Mod Expr Expr)
    (And Expr Expr)
    (Or Expr Expr)
    (Xor Expr Expr)
    (Shr Expr Expr)
    (Shl Expr Expr)
    (Not Expr)
    (Neg Expr)
    (Var String)
)
(ruleset default-ruleset)
(ruleset constant-folding)
(ruleset identity-zero-element)
(ruleset canonicalization)
(ruleset simplify)
(rewrite (Add (Num a) (Num b))   (Num (+ a b)) :ruleset constant-folding)
(rewrite (Sub (Num a) (Num b))   (Num (- a b)) :ruleset constant-folding)
(rewrite (Mul (Num a) (Num b))   (Num (* a b)) :ruleset constant-folding)
(rewrite (Div (Num a) (Num b))   (Num (/ a b)) :when ((!= (Num b) (Num 0)))  :ruleset constant-folding)
(rewrite (And (Num a) (Num b))   (Num (& a b)) :ruleset constant-folding)
(rewrite (Or (Num a) (Num b))   (Num (| a b)) :ruleset constant-folding)
(rewrite (Xor (Num a) (Num b))   (Num (^ a b)) :ruleset constant-folding)
(rewrite (Shl (Num a) (Num b))   (Num (<< a b)) :ruleset constant-folding)
(rewrite (Shr (Num a) (Num b))   (Num (>> a b)) :ruleset constant-folding)
(rewrite (Mod (Num a) (Num b))   (Num (% a b)) :ruleset constant-folding)
(rewrite (Not (Num a))   (Num (^ a -1)) :ruleset constant-folding)
(rewrite (Neg (Num a))   (Num (- 0 a)) :ruleset constant-folding)
"#;
    let mut egg = String::new();
    egg.push_str(&datatype);
    egg.push_str(&rewrite!("a+0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a-0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("0-a"=>"-a";"identity-zero-element"));
    egg.push_str(&rewrite!("--a"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a-a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a+-a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a*0"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a*1"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("0/a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a/1"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a*(1/a)"=>"1";"identity-zero-element"));
    egg.push_str(&rewrite!("a/-1"=>"-a";"identity-zero-element"));
    egg.push_str(&rewrite!("a/a"=>"1";"identity-zero-element"));
    egg.push_str(&rewrite!("a|0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a|-1"=>"-1";"identity-zero-element"));
    egg.push_str(&rewrite!("a|~a"=>"-1";"identity-zero-element"));
    egg.push_str(&rewrite!("a|a"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a&0"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a&-1"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a&a"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a&~a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a^a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("a^~a"=>"-1";"identity-zero-element"));
    egg.push_str(&rewrite!("a^0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a^-1"=>"~a";"identity-zero-element"));
    egg.push_str(&rewrite!("a>>0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a<<0"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("~~a"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a&(a|b)"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a|(a&b)"=>"a";"identity-zero-element"));

    egg.push_str(&rewrite!("a-b"=>"a+-b";"canonicalization"));
    egg.push_str(&rewrite!("a/b"=>"a*(1/b)";"canonicalization"));
    egg.push_str(&rewrite!("~a+1"=>"-a";"canonicalization"));
    egg.push_str(&rewrite!("a*-1"=>"-a";"canonicalization"));
    egg.push_str(&rewrite!("~(x*y)"=>"((~x*y)+(y-1))";"canonicalization"));
    egg.push_str(&rewrite!("~(x+y)"=>"((~y+1)+~x)";"canonicalization"));
    egg.push_str(&rewrite!("~(x-y)"=>"(~x-(~y+1))";"canonicalization"));
    egg.push_str(&rewrite!("~(x&y)"=>"-(x&y)-1";"canonicalization"));
    egg.push_str(&rewrite!("~(x&y)"=>"(~x|~y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x^y)"=>"((x&y)|~(x|y))";"canonicalization"));
    egg.push_str(&rewrite!("~(x|y)"=>"(~x&~y)";"canonicalization"));
    egg.push_str(&rewrite!("(x|y)"=>"(x^y)+(x&y)";"canonicalization"));
    egg.push_str(&rewrite!("-(x+y)"=>"-x+-y";"canonicalization"));
    egg.push_str(&rewrite!("-(x-y)"=>"-x+y";"canonicalization"));
    egg.push_str(&rewrite!("x+-y"=>"x-y";"canonicalization"));
    egg.push_str(&rewrite!("-(x*y)"=>"-x*y";"canonicalization"));
    egg.push_str(&rewrite!("-(x/y)"=>"-x/y";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a-b)"=>"a*a-b*b";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a+b)"=>"a*a+2*a*b+b*b";"canonicalization"));
    egg.push_str(&rewrite!("((x+y)*z)"=>"(x*z+y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x-y)*z)"=>"(x*z-y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)+(x*z))"=>"((y+z)*x)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)-(x*z))"=>"((y-z)*x)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)+y)"=>"((x+1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("(x+x)"=>"(2*x)";"canonicalization"));
    egg.push_str(&rewrite!("a>>b>>c"=>"a>>(b+c)";"canonicalization"));
    egg.push_str(&rewrite!("a|(b&c)"=>"(a|b)&(a|c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b|c)"=>"(a&b)|(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b^c)"=>"(a&b)^(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("a<<1"=>"a*2";"canonicalization"));
    egg.push_str(&rewrite!("a--b"=>"a+b";"canonicalization"));

    egg.push_str(&rewrite!("a+b"=>"b+a"));
    egg.push_str(&rewrite!("a*b"=>"b*a"));
    egg.push_str(&rewrite!("a&b"=>"b&a"));
    egg.push_str(&rewrite!("a|b"=>"b|a"));
    egg.push_str(&rewrite!("a^b"=>"b^a"));
    egg.push_str(&rewrite!("(x*(y*z))"=>"((x*y)*z)"));
    egg.push_str(&rewrite!("(x+(y+z))"=>"((x+y)+z)"));
    egg.push_str(&rewrite!("(x&(y&z))"=>"((x&y)&z)"));
    egg.push_str(&rewrite!("(x^(y^z))"=>"((x^y)^z)"));
    egg.push_str(&rewrite!("(x|(y|z))"=>"((x|y)|z)"));

    egg.push_str(&rewrite!("(x ^ y) - 2*(~x & y)" => "x - y";"simplify"));
    egg.push_str(&rewrite!("2*(x & ~y) - (x ^ y)" => "x - y";"simplify"));
    egg.push_str(&rewrite!("(a & b) ^ (a & ~b)" => "a";"simplify"));
    egg.push_str(&rewrite!("2*(x | y) + (x ^ ~y)" => "(x + y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x | ~y) + y" => "(x & y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x + y) + ~(x & y)" => "(x | y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x ^ y) + 2*(x & y)" => "x + y";"simplify"));
    egg.push_str(&rewrite!("((x & 0xFF) ^ (Num c1)) + 2*(x & (Num c2))" => "(x & 0xFF) + (Num c1)";"simplify :when ((= (& c1 255) c2))"));
    egg
}
fn simplify(s: &str, cli: &Cli) -> Result<String, Error> {
    let egg = make_egg(&cli.num_type);
    let mut egraph = new_experimental_egraph();
    egraph.parse_and_run_program(None, &egg)?;
    let result = egraph.parse_and_run_program(
        None,
        &format!(
            r#"
(let expr {})
(run-schedule
    (let-scheduler babibo
      (back-off
        :match-limit 64
        :ban-length 3
        :growth-rate 2
        :decay-rate 0.8
      )
    )
    (repeat {}
        (seq
            (run-with babibo canonicalization)
            (run-with babibo default-ruleset)
            (saturate (run constant-folding))
            (saturate (run identity-zero-element))
            (saturate (run simplify))
        )
    )
)
(extract expr)"#,
            s, cli.iter_limit
        ),
    )?;
    Ok(egglog_to_infix(
        &result
            .last()
            .ok_or(ParseError(ast::ParseError(
                Span::Panic,
                "fail to parse egglog".to_string(),
            )))?
            .to_string(),
    ))
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    #[arg(
        short,
        long,
        default_value_t = false,
        help = "Output expression in egglog format instead of simplifying"
    )]
    rule_compile: bool,
    #[arg(
        short,
        long,
        default_value_t = false,
        help = "Output expression in egglog rule format instead of simplifying"
    )]
    expr_compile: bool,
    #[arg(
        short,
        long,
        default_value = "i64",
        help = "Numeric type to use (e.g., i64, f64)"
    )]
    num_type: String,
    #[arg(
        short,
        long,
        default_value_t = 30,
        help = "Maximum number of simplification iterations"
    )]
    iter_limit: usize,
    #[arg(help = "The infix expression to simplify")]
    expr: String,
}
fn main() {
    let cli = Cli::parse();
    if cli.expr.is_empty() {
        println!("please enter a expression");
        return;
    }
    if cli.rule_compile {
        println!("{}", infix_to_egglog(&cli.expr, false));
        return;
    }
    if cli.expr_compile {
        println!("{}", infix_to_egglog(&cli.expr, true));
        return;
    }
    let egg_expr = infix_to_egglog(&cli.expr, true);
    if egg_expr.is_empty() {
        println!("please enter a valid expression");
        return;
    }
    let result = simplify(&egg_expr, &cli);
    if let Ok(v) = result {
        println!("\n{}", v);
    } else if let Err(v) = result {
        println!("\nerror:{}", v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_formal_simplify() {
        let cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i64".to_string(),
            iter_limit: 20,
            expr: "".to_string(),
        };
        let test_pairs = vec![
            ("a + 0", "a"),
            ("0 + a", "a"),
            ("a + 0 + b", "(a + b)"),
            ("a - a", "0"),
            ("a - a + b", "b"),
            ("a + b - a", "b"),
            ("a + b - b - a", "0"),
            ("a * 1", "a"),
            ("1 * a", "a"),
            ("a * 0", "0"),
            ("0 * a", "0"),
            ("a + a", "(a + a)"),
            ("a + a + a", "(3 * a)"),
            ("2 * a + 3 * a", "(5 * a)"),
            ("5 + 3", "8"),
            ("17 - 8", "9"),
            ("4 * 6", "24"),
            ("a + 5 - 5", "a"),
            ("a * 8 / 8", "a"),
            ("3 * a + 5 * a + 2 * a", "(10 * a)"),
            ("12 + a + 8 + b - 20", "(a + b)"),
            ("a & a", "a"),
            ("a | a", "a"),
            ("a ^ a", "0"),
            ("a & 0", "0"),
            ("a | 0", "a"),
            ("a ^ 0", "a"),
            ("a & -1", "a"),
            ("a | -1", "-1"),
            ("a ^ -1", "~a"),
            ("~(~a)", "a"),
            ("a & (a | b)", "a"),
            ("a | (a & b)", "a"),
            ("a ^ b ^ a", "b"),
            ("a ^ a ^ b ^ b", "0"),
            ("a ^ a ^ a", "a"),
            ("x & 255", "(x & 255)"),
            ("x & 0xff", "(x & 255)"),
            ("(x & 0xffff) << 8", "((x & 65535) << 8)"),
            ("x >> 3 << 3", "((x >> 3) << 3)"),
            ("(a + 1) & ~1", "((a + 1) & -2)"),
            ("(a * 2) >> 1", "((a * 2) >> 1)"),
            ("a + (b & 1)", "(a + (b & 1))"),
            ("(a << 3) + (b & 7)", "((a << 3) + (b & 7))"),
            ("((a + b) * c - d) + (d - a * c)", "(b * c)"),
            (
                "a * b + a * c + b * a + b * c",
                "(((b + (b + c)) * a) + (b * c))",
            ),
            (
                "(a + b + c) * (a + b + c)",
                "(((a + b) + c) * ((a + b) + c))",
            ),
            ("a - b + c - a + b - c", "0"),
            (
                "((x >> 4) & 0xf) | ((x & 0xf) << 4)",
                "(((x >> 4) & 15) | ((x & 15) << 4))",
            ),
            ("a + (~a + 1)", "0"),
            ("(a & b) ^ (a & ~b)", "a"),
            ("a + 1 + 3", "(4 + a)"),
            ("a + b + 0 + c + 0", "((a + b) + c)"),
            ("0 * (a + b + c)", "0"),
            ("1 * (a + b + c)", "((a + b) + c)"),
            ("(a + b) - (a + b)", "0"),
            ("a * (b - b)", "0"),
            ("a & ~a", "0"),
            ("a | ~a", "-1"),
            ("(a ^ b) ^ b", "a"),
            ("a ^ (b ^ a)", "b"),
            ("~0", "-1"),
            ("~-1", "0"),
            ("(x & 0xff00) >> 8", "((x & 65280) >> 8)"),
            ("x & (x | y)", "x"),
            ("(x | y) & x", "x"),
            ("a + b * 0", "a"),
            ("a * (1 + 0)", "a"),
            ("(2 * a) + (3 * a) + a", "(6 * a)"),
            ("a - 0", "a"),
            ("0 - a", "-a"),
            ("-(a - b)", "(b - a)"),
            ("a * -1", "-a"),
            ("-1 * a", "-a"),
            ("a + -a", "0"),
            ("a ^ (a ^ b ^ c) ^ b ^ c", "0"),
        ];
        for (case, expect) in test_pairs {
            let egg_expr = infix_to_egglog(case, true);
            let result = simplify(&egg_expr, &cli);
            assert_eq!(
                if result.is_ok() {
                    result.unwrap()
                } else {
                    result.unwrap_err().to_string()
                },
                expect,
                "{} {} \n{}",
                case,
                egg_expr,
                make_egg(&cli.num_type)
            );
        }
    }
}
