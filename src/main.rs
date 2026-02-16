mod expr_convert;

use crate::expr_convert::{egglog_to_infix, infix_to_egglog};
use clap::Parser;
use egglog::Error::ParseError;
use egglog::ast::Span;
use egglog::*;

macro_rules! rewrite {
    (
        $lhs:tt => $rhs:tt
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
        ; $suffix:expr
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
    ) => {{
        rewrite! {
            $lhs => $rhs
            ; "default-ruleset"
        }
    }};
    (
        $lhs:tt <=> $rhs:tt
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
        ; $suffix:expr
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
    ) => {{
        rewrite! {
            $lhs <=> $rhs
            ; "default-ruleset"
        }
    }};
}
fn make_egg(num_type: &str) -> String {
    let datatype = format!(
        r#"
(datatype Expr
    (Num i64 :cost 0)
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
    (Pow Expr Expr)
    (Not Expr)
    (Neg Expr)
    (Var String)
)
(ruleset default-ruleset)
(ruleset constant-folding)
(ruleset identity-zero-element)
(ruleset canonicalization)
(ruleset simplify)
(rewrite (Add (Num a) (Num b))   (Num (wrapping-add-{0} a b)) :ruleset constant-folding)
(rewrite (Sub (Num a) (Num b))   (Num (wrapping-sub-{0} a b)) :ruleset constant-folding)
(rewrite (Mul (Num a) (Num b))   (Num (wrapping-mul-{0} a b)) :ruleset constant-folding)
(rewrite (Div (Num a) (Num b))   (Num (wrapping-div-{0} a b)) :when ((!= (Num b) (Num 0))) :ruleset constant-folding)
(rewrite (And (Num a) (Num b))   (Num (wrapping-and-{0} a b)) :ruleset constant-folding)
(rewrite (Or (Num a) (Num b))   (Num (wrapping-or-{0} a b)) :ruleset constant-folding)
(rewrite (Xor (Num a) (Num b))   (Num (wrapping-xor-{0} a b)) :ruleset constant-folding)
(rewrite (Shl (Num a) (Num b))   (Num (wrapping-shl-{0} a b)) :ruleset constant-folding)
(rewrite (Shr (Num a) (Num b))   (Num (wrapping-shr-{0} a b)) :ruleset constant-folding)
(rewrite (Mod (Num a) (Num b))   (Num (wrapping-mod-{0} a b)) :when ((!= (Num b) (Num 0))) :ruleset constant-folding)
(rewrite (Not (Num a))   (Num (wrapping-not-{0} a)) :ruleset constant-folding)
(rewrite (Neg (Num a))   (Num (wrapping-neg-{0} a)) :ruleset constant-folding)
"#,
        num_type
    );
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

    egg.push_str(&rewrite!("a-b"<=>"a+-b";"canonicalization"));
    egg.push_str(&rewrite!("a/b"<=>"a*(1/b)";"canonicalization"));
    egg.push_str(&rewrite!("~a"<=>"-a-1";"canonicalization"));
    egg.push_str(&rewrite!("-a"<=>"a*-1";"canonicalization"));
    egg.push_str(&rewrite!("~(x*y)"<=>"((~x*y)+(y-1))";"canonicalization"));
    egg.push_str(&rewrite!("~(x+y)"<=>"((~y+1)+~x)";"canonicalization"));
    egg.push_str(&rewrite!("~(x-y)"<=>"(~x-(~y+1))";"canonicalization"));
    egg.push_str(&rewrite!("~(x&y)"<=>"-(x&y)-1";"canonicalization"));
    egg.push_str(&rewrite!("~(x&y)"<=>"(~x|~y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x^y)"<=>"(x^~y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x|y)"<=>"(~x&~y)";"canonicalization"));
    egg.push_str(&rewrite!("(x|y)"<=>"(x^y)+(x&y)";"canonicalization"));
    egg.push_str(&rewrite!("-(x+y)"<=>"-x-y";"canonicalization"));
    egg.push_str(&rewrite!("-(x-y)"<=>"y-x";"canonicalization"));
    egg.push_str(&rewrite!("-(x*y)"<=>"-x*y";"canonicalization"));
    egg.push_str(&rewrite!("(Num x)*-y"<=>"(- (Num x))*y";"canonicalization"));
    egg.push_str(&rewrite!("-(x/y)"<=>"-x/y";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a-b)"<=>"a*a-b*b";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a+b)"<=>"a*a+2*a*b+b*b";"canonicalization"));
    egg.push_str(&rewrite!("((x+y)*z)"<=>"(x*z+y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x-y)*z)"<=>"(x*z-y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)+y)"<=>"((x+1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)-y)"<=>"((x-1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("a>>b>>c"=>"a>>(b+c)";"canonicalization"));
    egg.push_str(&rewrite!("a<<b<<c"=>"a<<(b+c)";"canonicalization"));
    egg.push_str(&rewrite!("a|(b&c)"<=>"(a|b)&(a|c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b|c)"<=>"(a&b)|(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b^c)"<=>"(a&b)^(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("(x&y)>>z"<=>"(x>>z)&(y>>z)";"canonicalization"));
    egg.push_str(&rewrite!("2*x"<=>"x+x";"canonicalization"));
    if ["u64", "u32", "u16", "u8"].contains(&num_type) {
        egg.push_str(&rewrite!("a<<1"<=>"a*2";"canonicalization"));
    }
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
    egg.push_str(&rewrite!("(x & ~y) - (~x & y)" => "x - y";"simplify"));
    egg.push_str(&rewrite!("(a & b) ^ (a & ~b)" => "a";"simplify"));
    egg.push_str(&rewrite!("2*(x | y) + (x ^ ~y)" => "(x + y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x | ~y) + y" => "(x & y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x + y) + ~(x & y)" => "(x | y) - 1";"simplify"));
    egg.push_str(&rewrite!("(x ^ y) + 2*(x & y)" => "x + y";"simplify"));
    egg.push_str(&rewrite!("((x & 0xff) ^ (Num c1)) + 2*(x & (Num c2))" => "(x & 0xff) + (Num c1)";"simplify :when ((= (& c1 255) c2))"));
    egg.push_str(&rewrite!("(x ^ (Num c1)) + 2*(x | (Num c2))" => "x + (Num c2) - 1";format!("simplify :when ((is-bit-not-eq-{} c1 c2))",num_type)));
    egg.push_str(&rewrite!("(x - y) - 2*(x | ~y)" => "(x ^ y) + 2";"simplify"));
    egg.push_str(&rewrite!("(x | y)*(x & y) + (x & ~y)*(y & ~x)" => "x * y";"simplify"));
    egg.push_str(&rewrite!("(x + y) - (x | y)" => "x & y";"simplify"));
    egg.push_str(&rewrite!("(y & ~x) - y" => "-(y & x)";"simplify"));
    egg.push_str(&rewrite!("x - (y & x)" => "x & ~y";"simplify"));
    egg.push_str(&rewrite!("x + (y&~x)" => "x | y";"simplify"));
    egg.push_str(&rewrite!("(x | y) - y "=>" x & ~y";"simplify"));
    egg.push_str(&rewrite!("x ^ (x & y) "=>" x & ~y";"simplify"));
    egg.push_str(&rewrite!("(x | y) ^ y "=>" x & ~y";"simplify"));
    egg.push_str(&rewrite!("(x * x) & 3 "=>" x & 1";"simplify"));
    egg.push_str(&rewrite!("~x ^ ~y "=>" x ^ y";"simplify"));
    egg.push_str(&rewrite!("(x | y) ^ (~x | ~y)"=>"~(x ^ y)";"simplify"));
    egg.push_str(&rewrite!("((x | y) - (x & y)) "=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x & ~y) - (x & y) "=>"(x ^ y) - y";"simplify"));
    egg.push_str(&rewrite!("(x | y) + (x & ~y)"=>"(x ^ y) + x";"simplify"));
    egg.push_str(&rewrite!("(x & y) + (x & ~y)"=>"x";"simplify"));
    egg.push_str(&rewrite!("(x & y) ^ (x | y)"=>"x ^ y";"simplify"));

    egg
}
#[rustfmt::skip]
fn init_egg_function(eg: &mut EGraph) {
    add_primitive!(eg, "wrapping-add-i64" = |a: i64, b: i64| -> i64 { a.wrapping_add(b) } );
    add_primitive!(eg, "wrapping-add-u64" = |a: i64, b: i64| -> i64 { (a as u64).wrapping_add(b as u64) as i64 } );
    add_primitive!(eg, "wrapping-add-i32" = |a: i64, b: i64| -> i64 { (a as i32).wrapping_add(b as i32) as i64 } );
    add_primitive!(eg, "wrapping-add-u32" = |a: i64, b: i64| -> i64 { (a as u32).wrapping_add(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-add-i16" = |a: i64, b: i64| -> i64 { (a as i16).wrapping_add(b as i16) as i64 } );
    add_primitive!(eg, "wrapping-add-u16" = |a: i64, b: i64| -> i64 { (a as u16).wrapping_add(b as u16) as i64 } );
    add_primitive!(eg, "wrapping-add-i8" = |a: i64, b: i64| -> i64 { (a as i8).wrapping_add(b as i8) as i64 } );
    add_primitive!(eg, "wrapping-add-u8" = |a: i64, b: i64| -> i64 { (a as u8).wrapping_add(b as u8) as i64 } );

    add_primitive!(eg, "wrapping-sub-i64" = |a: i64, b: i64| -> i64 { a.wrapping_sub(b) } );
    add_primitive!(eg, "wrapping-sub-u64" = |a: i64, b: i64| -> i64 { (a as u64).wrapping_sub(b as u64) as i64 } );
    add_primitive!(eg, "wrapping-sub-i32" = |a: i64, b: i64| -> i64 { (a as i32).wrapping_sub(b as i32) as i64 } );
    add_primitive!(eg, "wrapping-sub-u32" = |a: i64, b: i64| -> i64 { (a as u32).wrapping_sub(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-sub-i16" = |a: i64, b: i64| -> i64 { (a as i16).wrapping_sub(b as i16) as i64 } );
    add_primitive!(eg, "wrapping-sub-u16" = |a: i64, b: i64| -> i64 { (a as u16).wrapping_sub(b as u16) as i64 } );
    add_primitive!(eg, "wrapping-sub-i8" = |a: i64, b: i64| -> i64 { (a as i8).wrapping_sub(b as i8) as i64 } );
    add_primitive!(eg, "wrapping-sub-u8" = |a: i64, b: i64| -> i64 { (a as u8).wrapping_sub(b as u8) as i64 } );

    add_primitive!(eg, "wrapping-mul-i64" = |a: i64, b: i64| -> i64 { a.wrapping_mul(b) } );
    add_primitive!(eg, "wrapping-mul-u64" = |a: i64, b: i64| -> i64 { (a as u64).wrapping_mul(b as u64) as i64 } );
    add_primitive!(eg, "wrapping-mul-i32" = |a: i64, b: i64| -> i64 { (a as i32).wrapping_mul(b as i32) as i64 } );
    add_primitive!(eg, "wrapping-mul-u32" = |a: i64, b: i64| -> i64 { (a as u32).wrapping_mul(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-mul-i16" = |a: i64, b: i64| -> i64 { (a as i16).wrapping_mul(b as i16) as i64 } );
    add_primitive!(eg, "wrapping-mul-u16" = |a: i64, b: i64| -> i64 { (a as u16).wrapping_mul(b as u16) as i64 } );
    add_primitive!(eg, "wrapping-mul-i8" = |a: i64, b: i64| -> i64 { (a as i8).wrapping_mul(b as i8) as i64 } );
    add_primitive!(eg, "wrapping-mul-u8" = |a: i64, b: i64| -> i64 { (a as u8).wrapping_mul(b as u8) as i64 } );

    add_primitive!(eg, "wrapping-div-i64" = |a: i64, b: i64| -> i64 { a.wrapping_div(b) } );
    add_primitive!(eg, "wrapping-div-u64" = |a: i64, b: i64| -> i64 { (a as u64).wrapping_div(b as u64) as i64 } );
    add_primitive!(eg, "wrapping-div-i32" = |a: i64, b: i64| -> i64 { (a as i32).wrapping_div(b as i32) as i64 } );
    add_primitive!(eg, "wrapping-div-u32" = |a: i64, b: i64| -> i64 { (a as u32).wrapping_div(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-div-i16" = |a: i64, b: i64| -> i64 { (a as i16).wrapping_div(b as i16) as i64 } );
    add_primitive!(eg, "wrapping-div-u16" = |a: i64, b: i64| -> i64 { (a as u16).wrapping_div(b as u16) as i64 } );
    add_primitive!(eg, "wrapping-div-i8" = |a: i64, b: i64| -> i64 { (a as i8).wrapping_div(b as i8) as i64 } );
    add_primitive!(eg, "wrapping-div-u8" = |a: i64, b: i64| -> i64 { (a as u8).wrapping_div(b as u8) as i64 } );

    add_primitive!(eg, "wrapping-pow-i64" = |a: i64, b: i64| -> i64 { a.wrapping_pow(b as u32) } );
    add_primitive!(eg, "wrapping-pow-u64" = |a: i64, b: i64| -> i64 { (a as u64).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-i32" = |a: i64, b: i64| -> i64 { (a as i32).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-u32" = |a: i64, b: i64| -> i64 { (a as u32).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-i16" = |a: i64, b: i64| -> i64 { (a as i16).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-u16" = |a: i64, b: i64| -> i64 { (a as u16).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-i8" = |a: i64, b: i64| -> i64 { (a as i8).wrapping_pow(b as u32) as i64 } );
    add_primitive!(eg, "wrapping-pow-u8" = |a: i64, b: i64| -> i64 { (a as u8).wrapping_pow(b as u32) as i64 } );

    add_primitive!(eg, "wrapping-and-i64" = |a: i64, b: i64| -> i64 { a & b } );
    add_primitive!(eg, "wrapping-and-u64" = |a: i64, b: i64| -> i64 { ((a as u64) & (b as u64)) as i64 } );
    add_primitive!(eg, "wrapping-and-i32" = |a: i64, b: i64| -> i64 { ((a as i32) & (b as i32)) as i64 } );
    add_primitive!(eg, "wrapping-and-u32" = |a: i64, b: i64| -> i64 { ((a as u32) & (b as u32)) as i64 } );
    add_primitive!(eg, "wrapping-and-i16" = |a: i64, b: i64| -> i64 { ((a as i16) & (b as i16)) as i64 } );
    add_primitive!(eg, "wrapping-and-u16" = |a: i64, b: i64| -> i64 { ((a as u16) & (b as u16)) as i64 } );
    add_primitive!(eg, "wrapping-and-i8" = |a: i64, b: i64| -> i64 { ((a as i8) & (b as i8)) as i64 } );
    add_primitive!(eg, "wrapping-and-u8" = |a: i64, b: i64| -> i64 { ((a as u8) & (b as u8)) as i64 } );

    add_primitive!(eg, "wrapping-or-i64" = |a: i64, b: i64| -> i64 { a | b } );
    add_primitive!(eg, "wrapping-or-u64" = |a: i64, b: i64| -> i64 { ((a as u64) | (b as u64)) as i64 } );
    add_primitive!(eg, "wrapping-or-i32" = |a: i64, b: i64| -> i64 { ((a as i32) | (b as i32)) as i64 } );
    add_primitive!(eg, "wrapping-or-u32" = |a: i64, b: i64| -> i64 { ((a as u32) | (b as u32)) as i64 } );
    add_primitive!(eg, "wrapping-or-i16" = |a: i64, b: i64| -> i64 { ((a as i16) | (b as i16)) as i64 } );
    add_primitive!(eg, "wrapping-or-u16" = |a: i64, b: i64| -> i64 { ((a as u16) | (b as u16)) as i64 } );
    add_primitive!(eg, "wrapping-or-i8" = |a: i64, b: i64| -> i64 { ((a as i8) | (b as i8)) as i64 } );
    add_primitive!(eg, "wrapping-or-u8" = |a: i64, b: i64| -> i64 { ((a as u8) | (b as u8)) as i64 } );

    add_primitive!(eg, "wrapping-xor-i64" = |a: i64, b: i64| -> i64 { a ^ b } );
    add_primitive!(eg, "wrapping-xor-u64" = |a: i64, b: i64| -> i64 { ((a as u64) ^ (b as u64)) as i64 } );
    add_primitive!(eg, "wrapping-xor-i32" = |a: i64, b: i64| -> i64 { ((a as i32) ^ (b as i32)) as i64 } );
    add_primitive!(eg, "wrapping-xor-u32" = |a: i64, b: i64| -> i64 { ((a as u32) ^ (b as u32)) as i64 } );
    add_primitive!(eg, "wrapping-xor-i16" = |a: i64, b: i64| -> i64 { ((a as i16) ^ (b as i16)) as i64 } );
    add_primitive!(eg, "wrapping-xor-u16" = |a: i64, b: i64| -> i64 { ((a as u16) ^ (b as u16)) as i64 } );
    add_primitive!(eg, "wrapping-xor-i8" = |a: i64, b: i64| -> i64 { ((a as i8) ^ (b as i8)) as i64 } );
    add_primitive!(eg, "wrapping-xor-u8" = |a: i64, b: i64| -> i64 { ((a as u8) ^ (b as u8)) as i64 } );

    add_primitive!(eg, "wrapping-shl-i64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { 0 } else { a << (b as u64) } } );
    add_primitive!(eg, "wrapping-shl-u64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { 0 } else{((a as u64) << (b as u64)) as i64} } );
    add_primitive!(eg, "wrapping-shl-i32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { 0 } else{((a as i32) << (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shl-u32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { 0 } else{((a as u32) << (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shl-i16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { 0 } else{((a as i16) << (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shl-u16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { 0 } else{((a as u16) << (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shl-i8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { 0 } else{((a as i8) << (b as u8)) as i64} } );
    add_primitive!(eg, "wrapping-shl-u8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { 0 } else{((a as u8) << (b as u8)) as i64} } );

    add_primitive!(eg, "wrapping-shr-i64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { 0 } else { a >> (b as u64) } } );
    add_primitive!(eg, "wrapping-shr-u64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { 0 } else{((a as u64) >> (b as u64)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { 0 } else{((a as i32) >> (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { 0 } else{((a as u32) >> (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { 0 } else{((a as i16) >> (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { 0 } else{((a as u16) >> (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { 0 } else{((a as i8) >> (b as u8)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { 0 } else{((a as u8) >> (b as u8)) as i64} } );

    add_primitive!(eg, "wrapping-mod-i64" = |a: i64, b: i64| -> i64 { a % b } );
    add_primitive!(eg, "wrapping-mod-u64" = |a: i64, b: i64| -> i64 { ((a as u64) % (b as u64)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i32" = |a: i64, b: i64| -> i64 { ((a as i32) % (b as i32)) as i64 } );
    add_primitive!(eg, "wrapping-mod-u32" = |a: i64, b: i64| -> i64 { ((a as u32) % (b as u32)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i16" = |a: i64, b: i64| -> i64 { ((a as i16) % (b as i16)) as i64 } );
    add_primitive!(eg, "wrapping-mod-u16" = |a: i64, b: i64| -> i64 { ((a as u16) % (b as u16)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i8" = |a: i64, b: i64| -> i64 { ((a as i8) % (b as i8)) as i64 } );
    add_primitive!(eg, "wrapping-mod-u8" = |a: i64, b: i64| -> i64 { ((a as u8) % (b as u8)) as i64 } );

    add_primitive!(eg, "wrapping-not-i64" = |a: i64| -> i64 { !a } );
    add_primitive!(eg, "wrapping-not-u64" = |a: i64| -> i64 { (!(a as u64)) as i64 } );
    add_primitive!(eg, "wrapping-not-i32" = |a: i64| -> i64 { (!(a as i32)) as i64 } );
    add_primitive!(eg, "wrapping-not-u32" = |a: i64| -> i64 { (!(a as u32)) as i64 } );
    add_primitive!(eg, "wrapping-not-i16" = |a: i64| -> i64 { (!(a as i16)) as i64 } );
    add_primitive!(eg, "wrapping-not-u16" = |a: i64| -> i64 { (!(a as u16)) as i64 } );
    add_primitive!(eg, "wrapping-not-i8" = |a: i64| -> i64 { (!(a as i8)) as i64 } );
    add_primitive!(eg, "wrapping-not-u8" = |a: i64| -> i64 { (!(a as u8)) as i64 } );

    add_primitive!(eg, "wrapping-neg-i64" = |a: i64| -> i64 { a.wrapping_neg() } );
    add_primitive!(eg, "wrapping-neg-u64" = |a: i64| -> i64 { ((a as u64).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-i32" = |a: i64| -> i64 { ((a as i32).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-u32" = |a: i64| -> i64 { ((a as u32).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-i16" = |a: i64| -> i64 { ((a as i16).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-u16" = |a: i64| -> i64 { ((a as u16).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-i8" = |a: i64| -> i64 { ((a as i8).wrapping_neg()) as i64 } );
    add_primitive!(eg, "wrapping-neg-u8" = |a: i64| -> i64 { ((a as u8).wrapping_neg()) as i64 } );

    add_primitive!( eg, "is-bit-not-eq-i64" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffffffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u64" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffffffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i32" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u32" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i16" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u16" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i8" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u8" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xff).then_some(()) });
}
fn simplify(s: &str, cli: &Cli) -> Result<String, Error> {
    let egg = make_egg(&cli.num_type);
    let mut egraph = new_experimental_egraph();
    init_egg_function(&mut egraph);
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
        :decay-rate 0.9
      )
    )
    (repeat {}
        (seq
            (run-with babibo canonicalization)
            (run-with babibo default-ruleset)
            (saturate (run constant-folding))
            (saturate (run identity-zero-element))
            (run-with babibo simplify)
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
        value_parser=["i64","u64","i32","u32","i16","u16","i8","u8"],
        help = "Numeric type to use"
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
                "((((b + c) + b) * a) + (b * c))",
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
    #[test]
    fn test_complex_simplify() {
        let cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i8".to_string(),
            iter_limit: 40,
            expr: "".to_string(),
        };
        let test_pairs = vec![
            ("x + (~y + 1)", vec!["(x - y)"]),
            ("(x ^ y) - 2*(~x & y)", vec!["(x - y)"]),
            ("(x & ~y) - (~x & y)", vec!["(x - y)"]),
            ("2*(x & ~y) - (x ^ y)", vec!["(x - y)"]),
            ("(-x - 1) - (-2 * x)", vec!["(-1 + x)", "~-x"]),
            ("2*x + ~x", vec!["~-x","(-1 + x)"]),
            (
                "2*(x | y) + (x ^ ~y)",
                vec!["(~-y + x)", "(~-x + y)", "((x + y) + -1)", "~(-y - x)","~(-x - y)"],
            ),
            ("(x | ~y) + y", vec!["((x & y) + -1)", "~-(x & y)"]),
            (
                "(x + y) + ~(x & y)",
                vec!["((x | y) + -1)", "((y | x) + -1)", "~-(x | y)", "~-(y | x)"],
            ),
            (
                "(~x | 1) + x",
                vec!["((1 & x) + -1)", "-(~x & 1)", "-(1 & ~x)", "~-(1 & x)"],
            ),
            ("x - (~y + 1)", vec!["(x + y)"]),
            ("(x ^ y) + 2*(x & y)", vec!["(x + y)"]),
            ("(x | y) + (x & y)", vec!["(x + y)"]),
            ("2*(x | y) - (x ^ y)", vec!["(x + y)"]),
            ("2*(x | y | z) - (x ^ (y | z))", vec!["((y | z) + x)"]),
            ("(x ^ y) + 2*(x & y)", vec!["(x + y)"]),
            ("(a ^ 5) + 2*(a & 5)", vec!["(a + 5)"]),
            (
                "((a & 0xff) ^ 0x12) + 2*(a & 0x12)",
                vec!["((a & 0xff) + 0x12)"],
            ),
            ("(a ^ 0xfe) + 2*(a | 0x01)", vec!["a"]),
            (
                "~(x ^ y) + 2*(x | y)",
                vec!["((y + x) - 1)", "((x + y) - 1)", "~-(x + y)","~(-y - x)","~(-x - y)","((x + y) + -1)"],
            ),
            (
                "~(x ^ y) - (-2 * (x | y))",
                vec!["((y + x) - 1)", "((x + y) - 1)", "~-(x + y)","~(-x - y)","~(-y - x)","((-1 + x) + y)"],
            ),
            ("(x - y) - 2*(x | ~y)", vec!["((x ^ y) + 2)"]),
            ("(x - y) - 2*(~(~x & y))", vec!["((x ^ y) + 2)"]),
            ("(x | y)*(x & y) + (x & ~y)*(y & ~x)", vec!["(x * y)"]),
            ("(x | y)*(x & y) + ~(x | ~y)*(x & ~y)", vec!["(x * y)"]),
            (
                "2 + 2*(y + (x | ~y))",
                vec!["(2 * (x & y))", "((x & y) * 2)"],
            ),
            ("-(x & y) - (x & y)", vec!["(-2 * (x & y))"]),
            ("(~x | y) - ~x", vec!["(x & y)"]),
            ("(x + y) - (x | y)", vec!["(x & y)"]),
            ("(x | y) - (x ^ y)", vec!["(x & y)"]),
            ("(x | y) & ~(x ^ y)", vec!["(x & y)"]),
            ("(x & y) & ~(x ^ y)", vec!["(x & y)"]),
            ("x & ~(x ^ y)", vec!["(x & y)"]),
            ("(x | y) - y", vec!["(x & ~y)"]),
            ("x - (x & y)", vec!["(x & ~y)"]),
            ("x ^ (x & y)", vec!["(x & ~y)"]),
            ("x & (x ^ y)", vec!["(x & ~y)"]),
            ("(x | y) ^ y", vec!["(x & ~y)"]),
            (
                "(x & z) | (y & z)",
                vec!["((x | y) & z)", "(z & (y | x))", "(z & (x | y))"],
            ),
            ("(x & z) ^ (y & z)", vec!["((x ^ y) & z)", "(z & (y ^ x))","(z & (x ^ y))"]),
            ("(~x | y) + (x + 1)", vec!["(x & y)"]),
            ("(x | y) & (x ^ ~y)", vec!["(x & y)"]),
            (" (x ^ ~y) & y", vec!["(x & y)"]),
            ("(x * x) & 3", vec!["(x & 1)"]),
            ("-x - 1", vec!["~x"]),
            ("~(x | y) | ~y", vec!["~y"]),
            ("(x - 1) - 2*x", vec!["~x"]),
            ("~(x ^ y) ^ y", vec!["~x"]),
            ("~x ^ ~y", vec!["(x ^ y)"]),
            ("(x ^ y) | ~(x | y)", vec!["~(x & y)"]),
            ("~x | ~y", vec!["~(x & y)"]),
            ("~x & ~y", vec!["~(x | y)"]),
            ("(x & y) | ~(x | y)", vec!["~(x ^ y)","(x ^ ~y)","(~y ^ x)","(~x ^ y)","(y ^ ~x)"]),
            ("(x & y) ^ (x | ~y)", vec!["~y"]),
            ("(x & y) | (~x & ~y)", vec!["~(x ^ y)","(x ^ ~y)","(~y ^ x)","(~x ^ y)","(y ^ ~x)"]),
            ("(x | y) ^ (~x | ~y)", vec!["~(x ^ y)","(x ^ ~y)","(~y ^ x)","(~x ^ y)","(y ^ ~x)"]),
            ("(x | ~y) & (~x | y)", vec!["~(x ^ y)","(x ^ ~y)","(~y ^ x)","(~x ^ y)","(y ^ ~x)"]),
            ("(~x | ~y) | (x ^ y)", vec!["~(x & y)"]),
            ("~x | (x ^ y)", vec!["~(x & y)","~(y & x)"]),
            ("(x ^ ~y) - 2*(x & y)", vec!["~(x + y)","(~x - y)","(~y - x)"]),
            ("(x & ~y) | ~(x | y)", vec!["~y"]),
            ("~x & (~x ^ c)", vec!["(x & ~c) ^ ~c","~(x | c)"]),
            ("((x ^ 0x12) & 1) | ((x ^ 8) & 0xfe)", vec!["(x ^ 8)"]),
            ("(x - 7) + 11*(x - 8)", vec!["(-0x5f + (0xc * x))","((x * 0xc) + -0x5f)","((0xc * x) + -0x5f)"]),
            ("(x >> z) & (y >> z)", vec!["((x & y) >> z)"]),
            ("2*x - (x & ~y)", vec!["(x + (x & y))","((x & y) + x)"]),
            ("(x & ~y) - 2*x", vec!["-(x + (x & y))","(-(x & y) - x)"]),
            ("(x & ~y) - (x & y)", vec!["((x ^ y) - y)"]),
            ("(~x | (~y & z)) + (x + (y & z)) - z", vec!["(x | (y | ~z))","((y | ~z) | x)","((~z | y) | x)"]),
            ("(x | y) + (x & ~y)", vec!["((x ^ y) + x)"]),
            ("(x & y) + (x & ~y)", vec!["x"]),
            ("(x & y) ^ (x & ~y)", vec!["x"]),
            ("x & (x | y)", vec!["x"]),
            ("~(x - 1)", vec!["-x"]),
            ("(x ^ y) - 2*(x | y)", vec!["-(x + y)"]),
            ("(-2 * (x | y)) + (x ^ y)", vec!["-(x + y)"]),
            ("(x ^ (y | z)) - 2*((x | y) | z)", vec!["-(x + (y | z))"]),
            ("(x & y) - (x + y)", vec!["-(x | y)"]),
            ("(x & y) - (x | y)", vec!["-(x ^ y)"]),
            ("(x + y) - 2*(x | y)", vec!["-(x ^ y)"]),
            ("(x + y) - (x & y)", vec!["(x | y)","(y | x)"]),
            ("(x - y) - (x & -y)", vec!["(x | -y)"]),
            ("(x & y) + (x ^ y)", vec!["(x | y)","(y | x)"]),
            ("(x ^ y) + (x & y)", vec!["(x | y)","(y | x)"]),
            ("((x + y) + 1) + ~(x & y)", vec!["(x | y)","(y | x)"]),
            ("(x + (x ^ y)) - (x & ~y)", vec!["(x | y)","(y | x)"]),
            ("(x & y) | (x ^ y)", vec!["(x | y)","(y | x)"]),
            ("(x & (y ^ z)) | ((x ^ y) ^ z)", vec!["(x | (y ^ z))"]),
            ("(x ^ y) | y", vec!["(x | y)","(y | x)"]),
            ("(x & y) ^ (x ^ y)", vec!["(x | y)","(y | x)"]),
            ("~x ^ (x & y)", vec!["(~x | y)"]),
            ("x ^ (~x & y)", vec!["(x | y)","(y | x)"]),
            ("(x & ~y) + y", vec!["(x | y)","(y | x)","(y | x)"]),
            ("(x | y) | (~x ^ ~y)", vec!["(x | y)","(y | x)"]),
            ("(x & y) | ~(~x ^ y)", vec!["(x | y)","(y | x)"]),
            ("(~x & y) | x", vec!["(x | y)","(y | x)"]),
            ("~(~x | ~y) | (x ^ y)", vec!["(x | y)","(y | x)"]),
            ("(x - y) + (~x | y)", vec!["(x | ~y)"]),
            ("(~x | y) ^ (x ^ y)", vec!["(x | ~y)"]),
            ("(x | y) - (x & y)", vec!["(x ^ y)"]),
            ("2*(x | y) - (x + y)", vec!["(x ^ y)"]),
            ("(x + y) - 2*(x & y)", vec!["(x ^ y)"]),
            ("((x - y) - 2*(x | ~y)) - 2", vec!["(x ^ y)"]),
            ("x - (2*(x & y) - y)", vec!["(x ^ y)"]),
            ("x - (2*(y & ~(x ^ y)) - y)", vec!["(x ^ y)"]),
            ("x - (2*(x & y) - y)", vec!["(x ^ y)"]),
            ("x - 2*(x & y)", vec!["((x ^ y) - y)"]),
            ("(x & ~y) | (~x & y)", vec!["(x ^ y)"]),
            ("(~x & y) ^ (x & ~y)", vec!["(x ^ y)"]),
            ("(x & y) ^ (x | y)", vec!["(x ^ y)"]),
            ("(x - y) + 2*(~x & y)", vec!["(x ^ y)"]),
            ("~x + (2*x | 2)", vec!["(x ^ 1)"]),
            ("(x & y) | ~(x | y)", vec!["(x ^ ~y)"]),
            ("((x ^ z) & (y ^ ~z)) | ((x ^ ~z) & (y ^ z))", vec!["(x ^ y)"]),
            ("((x ^ z) & (y ^ z)) | ((x ^ ~z) & (y ^ ~z))", vec!["(~x ^ y)"]),
            ("(x + y) - 2*(x | (y - 1))", vec!["((x ^ -y) + 2)"]),
        ];
        let mut c = 0;
        for (case, expect) in test_pairs {
            if case.is_empty() {
                continue;
            }
            c += 1;
            if c < 0 {
                continue;
            }
            let egg_expr = infix_to_egglog(case, true);
            let result = simplify(&egg_expr, &cli);
            let r = if result.is_ok() {
                result.unwrap()
            } else {
                result.unwrap_err().to_string()
            };
            println!("#{} {}", c, case);
            assert!(
                expect.contains(&r.as_str()),
                "{} {}\n{} != {:?} \n{}",
                case,
                egg_expr,
                r,
                expect,
                make_egg(&cli.num_type)
            );
        }
    }
}
