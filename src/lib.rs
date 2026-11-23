pub mod dag;
pub mod eval;
pub mod expr_convert;
pub mod linear_mba;
mod poly_mba;
mod lowbits;
mod tfunc;
pub mod sched;

use crate::expr_convert::{egglog_to_infix, infix_to_egglog};
use clap::Parser;
use egglog::ast::Span;
use egglog::Error::ParseError;
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
pub fn make_egg(num_type: &str) -> String {
    let datatype = format!(
        r#"
(datatype Expr
    ; Constants only break ties between forms with the same number of other nodes.
    (Num i64 :cost 1)
    (Add Expr Expr :cost 10)
    (Sub Expr Expr :cost 10)
    (Mul Expr Expr :cost 10)
    (Div Expr Expr :cost 10)
    (Mod Expr Expr :cost 10)
    (And Expr Expr :cost 10)
    (Or Expr Expr :cost 10)
    (Xor Expr Expr :cost 10)
    (Shr Expr Expr :cost 10)
    (Shl Expr Expr :cost 10)
    (Mulhi Expr Expr :cost 10)
    (Not Expr :cost 10)
    (Neg Expr :cost 10)
    (Var String :cost 10)
)
(ruleset default-ruleset)
(ruleset constant-folding)
(ruleset identity-zero-element)
(ruleset canonicalization)
(ruleset simplify)
(rewrite (Add (Num a) (Num b))   (Num (wrapping-add-{0} a b)) :ruleset constant-folding)
(rewrite (Sub (Num a) (Num b))   (Num (wrapping-sub-{0} a b)) :ruleset constant-folding)
(rewrite (Mul (Num a) (Num b))   (Num (wrapping-mul-{0} a b)) :ruleset constant-folding)
(rewrite (Div (Num a) (Num b))   (Num (wrapping-div-{0} a b)) :when ((is-nonzero-{0} b)) :ruleset constant-folding)
(rewrite (And (Num a) (Num b))   (Num (wrapping-and-{0} a b)) :ruleset constant-folding)
(rewrite (Or (Num a) (Num b))   (Num (wrapping-or-{0} a b)) :ruleset constant-folding)
(rewrite (Xor (Num a) (Num b))   (Num (wrapping-xor-{0} a b)) :ruleset constant-folding)
(rewrite (Shl (Num a) (Num b))   (Num (wrapping-shl-{0} a b)) :ruleset constant-folding)
(rewrite (Shr (Num a) (Num b))   (Num (wrapping-shr-{0} a b)) :ruleset constant-folding)
(rewrite (Mod (Num a) (Num b))   (Num (wrapping-mod-{0} a b)) :when ((is-nonzero-{0} b)) :ruleset constant-folding)
(rewrite (Not (Num a))   (Num (wrapping-not-{0} a)) :ruleset constant-folding)
(rewrite (Neg (Num a))   (Num (wrapping-neg-{0} a)) :ruleset constant-folding)
(rewrite (Num a)   (Num (sext-{0} a)) :ruleset constant-folding)
(rewrite (Mulhi (Num a) (Num b))   (Num (mulh-{0} a b)) :ruleset constant-folding)
(rewrite (Shl x (Num k)) (Mul x (Num (pow2 k))) :when ((is-shl-in-{0} k)) :ruleset canonicalization)
(rewrite (Add (And x (Num a)) (And x (Num b))) x :when ((is-bit-not-eq-{0} a b)) :ruleset simplify)
(rewrite (Or (And x (Num a)) (And x (Num b))) x :when ((is-bit-not-eq-{0} a b)) :ruleset simplify)
(rewrite (Xor (And x (Num a)) (And x (Num b))) x :when ((is-bit-not-eq-{0} a b)) :ruleset simplify)
(relation non-zero (Expr))
(ruleset analysis)
(rule ((= e (Num c)) (is-nonzero-{0} c)) ((non-zero e)) :ruleset analysis)
(rule ((= e (Or a b)) (non-zero a)) ((non-zero e)) :ruleset analysis)
(rule ((= e (Or a b)) (non-zero b)) ((non-zero e)) :ruleset analysis)
(rule ((= e (Neg a)) (non-zero a)) ((non-zero e)) :ruleset analysis)
(rule ((= e (Mul a (Num c))) (non-zero a) (is-odd c)) ((non-zero e)) :ruleset analysis)
(rule ((= e (Mul (Num c) a)) (non-zero a) (is-odd c)) ((non-zero e)) :ruleset analysis)
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
    // NOTE: no `a*(1/a)=>1` / `a/b<=>a*(1/b)` here: integer division truncates,
    // so 1/b folds to 0 for |b|>1 and would merge a/b with 0 in the e-graph.
    // Division/mod rules with a non-constant divisor must prove the divisor
    // non-zero (via the `non-zero` analysis), or two rules could assign different
    // values to a 0/0 node and merge distinct constants (0==1).
    // NOTE: `a*b/b => a` is UNSOUND under wrapping arithmetic: if `a*b` overflows
    // the type, truncating division does not recover `a` (e.g. u8 a=64,b=4:
    // (64*4 mod 256)/4 = 0 != 64). No guard on `b` alone can rule this out
    // (overflow depends on `a`), so the rule is omitted entirely.
    egg.push_str(&rewrite!("a/a"=>"1";"identity-zero-element :when ((non-zero a))"));
    egg.push_str(&rewrite!("a%a"=>"0";"identity-zero-element :when ((non-zero a))"));
    egg.push_str(&rewrite!("a%1"=>"0";"identity-zero-element"));
    // HD ch. 9: fundamental division identity x = (x/y)*y + x%y
    egg.push_str(&rewrite!("(x/y)*y+x%y"=>"x";"identity-zero-element"));
    egg.push_str(&rewrite!("x-(x/y)*y"=>"x%y";"identity-zero-element"));
    // `a/-1 => -a` holds only for signed types (there -1 is the true divisor,
    // and INT_MIN/-1 wraps to INT_MIN = -INT_MIN consistently). For unsigned
    // types -1 is the max value, and a/MAX = (a==MAX ? 1 : 0) != -a.
    if is_signed(num_type) {
        egg.push_str(&rewrite!("a/-1"=>"-a";"identity-zero-element"));
    }
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
    egg.push_str(&rewrite!("0>>a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("0<<a"=>"0";"identity-zero-element"));
    egg.push_str(&rewrite!("~~a"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("-~a"=>"a+1";"identity-zero-element"));
    egg.push_str(&rewrite!("~-a"=>"a-1";"identity-zero-element"));
    egg.push_str(&rewrite!("a&(a|b)"=>"a";"identity-zero-element"));
    egg.push_str(&rewrite!("a|(a&b)"=>"a";"identity-zero-element"));

    egg.push_str(&rewrite!("a-b"<=>"a+-b";"canonicalization"));
    egg.push_str(&rewrite!("~a"<=>"-a-1";"canonicalization"));
    egg.push_str(&rewrite!("-a"<=>"a*-1";"canonicalization"));
    egg.push_str(&rewrite!("~(x*y)"<=>"((~x*y)+(y-1))";"canonicalization"));
    // HD 2nd ed., extended De Morgan: ~(x+y) = ~x-y, ~(x-y) = ~x+y
    egg.push_str(&rewrite!("~x-y"=>"~(x+y)";"canonicalization"));
    egg.push_str(&rewrite!("~x+y"=>"~(x-y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x&y)"<=>"(~x|~y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x^y)"<=>"(x^~y)";"canonicalization"));
    egg.push_str(&rewrite!("~(x|y)"<=>"(~x&~y)";"canonicalization"));
    egg.push_str(&rewrite!("x|y"<=>"(x&~y)+y";"canonicalization"));
    egg.push_str(&rewrite!("x|y"<=>"(x+y)-(x&y)";"canonicalization"));
    egg.push_str(&rewrite!("x|y"<=>"(x^y)+(x&y)";"canonicalization"));
    egg.push_str(&rewrite!("-(x+y)"<=>"-x-y";"canonicalization"));
    egg.push_str(&rewrite!("-(x-y)"<=>"y-x";"canonicalization"));
    egg.push_str(&rewrite!("-(x*y)"<=>"-x*y";"canonicalization"));
    egg.push_str(&rewrite!("(Num x)*-y"<=>"(- (Num x))*y";"canonicalization"));
    // Folded negative factors never match the rule above; this lets `a + -c*b` become `a - c*b`.
    egg.push_str(&format!("(rewrite (Mul (Num c) a) (Neg (Mul (Num (wrapping-neg-{num_type} c)) a)) :when ((is-neg-in c {})) :ruleset canonicalization)\n", width_of(num_type)));
    egg.push_str(&rewrite!("(Num a)*x+(Num a)"=>"(Num a)*(x+1)";"canonicalization"));
    egg.push_str(&rewrite!("(Num a)*x-(Num a)"=>"(Num a)*(x-1)";"canonicalization"));
    egg.push_str(&rewrite!("((Num a)*x)&(Num a)"<=>"(Num a)*(x&1)";format!("canonicalization :when ((is-2-pow-n-{} a))",num_type)));
    egg.push_str(&rewrite!("(a+b)*(a-b)"=>"a*a-b*b";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a+b)"=>"a*a+2*a*b+b*b";"canonicalization"));
    egg.push_str(&rewrite!("((x+y)*z)"<=>"(x*z+y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x-y)*z)"<=>"(x*z-y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)+y)"=>"((x+1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)-y)"=>"((x-1)*y)";"canonicalization"));
    // Combining repeated shifts is only sound for CONSTANT amounts in [1,width-1]:
    // then the folded sum b+c stays in [2,2*width-2] (no wraparound in the type),
    // and an over-shift sum >= width saturates correctly on both sides. With a
    // variable amount, or an amount that wraps (e.g. u8 b=255,c=1 -> b+c=0), the
    // old unguarded rule was unsound: (a>>255)>>1 = 0 but a>>((255+1) mod 256) = a.
    egg.push_str(&rewrite!("a>>(Num b)>>(Num c)"=>"a>>((Num b)+(Num c))";format!("canonicalization :when ((is-shl-in-{0} b) (is-shl-in-{0} c))",num_type)));
    egg.push_str(&rewrite!("a<<(Num b)<<(Num c)"=>"a<<((Num b)+(Num c))";format!("canonicalization :when ((is-shl-in-{0} b) (is-shl-in-{0} c))",num_type)));
    egg.push_str(&rewrite!("(a|b)&(a|c)"=>"a|(b&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b|c)"<=>"(a&b)|(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b^c)"<=>"(a&b)^(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("(x>>z)&(y>>z)"=>"(x&y)>>z";"canonicalization"));
    // Batch D: shift distributes over every bitwise op and over +/- (a shift is a
    // position-uniform bit map whose fill bits — 0 for shl/logical-shr, sign for
    // arith-shr — combine consistently). Sound for variable amounts and both
    // shift kinds; verified at 8-bit incl. over-shift. Collapsing direction.
    egg.push_str(&rewrite!("(x>>z)|(y>>z)"=>"(x|y)>>z";"canonicalization"));
    egg.push_str(&rewrite!("(x>>z)^(y>>z)"=>"(x^y)>>z";"canonicalization"));
    egg.push_str(&rewrite!("(x<<z)&(y<<z)"=>"(x&y)<<z";"canonicalization"));
    egg.push_str(&rewrite!("(x<<z)|(y<<z)"=>"(x|y)<<z";"canonicalization"));
    egg.push_str(&rewrite!("(x<<z)^(y<<z)"=>"(x^y)<<z";"canonicalization"));
    egg.push_str(&rewrite!("(x<<z)+(y<<z)"=>"(x+y)<<z";"canonicalization"));
    egg.push_str(&rewrite!("(x<<z)-(y<<z)"=>"(x-y)<<z";"canonicalization"));
    egg.push_str(&rewrite!("2*x"<=>"x+x";"canonicalization"));
    // Unsigned only: signed division/remainder by 2^k round toward zero,
    // which shifts and masks do not.
    if ["u64", "u32", "u16", "u8"].contains(&num_type) {
        egg.push_str(&format!(
            "(rewrite (Div x (Num c)) (Shr x (Num (ilog2 c))) :when ((is-2-pow-n-{0} c)) :ruleset canonicalization)\n",
            num_type
        ));
        egg.push_str(&format!(
            "(rewrite (Mod x (Num c)) (And x (Num (wrapping-sub-{0} c 1))) :when ((is-2-pow-n-{0} c)) :ruleset canonicalization)\n",
            num_type
        ));
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

    egg.push_str(&rewrite!("(x^y)-2*(~x&y)"=>"x-y";"simplify"));
    egg.push_str(&rewrite!("2*(x&~y)-(x^y)"=>"x-y";"simplify"));
    egg.push_str(&rewrite!("(x&~y)-(~x&y)"=>"x-y";"simplify"));
    egg.push_str(&rewrite!("2*(x|y)+(x^~y)"=>"(x+y)-1";"simplify"));
    egg.push_str(&rewrite!("(x|~y)+y"=>"(x&y)-1";"simplify"));
    egg.push_str(&rewrite!("(x+y)+~(x&y)"=>"(x|y)-1";"simplify"));
    egg.push_str(&rewrite!("(x^y)+2*(x&y)"=>"x+y";"simplify"));
    egg.push_str(&rewrite!("((x& 0xff) ^ (Num c1)) + 2*(x & (Num c2))" => "(x & 0xff) + (Num c1)";"simplify :when ((= (& c1 255) c2))"));
    egg.push_str(&rewrite!("(x ^ (Num c1)) + 2*(x | (Num c2))" => "x + (Num c2) - 1";format!("simplify :when ((is-bit-not-eq-{} c1 c2))",num_type)));
    egg.push_str(&rewrite!("(x-y)-2*(x|~y)"=>"(x^y) + 2";"simplify"));
    egg.push_str(&rewrite!("(x|y)*(x&y)+(x&~y)*(y&~x)"=>"x*y";"simplify"));
    egg.push_str(&rewrite!("(x+y)-(x|y)"=>"x&y";"simplify"));
    egg.push_str(&rewrite!("(y&~x)-y"=>"-(y&x)";"simplify"));
    egg.push_str(&rewrite!("(x|y)-y"=>"x&~y";"simplify"));
    egg.push_str(&rewrite!("x^(x&y)"=>"x&~y";"simplify"));
    egg.push_str(&rewrite!("(x|y)^y"=>"x&~y";"simplify"));
    egg.push_str(&rewrite!("(x*x)&3"=>"x&1";"simplify"));
    // x & -x is x's lowest set bit L; -L sets every bit from L up, and x has none below L.
    egg.push_str(&rewrite!("x&-(x&-x)"=>"x";"simplify"));
    // x & 2x keeps the bits i with x_i = x_(i-1) = 1, all above L, where -x is ~x
    // and x - 1 is x; 2x has no bit L.
    egg.push_str(&rewrite!("(x&(2*x))&-x"=>"0";"simplify"));
    egg.push_str(&rewrite!("-x&~(x&(2*x))"=>"-x";"simplify"));
    egg.push_str(&rewrite!("x&~(-x&(-2*x))"=>"x";"simplify"));
    egg.push_str(&rewrite!("x&~(-x&(2*x))"=>"x";"simplify"));
    egg.push_str(&rewrite!("(2*x)&(x&-x)"=>"0";"simplify"));
    egg.push_str(&rewrite!("(x+-1)|(x&(2*x))"=>"x+-1";"simplify"));
    // -2x has no bits up to L, where x - 1 differs from x.
    egg.push_str(&rewrite!("((-2*x)&(x+-1))|x"=>"x";"simplify"));
    // -(y | -a) | y = a for y ⊆ a.
    egg.push_str(&rewrite!("-(y|-(x|y))|y"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("~x^~y"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("~x^((Num c)-y)"=>"x^(y+~(Num c))";"simplify"));
    egg.push_str(&rewrite!("(x|y)^(~x|~y)"=>"~(x^y)";"simplify"));
    egg.push_str(&rewrite!("(x&y)|~(x|y)"=>"~(x^y)";"simplify"));
    egg.push_str(&rewrite!("(x&y)|(~x&~y)"=>"~(x^y)";"simplify"));
    egg.push_str(&rewrite!("((x|y)-(x&y))"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x&~y)-(x&y)"=>"(x^y)-y";"simplify"));
    egg.push_str(&rewrite!("(x|y)+(x&~y)"=>"(x^y)+x";"simplify"));
    egg.push_str(&rewrite!("(x&y)+(x&~y)"=>"x";"simplify"));
    egg.push_str(&rewrite!("(x&y)^(x&~y)"=>"x";"simplify"));
    egg.push_str(&rewrite!("(x&y)^(x|y)"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x&y)|(x^y)"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("(x&y)^(x^y)"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("(x^y)|y"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("~(x-1)"=>"-x";"simplify"));
    egg.push_str(&rewrite!("~x+1"=>"-x";"simplify"));
    egg.push_str(&rewrite!("(x+y)-2*(x&y)"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("2*(x|y)-(x+y)"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x|y)-(x^y)"=>"x&y";"simplify"));
    egg.push_str(&rewrite!("(~x|y)-~x"=>"x&y";"simplify"));
    egg.push_str(&rewrite!("(x|y)+(x&y)"=>"x+y";"simplify"));
    egg.push_str(&rewrite!("2*(x|y)-(x^y)"=>"x+y";"simplify"));
    egg.push_str(&rewrite!("(x&y)-(x+y)"=>"-(x|y)";"simplify"));
    egg.push_str(&rewrite!("(x&y)-(x|y)"=>"-(x^y)";"simplify"));
    egg.push_str(&rewrite!("(x^y)-2*(x|y)"=>"-(x+y)";"simplify"));
    egg.push_str(&rewrite!("(x+y)-2*(x|y)"=>"-(x^y)";"simplify"));
    egg.push_str(&rewrite!("x-(x&y)"=>"x&~y";"simplify"));
    egg.push_str(&rewrite!("x&(x^y)"=>"x&~y";"simplify"));

    // Batch A: bitwise lattice fills (from LLVM InstCombine / GCC match.pd /
    // haroldbot). All pure bit identities, sound under wrapping at every width;
    // brute-force verified at 8-bit. Directed toward the smaller form.
    egg.push_str(&rewrite!("(x&~y)|(~x&y)"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x|y)&~(x&y)"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("x+(~x&y)"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("(x|y)-(~x&y)"=>"x";"simplify"));
    egg.push_str(&rewrite!("(x|y)-x"=>"~x&y";"simplify"));
    egg.push_str(&rewrite!("(x+y)-(x^y)"=>"2*(x&y)";"simplify"));
    egg.push_str(&rewrite!("(x&y)+~y"=>"x|~y";"simplify"));
    egg.push_str(&rewrite!("a&~(a^b)"=>"a&b";"simplify"));
    egg.push_str(&rewrite!("x|(x^y)"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("x^(x|y)"=>"~x&y";"simplify"));
    egg.push_str(&rewrite!("a^(~a&b)"=>"a|b";"simplify"));
    egg.push_str(&rewrite!("x+~x"=>"-1";"simplify"));
    egg.push_str(&rewrite!("(x+y)-(x&y)"=>"x|y";"simplify"));
    egg.push_str(&rewrite!("(x^y)-(x|y)"=>"-(x&y)";"simplify"));
    egg.push_str(&rewrite!("~x-~y"=>"y-x";"simplify"));
    egg.push_str(&rewrite!("x&~(x&y)"=>"x&~y";"simplify"));
    egg.push_str(&rewrite!("x|~(x|y)"=>"x|~y";"simplify"));
    egg.push_str(&rewrite!("x|~(x^y)"=>"x|~y";"simplify"));
    egg.push_str(&rewrite!("(x|y)&~(x^y)"=>"x&y";"simplify"));
    egg.push_str(&rewrite!("~x|(x^y)"=>"~(x&y)";"simplify"));
    egg.push_str(&rewrite!("(x^y)|~(x|y)"=>"~(x&y)";"simplify"));
    egg.push_str(&rewrite!("(x&y)^y"=>"~x&y";"simplify"));

    // Batch B: three-variable identities. `(x&~m)|(y&m)` is the bit-select /
    // masked-merge idiom; the full-adder pair recognizes 3-input add obfuscation
    // (generalizes the existing 2-input `(x^y)+2*(x&y)=x+y`). Verified at 8-bit.
    egg.push_str(&rewrite!("(a|b)^(a|c)"=>"(b^c)&~a";"simplify"));
    egg.push_str(&rewrite!("(a^b)^(a|c)"=>"(~a&c)^b";"simplify"));
    egg.push_str(&rewrite!("(x&~m)|(y&m)"=>"((x^y)&m)^x";"simplify"));
    egg.push_str(&rewrite!("(x^y^z)+2*((x&y)|(x&z)|(y&z))"=>"x+y+z";"simplify"));
    egg.push_str(&rewrite!("(x^y^z)+2*((x&y)|((x^y)&z))"=>"x+y+z";"simplify"));
    egg.push_str(&rewrite!("(x&y)|(x&z)|(y&z)"=>"(x&y)|((x^y)&z)";"simplify"));

    // Batch C: annihilation / lowest-set-bit identities (Hacker's Delight, GCC).
    // `a-1` and `-a` are bit-complementary around the lowest set bit, so these
    // collapse opaque predicates. Verified at 8-bit, all widths, incl a=0.
    egg.push_str(&rewrite!("(a-1)&-a"=>"0";"simplify"));
    egg.push_str(&rewrite!("(a-1)|-a"=>"-1";"simplify"));
    egg.push_str(&rewrite!("(a-1)^-a"=>"-1";"simplify"));
    egg.push_str(&rewrite!("(a&-a)-1"=>"(a-1)&~a";"simplify"));

    // Batch E: constant-gated identities (need new guard primitives).
    // Sign-bit: adding the top bit never carries out, so it equals flipping it
    // (kills `x + 0x80..` <-> `x ^ 0x80..` obfuscation).
    egg.push_str(&rewrite!("x+(Num c)"=>"x^(Num c)";format!("simplify :when ((is-sign-bit-{0} c))",num_type)));
    // Disjoint constants: c1 & c2 == 0, so masked slices don't carry into each
    // other and `+` is `|`.
    egg.push_str(&rewrite!("(x&(Num c1))+(x&(Num c2))"=>"x&((Num c1)|(Num c2))";format!("simplify :when ((is-disjoint-{0} c1 c2))",num_type)));
    // Mersenne mask m = 2^k-1: low k bits of a result depend only on the low k
    // bits of the operands, so the inner masks can be dropped (generalizes the
    // existing `(x*x)&3 => x&1`). These deep triple-`m` patterns (and the `x*y`
    // the multiply variant introduces) are the most expensive rules in this set;
    // verified sound at 8-bit for all widths.
    egg.push_str(&rewrite!("((x&(Num m))+(y&(Num m)))&(Num m)"=>"(x+y)&(Num m)";format!("simplify :when ((is-mersenne-{0} m))",num_type)));
    egg.push_str(&rewrite!("((x&(Num m))-(y&(Num m)))&(Num m)"=>"(x-y)&(Num m)";format!("simplify :when ((is-mersenne-{0} m))",num_type)));
    egg.push_str(&rewrite!("((x&(Num m))*(y&(Num m)))&(Num m)"=>"(x*y)&(Num m)";format!("simplify :when ((is-mersenne-{0} m))",num_type)));
    egg.push_str(&rewrite!("(a&(Num c1))+(b&(Num c2))"=>"(a&(Num c1))|(b&(Num c2))";format!("simplify :when ((is-disjoint-{0} c1 c2))",num_type)));
    egg.push_str(&rewrite!("(a&(Num c1))^(b&(Num c2))"=>"(a&(Num c1))|(b&(Num c2))";format!("simplify :when ((is-disjoint-{0} c1 c2))",num_type)));

    egg.push_str(&rewrite!("(x*x)&1"=>"x&1";"simplify"));
    egg.push_str(&rewrite!("(x*x)&2"=>"0";"simplify"));
    egg.push_str(&rewrite!("(x*(x+1))&1"=>"0";"simplify"));
    egg.push_str(&rewrite!("(x*~x)&1"=>"0";"simplify"));

    egg.push_str(&rewrite!("(a>>(Num c))<<(Num c)"=>"a&(-1<<(Num c))";format!("simplify :when ((is-shl-in-{0} c))",num_type)));
    // Unsigned only: a signed `>>` would copy the sign bit back into the cleared high bits.
    if !is_signed(num_type) {
        egg.push_str(&rewrite!("(a<<(Num c))>>(Num c)"=>"a&(-1>>(Num c))";format!("simplify :when ((is-shl-in-{0} c))",num_type)));
    }
    // `a << c` is canonicalized to `a * 2^c`, so the shift rules also need the multiply form.
    let w = width_of(num_type);
    egg.push_str(&format!("(rewrite (Mul (Shr a (Num c)) (Num p)) (And a (Shl (Num -1) (Num c))) :when ((is-pow2-of p c {w})) :ruleset simplify)\n"));
    if !is_signed(num_type) {
        egg.push_str(&format!("(rewrite (Shr (Mul a (Num p)) (Num c)) (And a (Shr (Num -1) (Num c))) :when ((is-pow2-of p c {w})) :ruleset simplify)\n"));
    }
    egg.push_str(&format!("(rewrite (Shr (And a (Num m)) (Num c)) (Shr a (Num c)) :when ((covers-high m c {w})) :ruleset simplify)\n"));
    egg.push_str(&format!("(rewrite (Mul (And a (Num m)) (Num p)) (Mul a (Num p)) :when ((covers-low m p {w})) :ruleset simplify)\n"));
    // `below-pow2` skips `|K| < 16`: such `K` are mostly constants the rules made, and rewriting them grows the e-graph.
    egg.push_str(&format!("(rewrite (Add (Mul (Xor a (Num k)) (Num p)) (Num c)) (Xor (Mul a (Num p)) (Num (wrapping-add-{num_type} (wrapping-mul-{num_type} k p) c))) :when ((below-pow2 c p k {w})) :ruleset simplify)\n"));

    // HD ch. 10: recognize magic-number division and rewrite back to `n / d`.
    // The divisor d is recovered from (M, s) by the magic-div-* primitive, which
    // returns d only if (M, s) is exactly the magic pair for some d under this
    // width/signedness (else the rule does not fire). `Mulhi` is the high half of
    // the 2W-bit product (mulhs for signed types, mulhu for unsigned).
    let w1 = width_of(num_type) - 1;
    egg.push_str("(rewrite (Mulhi n (Num m)) (Mulhi (Num m) n) :ruleset canonicalization)\n");
    egg.push_str(&format!(
"(rewrite (Sub n (Mul (Div n (Num d)) (Num d))) (Mod n (Num d)) :ruleset simplify)
(rule ((= e (Add n (Mul (Div n (Num d)) (Num nd)))) (= nd (wrapping-neg-{num_type} d))) ((union e (Mod n (Num d)))) :ruleset simplify)
"));
    if is_signed(num_type) {
        // Compilers subtract the sign mask (0 or -1) instead of adding the sign bit.
        egg.push_str(&format!("(rewrite (Sub a (Shr n (Num {w1}))) (Add a (And (Shr n (Num {w1})) (Num 1))) :ruleset canonicalization)\n"));
        // Signed division by 2^k (HD 10-1): add (2^k-1) if n<0, then shift.
        egg.push_str(&format!(
"(rule ((= e (Shr (Add n (And (Shr n (Num {w1})) (Num mask))) (Num k))) (= dd (pow2div-{t} mask k))) ((union e (Div n (Num dd)))) :ruleset simplify)\n",
            t = num_type, w1 = w1
        ));
        // sign correction sb = (n >> (W-1)) & 1  (0 or 1)
        egg.push_str(&format!(
"(rule ((= e (Add (Mulhi (Num m) n) (And (Shr n (Num {w1})) (Num 1)))) (= dd (magic-div-{t} m 0))) ((union e (Div n (Num dd)))) :ruleset simplify)
(rule ((= e (Add (Shr (Mulhi (Num m) n) (Num s)) (And (Shr n (Num {w1})) (Num 1)))) (= dd (magic-div-{t} m s))) ((union e (Div n (Num dd)))) :ruleset simplify)
(rule ((= e (Add (Shr (Add (Mulhi (Num m) n) n) (Num s)) (And (Shr n (Num {w1})) (Num 1)))) (= dd (magic-div-add-{t} m s))) ((union e (Div n (Num dd)))) :ruleset simplify)
",
            t = num_type, w1 = w1
        ));
    } else {
        // Unsigned: no sign correction. Third rule is the large-multiplier "add"
        // variant (e.g. u32 d=7): compilers emit q=mulhu(M,n) then the
        // Granlund-Montgomery overflow-free form ((n-q)>>1 + q) >> (s-1) = n/d.
        // The two Mulhi occurrences share one e-class (same m, n bindings).
        egg.push_str(&format!(
"(rule ((= e (Mulhi (Num m) n)) (= dd (magicu-div-{t} m 0))) ((union e (Div n (Num dd)))) :ruleset simplify)
(rule ((= e (Shr (Mulhi (Num m) n) (Num s))) (= dd (magicu-div-{t} m s))) ((union e (Div n (Num dd)))) :ruleset simplify)
(rule ((= e (Shr (Add (Shr (Sub n (Mulhi (Num m) n)) (Num 1)) (Mulhi (Num m) n)) (Num s))) (= dd (magicu-div-add-{t} m s))) ((union e (Div n (Num dd)))) :ruleset simplify)
",
            t = num_type
        ));
    }

    egg.push_str(&known_bits(width_of(num_type), is_signed(num_type)));
    egg.push_str(TRAILING_ZEROS);
    egg
}

/// `(tz-ge e y)`: `e` has at least as many trailing zeros as `y`, tracked only for
/// the `y` of a `y | -y` (all ones from the lowest set bit of `y` up), so that
/// `e & (y | -y) = e`.
const TRAILING_ZEROS: &str = r#"
(relation low-base (Expr))
(relation tz-ge (Expr Expr))
(rule ((= m (Or y (Neg y)))) ((low-base y)) :ruleset analysis)
(rule ((low-base y)) ((tz-ge y y)) :ruleset analysis)
(rule ((= e (Mul a b)) (tz-ge a y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Mul a b)) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (And a b)) (tz-ge a y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (And a b)) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Shl a b)) (tz-ge a y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Neg a)) (tz-ge a y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Add a b)) (tz-ge a y) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Sub a b)) (tz-ge a y) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Or a b)) (tz-ge a y) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)
(rule ((= e (Xor a b)) (tz-ge a y) (tz-ge b y)) ((tz-ge e y)) :ruleset analysis)

(rule ((= r (And e (Or y (Neg y)))) (tz-ge e y)) ((union r e)) :ruleset simplify)
"#;

/// Known-zero-bits analysis: `(kz e)` is a mask of bits known to be 0 in `e`.
/// Only the low `w` bits are meaningful; the kz-* primitives and `all-ones`
/// ignore the rest.
fn known_bits(w: u32, signed: bool) -> String {
    let s = signed as i64;
    format!(
        r#"
(function kz (Expr) i64 :merge (| old new))
(rule ((= e (Num c))) ((set (kz e) (not-i64 c))) :ruleset analysis)
(rule ((= e (And a b)) (= z (kz a))) ((set (kz e) z)) :ruleset analysis)
(rule ((= e (And a b)) (= z (kz b))) ((set (kz e) z)) :ruleset analysis)
(rule ((= e (Or a b)) (= za (kz a)) (= zb (kz b))) ((set (kz e) (& za zb))) :ruleset analysis)
(rule ((= e (Xor a b)) (= za (kz a)) (= zb (kz b))) ((set (kz e) (& za zb))) :ruleset analysis)
(rule ((= e (Shl a (Num k))) (= v (kz-shl 0 k {w}))) ((set (kz e) v)) :ruleset analysis)
(rule ((= e (Shl a (Num k))) (= z (kz a)) (= v (kz-shl z k {w}))) ((set (kz e) v)) :ruleset analysis)
(rule ((= e (Shl a b)) (= z (kz a))) ((set (kz e) (kz-low z {w}))) :ruleset analysis)
(rule ((= e (Shr a (Num k))) (= v (kz-shr 0 k {w} {s}))) ((set (kz e) v)) :ruleset analysis)
(rule ((= e (Shr a (Num k))) (= z (kz a)) (= v (kz-shr z k {w} {s}))) ((set (kz e) v)) :ruleset analysis)
(rule ((= e (Mul a b)) (= z (kz a))) ((set (kz e) (kz-low z {w}))) :ruleset analysis)
(rule ((= e (Mul a b)) (= z (kz b))) ((set (kz e) (kz-low z {w}))) :ruleset analysis)
(rule ((= e (Mul a b)) (= za (kz a)) (= zb (kz b))) ((set (kz e) (kz-mul za zb {w}))) :ruleset analysis)
(rule ((= e (Add a b)) (= za (kz a)) (= zb (kz b))) ((set (kz e) (kz-add za zb {w}))) :ruleset analysis)
(rule ((= e (Sub a b)) (= za (kz a)) (= zb (kz b))) ((set (kz e) (kz-add za zb {w}))) :ruleset analysis)
(rule ((= e (Neg a)) (= z (kz a))) ((set (kz e) (kz-low z {w}))) :ruleset analysis)

(rule ((= z (kz e)) (all-ones z {w})) ((union e (Num 0))) :ruleset simplify)
(rule ((= e (And a (Num c))) (= z (kz a)) (all-ones (| z c) {w})) ((union e a)) :ruleset simplify)
"#
    )
}

fn lowmask(k: u32) -> i64 {
    if k >= 64 { -1 } else { ((1u64 << k) - 1) as i64 }
}

/// Known-zero mask of `a << k` given known-zero mask `z` of `a`; None unless 0 <= k < w.
pub fn kz_shl(z: i64, k: i64, w: i64) -> Option<i64> {
    (0..w).contains(&k).then(|| (z << k) | lowmask(k as u32))
}

/// Known-zero mask of `a >> k` (arithmetic if `signed`); None unless 0 <= k < w.
pub fn kz_shr(z: i64, k: i64, w: i64, signed: bool) -> Option<i64> {
    (0..w).contains(&k).then(|| {
        if signed {
            let sh = 64 - w;
            ((z << sh) >> sh) >> k
        } else {
            let m = lowmask(w as u32) as u64;
            (((z as u64 & m) >> k) | !(m >> k)) as i64
        }
    })
}

/// Trailing known zeros of `z`, as a mask (kept by `-a` and by `a * b`).
pub fn kz_low(z: i64, w: i64) -> i64 {
    lowmask(z.trailing_ones().min(w as u32))
}

/// Known-zero mask of `a + b` or `a - b`: the shorter run of trailing known zeros.
pub fn kz_add(za: i64, zb: i64, w: i64) -> i64 {
    lowmask(za.trailing_ones().min(zb.trailing_ones()).min(w as u32))
}

/// Known-zero mask of `a * b`: trailing known zeros add up.
pub fn kz_mul(za: i64, zb: i64, w: i64) -> i64 {
    lowmask((za.trailing_ones() + zb.trailing_ones()).min(w as u32))
}

fn width_mask(w: i64) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// `m` keeps every bit of `a` that survives `a * p` for the power of two `p`.
fn covers_low(m: i64, p: i64, w: i64) -> bool {
    let p = p as u64 & width_mask(w);
    let low = width_mask(w) >> p.trailing_zeros().min(63);
    p.is_power_of_two() && (m as u64) & low == low
}

fn width_of(t: &str) -> u32 {
    match t {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        _ => 64,
    }
}
fn is_signed(t: &str) -> bool {
    t.starts_with('i')
}

/// Sign-extend the low `w` bits of `v` to a full i128.
fn sextn(v: i128, w: u32) -> i128 {
    let sh = 128 - w;
    (v << sh) >> sh
}

/// Signed division by a known power of 2 (HD 10-1): the correction-mask `mask`
/// and shift `k` recognize `(n + ((n>>(W-1)) & mask)) >> k == n / 2^k`.
/// Returns the divisor 2^k iff mask == 2^k-1 and 1 <= k <= W-2 (k=W-1 excluded:
/// 2^(W-1) is not representable as a positive signed divisor).
pub fn pow2_div(mask: i64, k: i64, w: u32) -> Option<i64> {
    if k < 1 || k as u32 > w - 2 {
        return None;
    }
    let lowmask: u128 = (1u128 << w) - 1;
    let expected = (1u128 << k) - 1;
    if (mask as u64 as u128 & lowmask) != expected {
        return None;
    }
    Some(1i64 << k)
}

/// Signed magic pair for a positive divisor `d` (HD Figure 10-1, generalized to
/// width W). Returns (multiplier m with 0<m<2^W, shift s, add-correction flag).
pub fn magic_s(d: i64, w: u32) -> Option<(u128, u32, bool)> {
    let dv = d as i128;
    if dv < 2 || dv >= (1i128 << (w - 1)) {
        return None;
    }
    let ad = dv as u128;
    let two_wm1: u128 = 1u128 << (w - 1);
    let anc = two_wm1 - 1 - (two_wm1 % ad);
    let mut p = w - 1;
    let mut q1 = two_wm1 / anc;
    let mut r1 = two_wm1 - q1 * anc;
    let mut q2 = two_wm1 / ad;
    let mut r2 = two_wm1 - q2 * ad;
    loop {
        p += 1;
        q1 *= 2;
        r1 *= 2;
        if r1 >= anc {
            q1 += 1;
            r1 -= anc;
        }
        q2 *= 2;
        r2 *= 2;
        if r2 >= ad {
            q2 += 1;
            r2 -= ad;
        }
        let delta = ad - r2;
        if !(q1 < delta || (q1 == delta && r1 == 0)) {
            break;
        }
        if p > 2 * w + 4 {
            return None;
        }
    }
    let m = q2 + 1;
    Some((m, p - w, m >= two_wm1))
}

/// Unsigned magic pair for divisor `d` (HD Figure 10-2, generalized to width W).
/// Returns (true multiplier m with 0<m<2^(W+1), shift s, add flag).
pub fn magic_u(d: i64, w: u32) -> Option<(u128, u32, bool)> {
    let mask: u128 = (1u128 << w) - 1;
    let dv = (d as u64 as u128) & mask;
    if dv < 2 {
        return None;
    }
    let two_w: u128 = 1u128 << w;
    let two_wm1: u128 = 1u128 << (w - 1);
    let nc = (two_w - (two_w % dv)) - 1;
    let mut a = false;
    let mut p = w - 1;
    let mut q1 = two_wm1 / nc;
    let mut r1 = two_wm1 - q1 * nc;
    let mut q2 = (two_wm1 - 1) / dv;
    let mut r2 = (two_wm1 - 1) - q2 * dv;
    loop {
        p += 1;
        if r1 >= nc - r1 {
            q1 = 2 * q1 + 1;
            r1 = 2 * r1 - nc;
        } else {
            q1 = 2 * q1;
            r1 = 2 * r1;
        }
        if r2 + 1 >= dv - r2 {
            if q2 >= two_wm1 - 1 {
                a = true;
            }
            q2 = 2 * q2 + 1;
            r2 = 2 * r2 + 1 - dv;
        } else {
            if q2 >= two_wm1 {
                a = true;
            }
            q2 = 2 * q2;
            r2 = 2 * r2 + 1;
        }
        let delta = dv - 1 - r2;
        if !(p < 2 * w && (q1 < delta || (q1 == delta && r1 == 0))) {
            break;
        }
    }
    Some((q2 + 1, p - w, a))
}

/// Recover the signed divisor from a bound (M, s), verifying it is the exact
/// magic pair with the given add-flag. Returns the divisor, or None.
pub fn magic_div_s(m_bits: i64, s: i64, w: u32, want_add: bool) -> Option<i64> {
    if s < 0 || s > w as i64 {
        return None;
    }
    let mask: u128 = (1u128 << w) - 1;
    let m = (m_bits as u64 as u128) & mask;
    if m == 0 {
        return None;
    }
    let p = s as u32 + w;
    let d0 = 1u128.checked_shl(p).map_or(u128::MAX / m, |x| x / m);
    for cand in [d0.saturating_sub(2), d0.saturating_sub(1), d0, d0 + 1, d0 + 2] {
        if cand < 2 || cand >= (1u128 << (w - 1)) {
            continue;
        }
        if magic_s(cand as i64, w) == Some((m, s as u32, want_add)) {
            return Some(cand as i64);
        }
    }
    None
}

/// Recover the unsigned divisor from a bound (M, s); returns it sign-extended
/// to i64 (matching how constants are stored), or None.
pub fn magic_div_u(m_bits: i64, s: i64, w: u32, want_add: bool) -> Option<i64> {
    if s < 0 || s > w as i64 {
        return None;
    }
    let mask: u128 = (1u128 << w) - 1;
    let mlow = (m_bits as u64 as u128) & mask;
    let m_full = if want_add { (1u128 << w) + mlow } else { mlow };
    if m_full == 0 {
        return None;
    }
    let p = s as u32 + w;
    let d0 = 1u128.checked_shl(p).map_or(u128::MAX / m_full, |x| x / m_full);
    for cand in [d0.saturating_sub(2), d0.saturating_sub(1), d0, d0 + 1, d0 + 2] {
        if cand < 2 || cand > mask {
            continue;
        }
        if magic_u(cand as i64, w) == Some((m_full, s as u32, want_add)) {
            return Some(sextn(cand as i128, w) as i64);
        }
    }
    None
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

    add_primitive!(eg, "wrapping-shr-i64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { a >> 63 } else { a >> (b as u64) } } );
    add_primitive!(eg, "wrapping-shr-u64" = |a: i64, b: i64| -> i64 { if b as u64 > 63 { 0 } else{((a as u64) >> (b as u64)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { ((a as i32) >> 31) as i64 } else{((a as i32) >> (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u32" = |a: i64, b: i64| -> i64 { if b as u32 > 31 { 0 } else{((a as u32) >> (b as u32)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { ((a as i16) >> 15) as i64 } else{((a as i16) >> (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u16" = |a: i64, b: i64| -> i64 { if b as u16 > 15 { 0 } else{((a as u16) >> (b as u16)) as i64} } );
    add_primitive!(eg, "wrapping-shr-i8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { ((a as i8) >> 7) as i64 } else{((a as i8) >> (b as u8)) as i64} } );
    add_primitive!(eg, "wrapping-shr-u8" = |a: i64, b: i64| -> i64 { if b as u8 > 7 { 0 } else{((a as u8) >> (b as u8)) as i64} } );

    add_primitive!(eg, "wrapping-mod-i64" = |a: i64, b: i64| -> i64 { a.wrapping_rem(b) } );
    add_primitive!(eg, "wrapping-mod-u64" = |a: i64, b: i64| -> i64 { ((a as u64) % (b as u64)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i32" = |a: i64, b: i64| -> i64 { ((a as i32).wrapping_rem(b as i32)) as i64 } );
    add_primitive!(eg, "wrapping-mod-u32" = |a: i64, b: i64| -> i64 { ((a as u32) % (b as u32)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i16" = |a: i64, b: i64| -> i64 { ((a as i16).wrapping_rem(b as i16)) as i64 } );
    add_primitive!(eg, "wrapping-mod-u16" = |a: i64, b: i64| -> i64 { ((a as u16) % (b as u16)) as i64 } );
    add_primitive!(eg, "wrapping-mod-i8" = |a: i64, b: i64| -> i64 { ((a as i8).wrapping_rem(b as i8)) as i64 } );
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

    add_primitive!( eg, "is-bit-not-eq-i64" = |a: i64, b: i64| -?> () { ((a as u64) ^ (b as u64) == u64::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u64" = |a: i64, b: i64| -?> () { ((a as u64) ^ (b as u64) == u64::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i32" = |a: i64, b: i64| -?> () { ((a as u32) ^ (b as u32) == u32::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u32" = |a: i64, b: i64| -?> () { ((a as u32) ^ (b as u32) == u32::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i16" = |a: i64, b: i64| -?> () { ((a as u16) ^ (b as u16) == u16::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u16" = |a: i64, b: i64| -?> () { ((a as u16) ^ (b as u16) == u16::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i8" = |a: i64, b: i64| -?> () { ((a as u8) ^ (b as u8) == u8::MAX).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u8" = |a: i64, b: i64| -?> () { ((a as u8) ^ (b as u8) == u8::MAX).then_some(()) });

    add_primitive!(eg, "sext-i64" = |a: i64| -> i64 { a } );
    add_primitive!(eg, "sext-u64" = |a: i64| -> i64 { a } );
    add_primitive!(eg, "sext-i32" = |a: i64| -> i64 { (a as i32) as i64 } );
    add_primitive!(eg, "sext-u32" = |a: i64| -> i64 { (a as i32) as i64 } );
    add_primitive!(eg, "sext-i16" = |a: i64| -> i64 { (a as i16) as i64 } );
    add_primitive!(eg, "sext-u16" = |a: i64| -> i64 { (a as i16) as i64 } );
    add_primitive!(eg, "sext-i8" = |a: i64| -> i64 { (a as i8) as i64 } );
    add_primitive!(eg, "sext-u8" = |a: i64| -> i64 { (a as i8) as i64 } );


    add_primitive!( eg, "is-odd" = |a: i64| -?> () { ((a & 1) == 1).then_some(()) });

    add_primitive!(eg, "mulh-i64" = |a: i64, b: i64| -> i64 { (((a as i128) * (b as i128)) >> 64) as i64 } );
    add_primitive!(eg, "mulh-u64" = |a: i64, b: i64| -> i64 { (((a as u64 as u128) * (b as u64 as u128)) >> 64) as i64 } );
    add_primitive!(eg, "mulh-i32" = |a: i64, b: i64| -> i64 { (((a as i32 as i128) * (b as i32 as i128)) >> 32) as i64 } );
    add_primitive!(eg, "mulh-u32" = |a: i64, b: i64| -> i64 { (((a as u32 as u128) * (b as u32 as u128)) >> 32) as i64 } );
    add_primitive!(eg, "mulh-i16" = |a: i64, b: i64| -> i64 { (((a as i16 as i128) * (b as i16 as i128)) >> 16) as i64 } );
    add_primitive!(eg, "mulh-u16" = |a: i64, b: i64| -> i64 { (((a as u16 as u128) * (b as u16 as u128)) >> 16) as i64 } );
    add_primitive!(eg, "mulh-i8" = |a: i64, b: i64| -> i64 { (((a as i8 as i128) * (b as i8 as i128)) >> 8) as i64 } );
    add_primitive!(eg, "mulh-u8" = |a: i64, b: i64| -> i64 { (((a as u8 as u128) * (b as u8 as u128)) >> 8) as i64 } );

    add_primitive!(eg, "magic-div-i64" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 64, false) });
    add_primitive!(eg, "magic-div-i32" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 32, false) });
    add_primitive!(eg, "magic-div-i16" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 16, false) });
    add_primitive!(eg, "magic-div-i8" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 8, false) });
    add_primitive!(eg, "pow2div-i64" = |mask: i64, k: i64| -?> i64 { pow2_div(mask, k, 64) });
    add_primitive!(eg, "pow2div-i32" = |mask: i64, k: i64| -?> i64 { pow2_div(mask, k, 32) });
    add_primitive!(eg, "pow2div-i16" = |mask: i64, k: i64| -?> i64 { pow2_div(mask, k, 16) });
    add_primitive!(eg, "pow2div-i8" = |mask: i64, k: i64| -?> i64 { pow2_div(mask, k, 8) });
    add_primitive!(eg, "magic-div-add-i64" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 64, true) });
    add_primitive!(eg, "magic-div-add-i32" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 32, true) });
    add_primitive!(eg, "magic-div-add-i16" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 16, true) });
    add_primitive!(eg, "magic-div-add-i8" = |m: i64, s: i64| -?> i64 { magic_div_s(m, s, 8, true) });
    add_primitive!(eg, "magicu-div-u64" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s, 64, false) });
    add_primitive!(eg, "magicu-div-u32" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s, 32, false) });
    add_primitive!(eg, "magicu-div-u16" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s, 16, false) });
    add_primitive!(eg, "magicu-div-u8" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s, 8, false) });
    // The add-variant's outer shift is (real magic shift - 1); recover s = outer + 1.
    add_primitive!(eg, "magicu-div-add-u64" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s.saturating_add(1), 64, true) });
    add_primitive!(eg, "magicu-div-add-u32" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s.saturating_add(1), 32, true) });
    add_primitive!(eg, "magicu-div-add-u16" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s.saturating_add(1), 16, true) });
    add_primitive!(eg, "magicu-div-add-u8" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s.saturating_add(1), 8, true) });

    add_primitive!(eg, "ilog2" = |a: i64| -> i64 { (a as u64).trailing_zeros() as i64 } );
    add_primitive!(eg, "pow2" = |a: i64| -> i64 { 1i64.wrapping_shl(a as u32) } );
    add_primitive!(eg, "is-neg-in" = |c: i64, w: i64| -?> () { (((c as u64) & width_mask(w)) > (width_mask(w) >> 1) + 1).then_some(()) });
    add_primitive!(eg, "is-pow2-of" = |p: i64, c: i64, w: i64| -?> () { (c >= 1 && c < w && (p as u64) & width_mask(w) == 1u64 << c).then_some(()) });
    add_primitive!(eg, "covers-high" = |m: i64, c: i64, w: i64| -?> () { (c >= 1 && c < w && ((m as u64) | ((1u64 << c) - 1)) & width_mask(w) == width_mask(w)).then_some(()) });
    add_primitive!(eg, "below-pow2" = |c: i64, p: i64, k: i64, w: i64| -?> () { {let m = width_mask(w); let p = (p as u64) & m; (p > 1 && p & (p - 1) == 0 && (c as u64) & m < p && (c as u64) & m != 0 && { let s = 64 - w as u32; let k = (((k as u64) << s) as i64) >> s; !(-16..16).contains(&k) }).then_some(())} });
    add_primitive!(eg, "covers-low" = |m: i64, p: i64, w: i64| -?> () { covers_low(m, p, w).then_some(()) });
    add_primitive!( eg, "is-shl-in-i64" = |a: i64| -?> () { (a >= 1 && a <= 63).then_some(()) });
    add_primitive!( eg, "is-shl-in-u64" = |a: i64| -?> () { (a >= 1 && a <= 63).then_some(()) });
    add_primitive!( eg, "is-shl-in-i32" = |a: i64| -?> () { (a >= 1 && a <= 31).then_some(()) });
    add_primitive!( eg, "is-shl-in-u32" = |a: i64| -?> () { (a >= 1 && a <= 31).then_some(()) });
    add_primitive!( eg, "is-shl-in-i16" = |a: i64| -?> () { (a >= 1 && a <= 15).then_some(()) });
    add_primitive!( eg, "is-shl-in-u16" = |a: i64| -?> () { (a >= 1 && a <= 15).then_some(()) });
    add_primitive!( eg, "is-shl-in-i8" = |a: i64| -?> () { (a >= 1 && a <= 7).then_some(()) });
    add_primitive!( eg, "is-shl-in-u8" = |a: i64| -?> () { (a >= 1 && a <= 7).then_some(()) });

    add_primitive!( eg, "is-nonzero-i64" = |a: i64| -?> () { (a != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-u64" = |a: i64| -?> () { ((a as u64) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-i32" = |a: i64| -?> () { ((a as i32) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-u32" = |a: i64| -?> () { ((a as u32) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-i16" = |a: i64| -?> () { ((a as i16) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-u16" = |a: i64| -?> () { ((a as u16) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-i8" = |a: i64| -?> () { ((a as i8) != 0).then_some(()) });
    add_primitive!( eg, "is-nonzero-u8" = |a: i64| -?> () { ((a as u8) != 0).then_some(()) });

    add_primitive!( eg, "is-2-pow-n-i64" = |a: i64| -?> () { {let a= a as u64;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-u64" = |a: i64| -?> () { {let a= a as u64;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-i32" = |a: i64| -?> () { {let a= a as u32;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-u32" = |a: i64| -?> () { {let a= a as u32;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-i16" = |a: i64| -?> () { {let a= a as u16;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-u16" = |a: i64| -?> () { {let a= a as u16;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-i8" = |a: i64| -?> () { {let a= a as u8;(a>1&&a&(a-1)==0).then_some(())} });
    add_primitive!( eg, "is-2-pow-n-u8" = |a: i64| -?> () { {let a= a as u8;(a>1&&a&(a-1)==0).then_some(())} });

    // is-mersenne-<type>: value is a low run of 1s (2^k - 1) in the type width,
    // i.e. m != 0 && (m & (m+1)) == 0 in the truncated domain. Used to license
    // "low bits depend only on low bits" mask rules.
    add_primitive!( eg, "is-mersenne-i64" = |a: i64| -?> () { {let m=a as u64;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-u64" = |a: i64| -?> () { {let m=a as u64;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-i32" = |a: i64| -?> () { {let m=a as u32;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-u32" = |a: i64| -?> () { {let m=a as u32;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-i16" = |a: i64| -?> () { {let m=a as u16;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-u16" = |a: i64| -?> () { {let m=a as u16;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-i8" = |a: i64| -?> () { {let m=a as u8;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });
    add_primitive!( eg, "is-mersenne-u8" = |a: i64| -?> () { {let m=a as u8;(m!=0&&m&m.wrapping_add(1)==0).then_some(())} });

    // is-sign-bit-<type>: value equals 1 << (width-1) in the type domain (the
    // top bit). Adding it never produces a surviving carry, so `+c` == `^c`.
    add_primitive!( eg, "is-sign-bit-i64" = |a: i64| -?> () { ((a as u64)==1u64<<63).then_some(()) });
    add_primitive!( eg, "is-sign-bit-u64" = |a: i64| -?> () { ((a as u64)==1u64<<63).then_some(()) });
    add_primitive!( eg, "is-sign-bit-i32" = |a: i64| -?> () { ((a as u32)==1u32<<31).then_some(()) });
    add_primitive!( eg, "is-sign-bit-u32" = |a: i64| -?> () { ((a as u32)==1u32<<31).then_some(()) });
    add_primitive!( eg, "is-sign-bit-i16" = |a: i64| -?> () { ((a as u16)==1u16<<15).then_some(()) });
    add_primitive!( eg, "is-sign-bit-u16" = |a: i64| -?> () { ((a as u16)==1u16<<15).then_some(()) });
    add_primitive!( eg, "is-sign-bit-i8" = |a: i64| -?> () { ((a as u8)==1u8<<7).then_some(()) });
    add_primitive!( eg, "is-sign-bit-u8" = |a: i64| -?> () { ((a as u8)==1u8<<7).then_some(()) });

    // is-disjoint-<type>: two constants share no set bits in the type domain, so
    // `+`, `|`, `^` all coincide on `(x&c1)`, `(x&c2)`.
    add_primitive!( eg, "is-disjoint-i64" = |a: i64, b: i64| -?> () { (((a as u64)&(b as u64))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-u64" = |a: i64, b: i64| -?> () { (((a as u64)&(b as u64))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-i32" = |a: i64, b: i64| -?> () { (((a as u32)&(b as u32))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-u32" = |a: i64, b: i64| -?> () { (((a as u32)&(b as u32))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-i16" = |a: i64, b: i64| -?> () { (((a as u16)&(b as u16))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-u16" = |a: i64, b: i64| -?> () { (((a as u16)&(b as u16))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-i8" = |a: i64, b: i64| -?> () { (((a as u8)&(b as u8))==0).then_some(()) });
    add_primitive!( eg, "is-disjoint-u8" = |a: i64, b: i64| -?> () { (((a as u8)&(b as u8))==0).then_some(()) });

    add_primitive!(eg, "kz-shl" = |z: i64, k: i64, w: i64| -?> i64 { kz_shl(z, k, w) });
    add_primitive!(eg, "kz-shr" = |z: i64, k: i64, w: i64, s: i64| -?> i64 { kz_shr(z, k, w, s != 0) });
    add_primitive!(eg, "kz-low" = |z: i64, w: i64| -> i64 { kz_low(z, w) });
    add_primitive!(eg, "kz-add" = |a: i64, b: i64, w: i64| -> i64 { kz_add(a, b, w) });
    add_primitive!(eg, "kz-mul" = |a: i64, b: i64, w: i64| -> i64 { kz_mul(a, b, w) });
    add_primitive!(eg, "all-ones" = |z: i64, w: i64| -?> () { {let m = lowmask(w as u32); (z & m == m).then_some(())} });
}
/// One equality-saturation round on a fresh e-graph: insert `s` (unioned with
/// its linear-MBA rebuild), run the schedule, extract the best term (in egglog
/// syntax).
/// One saturate-and-extract round on `s` together with its linear-MBA rebuild, or
/// on the rebuild alone if `keep_input` is false and the pre-pass changed `s`.
pub fn simplify_round(egg: &str, s: &str, cli: &Cli, keep_input: bool) -> Result<String, Error> {
    simplify_round_with(egg, s, cli, keep_input, &sched_options(cli))
}

fn sched_options(cli: &Cli) -> sched::Options {
    sched::Options {
        on: cli.sched,
        disable: cli.disable.clone(),
        trace: cli.trace,
        deadline: sched::deadline(cli.time_limit),
    }
}

fn simplify_round_with(egg: &str, s: &str, cli: &Cli, keep_input: bool, opts: &sched::Options) -> Result<String, Error> {
    let mut egraph = new_experimental_egraph();
    init_egg_function(&mut egraph);
    egraph.parse_and_run_program(None, egg)?;
    let (alt, other) = linear_mba::simplify_linear_with(s, width_of(&cli.num_type), opts);
    let mut roots: Vec<&str> = match alt != s {
        true if !keep_input => vec![&alt],
        true => vec![s, &alt],
        false => vec![s],
    };
    roots.extend(other.iter().map(String::as_str));
    // Subterms repeat a lot in large inputs; egglog reads the text once per occurrence.
    let mut table = dag::NodeTable::new();
    let ids: Vec<dag::NodeId> = roots.iter().map(|r| table.intern(&eval::parse(r))).collect();
    let (lets, roots) = table.show_shared(&ids, "shared-");
    let s = &roots[0];
    let union: String = roots[1..].iter().map(|o| format!("(union expr {o})")).collect();
    let result = egraph.parse_and_run_program(
        None,
        &format!(
            r#"
{lets}
(let expr {})
{union}
(run-schedule
    (let-scheduler babibo
      (back-off
        :match-limit 64
        :ban-length 3
      )
    )
    (repeat {}
        (seq
            (run-with babibo default-ruleset)
            (run-with babibo canonicalization)
            (saturate (run constant-folding))
            (saturate (run analysis))
            (saturate (run identity-zero-element))
            (run-with babibo simplify)
        )
    )
)
(extract expr)"#,
            s, cli.iter_limit
        ),
    )?;
    Ok(result
        .last()
        .ok_or(ParseError(ast::ParseError(
            Span::Panic,
            "fail to parse egglog".to_string(),
        )))?
        .to_string()
        .trim()
        .to_string())
}

/// Extract-and-restart driver: repeatedly saturate on a fresh e-graph seeded
/// with the previous round's extraction, until a fixpoint (or the round cap
/// `cli.max_restarts`). Restarting discards the blown-up e-graph, so later
/// rounds resume rewriting from the smaller term with the full match budget
/// available again.
pub fn simplify(s: &str, cli: &Cli) -> Result<String, Error> {
    let egg = make_egg(&cli.num_type);
    let opts = sched_options(cli);
    sched::take_used();
    let mut seed = drive(&egg, s, cli, &opts)?;
    // The rules can finish a smaller pre-pass result worse, so a run whose pre-pass the
    // scheduler changed is compared with the run without it.
    if opts.on && sched::take_used() {
        let legacy = drive(&egg, s, cli, &sched::Options { on: false, ..opts.clone() })?;
        if eval::size(&eval::parse(&legacy)) <= eval::size(&eval::parse(&seed)) {
            seed = legacy;
        }
    }
    Ok(egglog_to_infix(&seed, &|n| norm_const(n, &cli.num_type)))
}

/// The restart rounds of `simplify`; returns the last extraction.
fn drive(egg: &str, s: &str, cli: &Cli, opts: &sched::Options) -> Result<String, Error> {
    let mut seed = s.to_string();
    // Extraction prefers fewer non-constant nodes, but results are compared by node count,
    // so the forms the pre-pass and the rules give along the way are kept by node count.
    let size_of = |e: &str| eval::size(&eval::parse(e));
    let mut smallest: Option<(usize, String)> = None;
    let mut offer = |e: &str| {
        let n = size_of(e);
        if smallest.as_ref().is_none_or(|(m, _)| n < *m) {
            smallest = Some((n, e.to_string()));
        }
    };
    let (mut rounds, mut extra, mut first) = (cli.max_restarts.max(1), 2, true);
    while rounds > 0 {
        rounds -= 1;
        let (alt, other) = linear_mba::simplify_linear_with(&seed, width_of(&cli.num_type), opts);
        offer(&alt);
        other.iter().for_each(|o| offer(o));
        // Saturating a large input is most of the run time and rarely beats its
        // rebuild; it is kept only where rules do better from the input: results
        // that still mix arithmetic or constants into bitwise operations, and
        // inputs with shifts, division or mulhi, unless the rebuild is already tiny.
        let opaque = ["(Shl ", "(Shr ", "(Div ", "(Mod ", "(Mulhi "].iter().any(|o| seed.contains(o))
            && !(first && eval::size(&eval::parse(&linear_mba::simplify_linear_with(&seed, width_of(&cli.num_type), &opts).0)) <= linear_mba::TINY);
        let mut extracted = simplify_round_with(&egg, &seed, cli, first && opaque, &opts)?;
        if first && !opaque && mixed(&eval::parse(&extracted)) {
            let full = simplify_round_with(&egg, &seed, cli, true, &opts)?;
            if eval::size(&eval::parse(&full)) <= eval::size(&eval::parse(&extracted)) {
                extracted = full;
            }
        }
        offer(&extracted);
        if opts.trace {
            eprintln!("round: seed {} extracted {}", eval::size(&eval::parse(&seed)), eval::size(&eval::parse(&extracted)));
        }
        first = false;
        if extracted == seed || opts.deadline.is_some_and(|d| std::time::Instant::now() >= d) {
            seed = extracted;
            break;
        }
        seed = extracted;
        // The last extraction can still hold a linear region the pre-pass rebuilds.
        if rounds == 0 && extra > 0 && linear_mba::simplify_linear_with(&seed, width_of(&cli.num_type), &opts).0 != seed {
            rounds = 1;
            extra -= 1;
        }
    }
    let polished = linear_mba::polish(&seed, width_of(&cli.num_type));
    if opts.trace {
        eprintln!("polish: {} -> {}", size_of(&seed), size_of(&polished));
    }
    offer(&polished);
    match smallest {
        Some((n, e)) if n < size_of(&seed) => Ok(e),
        _ => Ok(seed),
    }
}

/// Whether `t` has an arithmetic operation or a constant directly under a bitwise one.
fn mixed(t: &eval::Term) -> bool {
    let eval::Term::Op(op, a) = t else { return false };
    let bit = |o: &eval::Op| matches!(o, eval::Op::And | eval::Op::Or | eval::Op::Xor | eval::Op::Not);
    let plain = |x: &eval::Term| match x {
        eval::Term::Op(o, _) => bit(o),
        eval::Term::Num(_) => false,
        eval::Term::Var(_) => true,
    };
    bit(op) && !a.iter().all(plain) || a.iter().any(mixed)
}

fn norm_const(n: i64, num_type: &str) -> i64 {
    match num_type {
        "i8" => (n as i8) as i64,
        "u8" => (n as u8) as i64,
        "i16" => (n as i16) as i64,
        "u16" => (n as u16) as i64,
        "i32" => (n as i32) as i64,
        "u32" => (n as u32) as i64,
        _ => n,
    }
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    #[arg(
        short,
        long,
        default_value_t = false,
        help = "Output expression in egglog format instead of simplifying"
    )]
    pub rule_compile: bool,
    #[arg(
        short,
        long,
        default_value_t = false,
        help = "Output expression in egglog rule format instead of simplifying"
    )]
    pub expr_compile: bool,
    #[arg(
        short,
        long,
        default_value = "i64",
        value_parser=["i64","u64","i32","u32","i16","u16","i8","u8"],
        help = "Numeric type to use"
    )]
    pub num_type: String,
    #[arg(
        short,
        long,
        default_value_t = 10,
        help = "Maximum number of simplification iterations"
    )]
    pub iter_limit: usize,
    #[arg(
        short,
        long,
        default_value_t = 2,
        help = "Maximum number of extract-and-restart rounds (each round runs the full iteration schedule on a fresh e-graph seeded with the previous round's result)"
    )]
    pub max_restarts: usize,
    #[arg(long, help = "Run the pass scheduler after the pre-pass")]
    pub sched: bool,
    #[arg(long, value_delimiter = ',', help = "Scheduler passes not to run, comma-separated")]
    pub disable: Vec<String>,
    #[arg(long, help = "Print scheduler statistics to stderr")]
    pub trace: bool,
    #[arg(long, help = "Stop scheduling and restarting after this many seconds and return the best result so far")]
    pub time_limit: Option<f64>,
    #[arg(help = "The infix expression to simplify")]
    pub expr: String,
}

impl Default for Cli {
    fn default() -> Cli {
        Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i64".to_string(),
            iter_limit: 10,
            max_restarts: 2,
            sched: false,
            disable: Vec::new(),
            trace: false,
            time_limit: None,
            expr: String::new(),
        }
    }
}
