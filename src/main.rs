mod expr_convert;

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
    (Mulhi Expr Expr)
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
(rewrite (Div (Num a) (Num b))   (Num (wrapping-div-{0} a b)) :when ((!= b 0)) :ruleset constant-folding)
(rewrite (And (Num a) (Num b))   (Num (wrapping-and-{0} a b)) :ruleset constant-folding)
(rewrite (Or (Num a) (Num b))   (Num (wrapping-or-{0} a b)) :ruleset constant-folding)
(rewrite (Xor (Num a) (Num b))   (Num (wrapping-xor-{0} a b)) :ruleset constant-folding)
(rewrite (Shl (Num a) (Num b))   (Num (wrapping-shl-{0} a b)) :ruleset constant-folding)
(rewrite (Shr (Num a) (Num b))   (Num (wrapping-shr-{0} a b)) :ruleset constant-folding)
(rewrite (Mod (Num a) (Num b))   (Num (wrapping-mod-{0} a b)) :when ((!= b 0)) :ruleset constant-folding)
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
    egg.push_str(&rewrite!("a*b/b"=>"a";"identity-zero-element :when ((non-zero b))"));
    egg.push_str(&rewrite!("a/a"=>"1";"identity-zero-element :when ((non-zero a))"));
    egg.push_str(&rewrite!("a%a"=>"0";"identity-zero-element :when ((non-zero a))"));
    egg.push_str(&rewrite!("a%1"=>"0";"identity-zero-element"));
    // HD ch. 9: fundamental division identity x = (x/y)*y + x%y
    egg.push_str(&rewrite!("(x/y)*y+x%y"=>"x";"identity-zero-element"));
    egg.push_str(&rewrite!("x-(x/y)*y"=>"x%y";"identity-zero-element"));
    egg.push_str(&rewrite!("a/-1"=>"-a";"identity-zero-element"));
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
    egg.push_str(&rewrite!("(Num a)*x+(Num a)"=>"(Num a)*(x+1)";"canonicalization"));
    egg.push_str(&rewrite!("(Num a)*x-(Num a)"=>"(Num a)*(x-1)";"canonicalization"));
    egg.push_str(&rewrite!("((Num a)*x)&(Num a)"<=>"(Num a)*(x&1)";format!("canonicalization :when ((is-2-pow-n-{} a))",num_type)));
    egg.push_str(&rewrite!("-(x/y)"<=>"-x/y";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a-b)"=>"a*a-b*b";"canonicalization"));
    egg.push_str(&rewrite!("(a+b)*(a+b)"=>"a*a+2*a*b+b*b";"canonicalization"));
    egg.push_str(&rewrite!("((x+y)*z)"<=>"(x*z+y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x-y)*z)"<=>"(x*z-y*z)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)+y)"=>"((x+1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("((x*y)-y)"=>"((x-1)*y)";"canonicalization"));
    egg.push_str(&rewrite!("a>>b>>c"=>"a>>(b+c)";"canonicalization"));
    egg.push_str(&rewrite!("a<<b<<c"=>"a<<(b+c)";"canonicalization"));
    egg.push_str(&rewrite!("(a|b)&(a|c)"=>"a|(b&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b|c)"<=>"(a&b)|(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("a&(b^c)"<=>"(a&b)^(a&c)";"canonicalization"));
    egg.push_str(&rewrite!("(x>>z)&(y>>z)"=>"(x&y)>>z";"canonicalization"));
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
    egg.push_str(&rewrite!("~x^~y"=>"x^y";"simplify"));
    egg.push_str(&rewrite!("(x|y)^(~x|~y)"=>"~(x^y)";"simplify"));
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

    // HD ch. 10: recognize magic-number division and rewrite back to `n / d`.
    // The divisor d is recovered from (M, s) by the magic-div-* primitive, which
    // returns d only if (M, s) is exactly the magic pair for some d under this
    // width/signedness (else the rule does not fire). `Mulhi` is the high half of
    // the 2W-bit product (mulhs for signed types, mulhu for unsigned).
    let w1 = width_of(num_type) - 1;
    if is_signed(num_type) {
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

    egg
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
fn pow2_div(mask: i64, k: i64, w: u32) -> Option<i64> {
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
fn magic_s(d: i64, w: u32) -> Option<(u128, u32, bool)> {
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
fn magic_u(d: i64, w: u32) -> Option<(u128, u32, bool)> {
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
fn magic_div_s(m_bits: i64, s: i64, w: u32, want_add: bool) -> Option<i64> {
    if s < 0 {
        return None;
    }
    let mask: u128 = (1u128 << w) - 1;
    let m = (m_bits as u64 as u128) & mask;
    if m == 0 {
        return None;
    }
    let p = s as u32 + w;
    let d0 = (1u128 << p) / m;
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
fn magic_div_u(m_bits: i64, s: i64, w: u32, want_add: bool) -> Option<i64> {
    if s < 0 {
        return None;
    }
    let mask: u128 = (1u128 << w) - 1;
    let mlow = (m_bits as u64 as u128) & mask;
    let m_full = if want_add { (1u128 << w) + mlow } else { mlow };
    if m_full == 0 {
        return None;
    }
    let p = s as u32 + w;
    let d0 = (1u128 << p) / m_full;
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

    add_primitive!( eg, "is-bit-not-eq-i64" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffffffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u64" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffffffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i32" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u32" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffffffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i16" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u16" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xffff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-i8" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xff).then_some(()) });
    add_primitive!( eg, "is-bit-not-eq-u8" = |a: i64, b: i64| -?> () { ((a as u64 ).wrapping_add(b as u64) == 0xff).then_some(()) });

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
    add_primitive!(eg, "magicu-div-add-u64" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s + 1, 64, true) });
    add_primitive!(eg, "magicu-div-add-u32" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s + 1, 32, true) });
    add_primitive!(eg, "magicu-div-add-u16" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s + 1, 16, true) });
    add_primitive!(eg, "magicu-div-add-u8" = |m: i64, s: i64| -?> i64 { magic_div_u(m, s + 1, 8, true) });

    add_primitive!(eg, "ilog2" = |a: i64| -> i64 { (a as u64).trailing_zeros() as i64 } );
    add_primitive!(eg, "pow2" = |a: i64| -> i64 { 1i64.wrapping_shl(a as u32) } );
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
    Ok(egglog_to_infix(
        &result
            .last()
            .ok_or(ParseError(ast::ParseError(
                Span::Panic,
                "fail to parse egglog".to_string(),
            )))?
            .to_string(),
        &|n| norm_const(n, &cli.num_type),
    ))
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
    use crate::expr_convert::ac_canon_infix;

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
    #[test]
    fn test_formal_simplify() {
        let mut cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i64".to_string(),
            iter_limit: 20,
            expr: "".to_string(),
        };
        let test_pairs = vec![
            ("a + 0", vec!["a"], 10),
            ("0 + a", vec!["a"], 10),
            ("a + 0 + b", vec!["(a + b)"], 10),
            ("a - a", vec!["0"], 10),
            ("a - a + b", vec!["b"], 10),
            ("a + b - a", vec!["b"], 10),
            ("a + b - b - a", vec!["0"], 10),
            ("a * 1", vec!["a"], 10),
            ("1 * a", vec!["a"], 10),
            ("a * 0", vec!["0"], 10),
            ("0 * a", vec!["0"], 10),
            ("a + a", vec!["(a + a)", "(2 * a)"], 10),
            ("a + a + a", vec!["(3 * a)"], 10),
            ("2 * a + 3 * a", vec!["(5 * a)"], 10),
            ("5 + 3", vec!["8"], 10),
            ("17 - 8", vec!["9"], 10),
            ("4 * 6", vec!["0x18"], 10),
            ("a + 5 - 5", vec!["a"], 10),
            ("a * 8 / 8", vec!["a"], 10),
            ("6 / 2", vec!["3"], 10),
            ("10 % 3", vec!["1"], 10),
            ("a / 2 + (b - b)", vec!["(a / 2)"], 10),
            ("(x << 2) + x", vec!["(5 * x)", "(x * 5)"], 10),
            ("(a << 3) / 8", vec!["a"], 10),
            ("(x / y) * y + x % y", vec!["x"], 10),
            ("x - (x / y) * y", vec!["(x % y)"], 10),
            ("x % 1", vec!["0"], 10),
            ("(x << 2) ^ (4 * x)", vec!["0"], 10),
            ("a / a", vec!["(a / a)"], 10),
            ("1 + (b - b) / (b - b)", vec!["1"], 10),
            ("(a | 4) / (a | 4)", vec!["1"], 10),
            ("b * (a | 1) / (a | 1)", vec!["b"], 10),
            ("(3 * (b | 1)) / (3 * (b | 1))", vec!["1"], 10),
            ("(x | 2) % (x | 2)", vec!["0"], 10),
            ("3 * a + 5 * a + 2 * a", vec!["(0xa * a)"], 10),
            ("12 + a + 8 + b - 20", vec!["(a + b)"], 10),
            ("a & a", vec!["a"], 10),
            ("a | a", vec!["a"], 10),
            ("a ^ a", vec!["0"], 10),
            ("a & 0", vec!["0"], 10),
            ("a | 0", vec!["a"], 10),
            ("a ^ 0", vec!["a"], 10),
            ("a & -1", vec!["a"], 10),
            ("a | -1", vec!["-1"], 10),
            ("a ^ -1", vec!["~a"], 10),
            ("~(~a)", vec!["a"], 10),
            ("a & (a | b)", vec!["a"], 10),
            ("a | (a & b)", vec!["a"], 10),
            ("a ^ b ^ a", vec!["b"], 10),
            ("a ^ a ^ b ^ b", vec!["0"], 10),
            ("a ^ a ^ a", vec!["a"], 10),
            (
                "(x & 0xffff) << 8",
                vec!["((x & 0xffff) << 8)", "((x & 0xffff) * 0x100)"],
                10,
            ),
            (
                "x >> 3 << 3",
                vec!["((x >> 3) << 3)", "((x >> 3) * 8)"],
                10,
            ),
            ("(a + 1) & ~1", vec!["((a + 1) & -2)"], 10),
            ("(a * 2) >> 1", vec!["((a * 2) >> 1)"], 10),
            ("a + (b & 1)", vec!["(a + (b & 1))"], 10),
            (
                "(a << 3) + (b & 7)",
                vec!["((a << 3) + (b & 7))", "((a * 8) + (b & 7))"],
                10,
            ),
            ("((a + b) * c - d) + (d - a * c)", vec!["(b * c)"], 10),
            (
                "a * b + a * c + b * a + b * c",
                vec![
                    "((((b + c) + b) * a) + (b * c))",
                    "(((b + a) * c) + (2 * (a * b)))",
                ],
                10,
            ),
            (
                "(a + b + c) * (a + b + c)",
                vec!["(((a + b) + c) * ((a + b) + c))"],
                10,
            ),
            ("a - b + c - a + b - c", vec!["0"], 10),
            ("a + (~a + 1)", vec!["0"], 10),
            ("(a & b) ^ (a & ~b)", vec!["a"], 10),
            ("a + 1 + 3", vec!["(4 + a)"], 10),
            ("a + b + 0 + c + 0", vec!["((a + b) + c)"], 10),
            ("0 * (a + b + c)", vec!["0"], 10),
            ("1 * (a + b + c)", vec!["((a + b) + c)"], 10),
            ("(a + b) - (a + b)", vec!["0"], 10),
            ("a * (b - b)", vec!["0"], 10),
            ("a & ~a", vec!["0"], 10),
            ("a | ~a", vec!["-1"], 10),
            ("(a ^ b) ^ b", vec!["a"], 10),
            ("a ^ (b ^ a)", vec!["b"], 10),
            ("~0", vec!["-1"], 10),
            ("~-1", vec!["0"], 10),
            ("x & (x | y)", vec!["x"], 10),
            ("(x | y) & x", vec!["x"], 10),
            ("a + b * 0", vec!["a"], 10),
            ("a * (1 + 0)", vec!["a"], 10),
            ("(2 * a) + (3 * a) + a", vec!["(6 * a)"], 10),
            ("a - 0", vec!["a"], 10),
            ("0 - a", vec!["-a"], 10),
            ("-(a - b)", vec!["(b - a)"], 10),
            ("a * -1", vec!["-a"], 10),
            ("-1 * a", vec!["-a"], 10),
            ("a + -a", vec!["0"], 10),
            ("a ^ (a ^ b ^ c) ^ b ^ c", vec!["0"], 10),
        ];
        let mut c = 0;
        for (case, expect, iter) in test_pairs {
            if case.is_empty() {
                continue;
            }
            c += 1;
            if c < 0 {
                continue;
            }
            cli.iter_limit = iter;
            let egg_expr = infix_to_egglog(case, true);
            let result = simplify(&egg_expr, &cli);
            let ok = result.is_ok();
            let r = if ok {
                result.unwrap()
            } else {
                result.unwrap_err().to_string()
            };
            println!("#{} {}", c, case);
            assert!(
                matches_expected(&expect, &r, ok),
                "{} {}\n{} != {:?} \n{}",
                case,
                egg_expr,
                r,
                expect,
                make_egg(&cli.num_type)
            );
        }
    }
    #[test]
    fn test_magic_numbers() {
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
    fn test_magic_division() {
        let mut cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i32".to_string(),
            iter_limit: 12,
            expr: "".to_string(),
        };
        // (num_type, expr, expected)
        let cases = vec![
            ("i32", "mulhi(0x55555556, n) + ((n >> 31) & 1)", "(n / 3)"),
            ("i32", "(mulhi(0x66666667, n) >> 1) + ((n >> 31) & 1)", "(n / 5)"),
            (
                "i32",
                "((mulhi(0x92492493, n) + n) >> 2) + ((n >> 31) & 1)",
                "(n / 7)",
            ),
            ("u32", "mulhi(0xAAAAAAAB, n) >> 1", "(n / 3)"),
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
            // Non-magic multiplier: must NOT collapse to a division.
            (
                "i32",
                "mulhi(0x12345678, n) + ((n >> 31) & 1)",
                "(mulhi(0x12345678, n) + ((n >> 0x1f) & 1))",
            ),
        ];
        for (nt, case, expected) in cases {
            cli.num_type = nt.to_string();
            let egg_expr = infix_to_egglog(case, true);
            let r = simplify(&egg_expr, &cli).unwrap();
            println!("{} -> {}", case, r);
            assert_eq!(r, expected, "case: {}", case);
        }
    }

    #[test]
    fn test_unsigned_simplify() {
        let mut cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "u8".to_string(),
            iter_limit: 10,
            expr: "".to_string(),
        };
        let test_pairs = vec![
            ("(x / 8) ^ (x >> 3)", vec!["0"], 10),
            ("(x % 8) ^ (x & 7)", vec!["0"], 10),
            ("x / 4 * 4 + x % 4", vec!["x"], 10),
        ];
        let mut c = 0;
        for (case, expect, iter) in test_pairs {
            c += 1;
            cli.iter_limit = iter;
            let egg_expr = infix_to_egglog(case, true);
            let result = simplify(&egg_expr, &cli);
            let ok = result.is_ok();
            let r = if ok {
                result.unwrap()
            } else {
                result.unwrap_err().to_string()
            };
            println!("#{} {}", c, case);
            assert!(
                matches_expected(&expect, &r, ok),
                "{} {}\n{} != {:?}",
                case,
                egg_expr,
                r,
                expect,
            );
        }
    }

    #[test]
    fn test_complex_simplify() {
        let mut cli = Cli {
            rule_compile: false,
            expr_compile: false,
            num_type: "i8".to_string(),
            iter_limit: 10,
            expr: "".to_string(),
        };
        let test_pairs = vec![
            ("x + (~y + 1)", vec!["(x - y)"], 10),
            ("(x ^ y) - 2*(~x & y)", vec!["(x - y)"], 10),
            ("(x & ~y) - (~x & y)", vec!["(x - y)"], 10),
            ("2*(x & ~y) - (x ^ y)", vec!["(x - y)"], 10),
            (
                "(-x - 1) - (-2 * x)",
                vec!["(-1 + x)", "~-x", "(x + -1)"],
                10,
            ),
            ("2*x + ~x", vec!["~-x", "(-1 + x)", "(x + -1)"], 10),
            (
                "2*(x | y) + (x ^ ~y)",
                vec![
                    "(~-y + x)",
                    "(~-x + y)",
                    "((x + y) + -1)",
                    "~(-y - x)",
                    "~(-x - y)",
                ],
                10,
            ),
            ("(x | ~y) + y", vec!["((x & y) + -1)", "~-(x & y)"], 10),
            (
                "(x + y) + ~(x & y)",
                vec!["((x | y) + -1)", "((y | x) + -1)", "~-(x | y)", "~-(y | x)"],
                10,
            ),
            (
                "(~x | 1) + x",
                vec![
                    "((1 & x) + -1)",
                    "-(~x & 1)",
                    "-(1 & ~x)",
                    "~-(1 & x)",
                    "((-2 | x) + 1)",
                ],
                10,
            ),
            ("x - (~y + 1)", vec!["(x + y)"], 10),
            ("(x ^ y) + 2*(x & y)", vec!["(x + y)"], 10),
            ("(x | y) + (x & y)", vec!["(x + y)"], 10),
            ("2*(x | y) - (x ^ y)", vec!["(x + y)"], 10),
            ("2*(x | y | z) - (x ^ (y | z))", vec!["((y | z) + x)"], 10),
            ("(x ^ y) + 2*(x & y)", vec!["(x + y)"], 10),
            ("(a ^ 5) + 2*(a & 5)", vec!["(a + 5)"], 10),
            (
                "((a & 0xff) ^ 0x12) + 2*(a & 0x12)",
                vec!["((a & 0xff) + 0x12)", "(a + 0x12)", "(0x12 + a)"],
                10,
            ),
            ("(x & 0xf0) + (x & 0x0f)", vec!["x"], 10),
            ("(x & 0xf0) | (x & 0x0f)", vec!["x"], 10),
            ("(x & 0xf0) ^ (x & 0x0f)", vec!["x"], 10),
            ("(~x - y) ^ ~(x + y)", vec!["0"], 10),
            ("(~x + y) ^ ~(x - y)", vec!["0"], 10),
            ("(0 - ~x) ^ (x + 1)", vec!["0"], 10),
            ("a & 0xff", vec!["a"], 10),
            ("a ^ 0xff", vec!["~a"], 10),
            ("a * 0x100", vec!["0"], 10),
            ("a | 0xff", vec!["-1"], 10),
            ("(a ^ 0xfe) + 2*(a | 0x01)", vec!["a"], 10),
            (
                "~(x ^ y) + 2*(x | y)",
                vec![
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
                vec![
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
            ("(x - y) - 2*(x | ~y)", vec!["((x ^ y) + 2)"], 10),
            ("(x - y) - 2*(~(~x & y))", vec!["((x ^ y) + 2)"], 10),
            ("(x | y)*(x & y) + (x & ~y)*(y & ~x)", vec!["(x * y)"], 10),
            ("(x | y)*(x & y) + ~(x | ~y)*(x & ~y)", vec!["(x * y)"], 10),
            (
                "2 + 2*(y + (x | ~y))",
                vec![
                    "(2 * (x & y))",
                    "(2 * (y & x))",
                    "((x & y) * 2)",
                    "((y & x) * 2)",
                ],
                10,
            ),
            ("-(x & y) - (x & y)", vec!["(-2 * (x & y))"], 10),
            ("(~x | y) - ~x", vec!["(x & y)"], 10),
            ("(x + y) - (x | y)", vec!["(x & y)"], 10),
            ("(x | y) - (x ^ y)", vec!["(x & y)"], 10),
            ("(x | y) & ~(x ^ y)", vec!["(x & y)"], 10),
            ("(x & y) & ~(x ^ y)", vec!["(x & y)"], 10),
            ("x & ~(x ^ y)", vec!["(x & y)"], 10),
            ("(x | y) - y", vec!["(x & ~y)"], 10),
            ("x - (x & y)", vec!["(x & ~y)"], 10),
            ("x ^ (x & y)", vec!["(x & ~y)"], 10),
            ("x & (x ^ y)", vec!["(x & ~y)"], 10),
            ("(x | y) ^ y", vec!["(x & ~y)"], 10),
            (
                "(x & z) | (y & z)",
                vec!["((x | y) & z)", "(z & (y | x))", "(z & (x | y))"],
                10,
            ),
            (
                "(x & z) ^ (y & z)",
                vec!["((x ^ y) & z)", "(z & (y ^ x))", "(z & (x ^ y))"],
                10,
            ),
            ("(~x | y) + (x + 1)", vec!["(x & y)"], 10),
            ("(x | y) & (x ^ ~y)", vec!["(x & y)"], 10),
            (" (x ^ ~y) & y", vec!["(x & y)", "(y & x)"], 10),
            ("(x * x) & 3", vec!["(x & 1)"], 10),
            ("-x - 1", vec!["~x"], 10),
            ("~(x | y) | ~y", vec!["~y"], 10),
            ("(x - 1) - 2*x", vec!["~x"], 10),
            ("~(x ^ y) ^ y", vec!["~x"], 10),
            ("~x ^ ~y", vec!["(x ^ y)"], 10),
            ("(x ^ y) | ~(x | y)", vec!["~(x & y)", "~(y & x)"], 10),
            ("~x | ~y", vec!["~(x & y)", "~(y & x)"], 10),
            ("~x & ~y", vec!["~(x | y)", "~(y | x)"], 10),
            (
                "(x & y) | ~(x | y)",
                vec!["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            ("(x & y) ^ (x | ~y)", vec!["~y"], 10),
            (
                "(x & y) | (~x & ~y)",
                vec!["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x | y) ^ (~x | ~y)",
                vec!["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            (
                "(x | ~y) & (~x | y)",
                vec!["~(x ^ y)", "(x ^ ~y)", "(~y ^ x)", "(~x ^ y)", "(y ^ ~x)"],
                10,
            ),
            ("(~x | ~y) | (x ^ y)", vec!["~(x & y)"], 10),
            ("~x | (x ^ y)", vec!["~(x & y)", "~(y & x)"], 10),
            (
                "(x ^ ~y) - 2*(x & y)",
                vec!["~(x + y)", "(~x - y)", "(~y - x)"],
                10,
            ),
            ("(x & ~y) | ~(x | y)", vec!["~y"], 10),
            ("~x & (~x ^ c)", vec!["(x & ~c) ^ ~c", "~(x | c)"], 10),
            (
                "((x ^ 0x12) & 1) | ((x ^ 8) & 0xfe)",
                vec!["((x ^ 8) | (1 & x))", "(x ^ 8)"],
                15,
            ),
            ("((x ^ 8) | (1 & x))", vec!["(x ^ 8)"], 15),
            (
                "(x - 7) + 11*(x - 8)",
                vec![
                    "(-0x5f + (0xc * x))",
                    "((x * 0xc) + -0x5f)",
                    "((0xc * x) + -0x5f)",
                ],
                10,
            ),
            (
                "(x >> z) & (y >> z)",
                vec!["((x & y) >> z)", "((y & x) >> z)"],
                10,
            ),
            ("2*x - (x & ~y)", vec!["(x + (x & y))", "((x & y) + x)"], 10),
            (
                "(x & ~y) - 2*x",
                vec!["-(x + (x & y))", "(-(x & y) - x)", "-((x & y) + x)"],
                10,
            ),
            (
                "(x & ~y) - (x & y)",
                vec!["((x ^ y) - y)", "((x ^ y) + -y)"],
                20,
            ),
            (
                "(~x | (~y & z)) + (x + (y & z)) - z",
                vec![
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
                vec![
                    "(x | (y | ~z))",
                    "((y | ~z) | x)",
                    "((~z | y) | x)",
                    "((x | y) | ~z)",
                    "(x | (~z | y))",
                ],
                10,
            ),
            (
                "(x | y) + (x & ~y)",
                vec!["((x ^ y) + x)", "((y ^ x) + x)", "(x + (y ^ x))"],
                10,
            ),
            ("(x & y) + (x & ~y)", vec!["x"], 10),
            ("(x & y) ^ (x & ~y)", vec!["x"], 10),
            ("x & (x | y)", vec!["x"], 10),
            ("~(x - 1)", vec!["-x"], 10),
            ("(x ^ y) - 2*(x | y)", vec!["-(x + y)", "-(y + x)"], 10),
            (
                "(-2 * (x | y)) + (x ^ y)",
                vec!["-(x + y)", "(-y - x)", "(-x - y)"],
                10,
            ),
            (
                "(x ^ (y | z)) - 2*((x | y) | z)",
                vec![
                    "-(x + (y | z))",
                    "-((y | z) + x)",
                    "(-(y | z) - x)",
                    "(-x - (y | z))",
                ],
                10,
            ),
            ("(x & y) - (x + y)", vec!["-(x | y)"], 10),
            ("(x & y) - (x | y)", vec!["-(x ^ y)", "-(y ^ x)"], 10),
            ("(x + y) - 2*(x | y)", vec!["-(x ^ y)", "-(y ^ x)"], 10),
            ("(x + y) - (x & y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x - y) - (x & -y)", vec!["(x | -y)"], 10),
            ("(x & y) + (x ^ y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x ^ y) + (x & y)", vec!["(x | y)", "(y | x)"], 10),
            ("((x + y) + 1) + ~(x & y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x + (x ^ y)) - (x & ~y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x & y) | (x ^ y)", vec!["(x | y)", "(y | x)"], 10),
            (
                "(x & (y ^ z)) | ((x ^ y) ^ z)",
                vec!["(x | (y ^ z))", "((y ^ z) | x)"],
                10,
            ),
            ("(x ^ y) | y", vec!["(x | y)", "(y | x)"], 10),
            ("(x & y) ^ (x ^ y)", vec!["(x | y)", "(y | x)"], 10),
            ("~x ^ (x & y)", vec!["(~x | y)"], 10),
            ("x ^ (~x & y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x & ~y) + y", vec!["(x | y)", "(y | x)", "(y | x)"], 10),
            ("(x | y) | (~x ^ ~y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x & y) | ~(~x ^ y)", vec!["(x | y)", "(y | x)"], 10),
            ("(~x & y) | x", vec!["(x | y)", "(y | x)"], 10),
            ("~(~x | ~y) | (x ^ y)", vec!["(x | y)", "(y | x)"], 10),
            ("(x - y) + (~x | y)", vec!["(x | ~y)", "(~y | x)"], 10),
            ("(~x | y) ^ (x ^ y)", vec!["(x | ~y)", "(~y | x)"], 10),
            ("(x | y) - (x & y)", vec!["(x ^ y)"], 10),
            ("2*(x | y) - (x + y)", vec!["(x ^ y)"], 10),
            ("(x + y) - 2*(x & y)", vec!["(x ^ y)"], 10),
            ("((x - y) - 2*(x | ~y)) - 2", vec!["(x ^ y)"], 10),
            ("x - (2*(x & y) - y)", vec!["(x ^ y)"], 10),
            ("x - (2*(y & ~(x ^ y)) - y)", vec!["(x ^ y)"], 10),
            ("x - (2*(x & y) - y)", vec!["(x ^ y)"], 10),
            ("x - 2*(x & y)", vec!["((x ^ y) - y)", "((x ^ y) + -y)"], 10),
            ("(x & ~y) | (~x & y)", vec!["(x ^ y)"], 10),
            ("(~x & y) ^ (x & ~y)", vec!["(x ^ y)"], 15),
            ("(x & y) ^ (x | y)", vec!["(x ^ y)"], 10),
            ("(x - y) + 2*(~x & y)", vec!["(x ^ y)"], 10),
            ("~x + (2*x | 2)", vec!["(x ^ 1)", "(1 ^ x)"], 20),
            (
                "((x ^ z) & (y ^ ~z)) | ((x ^ ~z) & (y ^ z))",
                vec!["(x ^ y)", "((y ^ z) ^ (x ^ z))"],
                10,
            ),
            ("((y ^ z) ^ (x ^ z))", vec!["(x ^ y)", "(y ^ x)"], 10),
            (
                "((x ^ z) & (y ^ z)) | ((x ^ ~z) & (y ^ ~z))",
                vec![
                    "(~x ^ y)",
                    "((y ^ z) ^ (x ^ ~z))",
                    "((y ^ ~z) ^ (x ^ z))",
                ],
                10,
            ),
            ("((y ^ z) ^ (x ^ ~z))", vec!["(~x ^ y)", "~(y ^ x)"], 10),
            ("(x + y) - 2*(x | (y - 1))", vec!["((x ^ -y) + 2)"], 10),
        ];
        let mut c = 0;
        for (case, expect, iter) in test_pairs {
            if case.is_empty() {
                continue;
            }
            c += 1;
            if c < 0 {
                continue;
            }
            cli.iter_limit = iter;
            let egg_expr = infix_to_egglog(case, true);
            let result = simplify(&egg_expr, &cli);
            let ok = result.is_ok();
            let r = if ok {
                result.unwrap()
            } else {
                result.unwrap_err().to_string()
            };
            println!("#{} {}", c, case);
            assert!(
                matches_expected(&expect, &r, ok),
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
