use super::*;
use crate::eval::{NumType, eval, parse};
use std::collections::HashMap;

fn full_eval(t: &T, w: &Ctx, env: &HashMap<String, u64>) -> u64 {
    let ty = NumType { bits: w.w, signed: false };
    eval(t, ty, &|v: &str| env[v]).expect("no division in generated terms")
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

const VARS: [&str; 6] = ["x", "y", "z", "u", "v", "w"];

fn random_term(r: &mut Rng, depth: u32) -> T {
    random_term_in(r, depth, &VARS)
}

fn random_term_in(r: &mut Rng, depth: u32, vars: &[&str]) -> T {
    let var = |r: &mut Rng| T::Var(vars[(r.next() % vars.len() as u64) as usize].into());
    if depth == 0 {
        return match r.next() % 6 {
            0 => T::Num((r.next() % 7) as i64 - 3),
            _ => var(r),
        };
    }
    let sub = |r: &mut Rng| random_term_in(r, depth - 1, vars);
    match r.next() % 12 {
        0 => T::Op(Op::Not, vec![sub(r)]),
        1 => T::Op(Op::Neg, vec![sub(r)]),
        2 | 3 => T::Op(Op::Add, vec![sub(r), sub(r)]),
        4 => T::Op(Op::Sub, vec![sub(r), sub(r)]),
        5 => T::Op(Op::Mul, vec![T::Num((r.next() % 9) as i64 - 4), sub(r)]),
        6 => T::Op(Op::And, vec![sub(r), sub(r)]),
        7 => T::Op(Op::Or, vec![sub(r), sub(r)]),
        8 => T::Op(Op::Xor, vec![sub(r), sub(r)]),
        9 => T::Op(Op::Mul, vec![sub(r), sub(r)]),
        10 => T::Op(Op::Shl, vec![sub(r), T::Num((r.next() % 10) as i64)]),
        _ => T::Op(Op::Shr, vec![sub(r), T::Num((r.next() % 4) as i64)]),
    }
}

/// Terms with the shapes `unshift` and `halve` rewrite, over `x` and `y`.
fn shifted_term(r: &mut Rng, depth: u32) -> T {
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    if depth == 0 {
        return match r.next() % 4 {
            0 => T::Num((r.next() % 9) as i64 - 4),
            1 => T::Var("x".into()),
            _ => T::Var("y".into()),
        };
    }
    let sub = |r: &mut Rng| shifted_term(r, depth - 1);
    let k = 1 + (r.next() % 3) as i64;
    let c = [1i64, -1, 3, -3, 5][(r.next() % 5) as usize];
    let even = |r: &mut Rng| match r.next() % 6 {
        0 => op(Op::Mul, vec![T::Num(c << k), sub(r)]),
        1 => op(Op::Add, vec![op(Op::Mul, vec![sub(r), T::Num(4)]), T::Num((r.next() % 4) as i64)]),
        2 => op(Op::Neg, vec![op(Op::Mul, vec![T::Num(2), sub(r)])]),
        3 => op(Op::Not, vec![op(Op::Shl, vec![sub(r), T::Num(k)])]),
        4 => op(Op::Sub, vec![op(Op::Mul, vec![T::Num(2), sub(r)]), op(Op::Mul, vec![sub(r), op(Op::Mul, vec![T::Num(2), sub(r)])])]),
        _ => T::Num((r.next() % 512) as i64 - 256),
    };
    let bit = [Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize];
    match r.next() % 8 {
        0 => op(Op::Mul, vec![T::Num(c << k), op(Op::Shr, vec![sub(r), T::Num(k)])]),
        1 => op(Op::Shl, vec![op(Op::Shr, vec![sub(r), T::Num(k)]), T::Num(k + (r.next() % 3) as i64)]),
        2 => op(Op::Mul, vec![op(Op::Not, vec![op(Op::Shr, vec![sub(r), T::Num(k)])]), T::Num(c << (k + 1))]),
        3 | 4 => op(bit, vec![even(r), even(r)]),
        5 => op(Op::Add, vec![sub(r), sub(r)]),
        6 => op(bit, vec![sub(r), sub(r)]),
        _ => op(Op::Mul, vec![sub(r), sub(r)]),
    }
}

#[test]
fn unshift_and_halve_preserve_value() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x6a09e667f3bcc909);
        let (mut unshifted, mut halved) = (0, 0);
        for _ in 0..400 {
            let depth = 1 + (r.next() % 3) as u32;
            let t = shifted_term(&mut r, depth);
            for (bits, signed) in [(8, false), (8, true), (64, false), (64, true)] {
                let (w, ty) = (Ctx::new(bits), NumType { bits, signed });
                let (u, h) = (unshift(&t, &w), halve(&t, &w));
                unshifted += (u != t) as u32;
                halved += (h != t) as u32;
                let check = |x: u64, y: u64| {
                    let env = |v: &str| if v == "x" { x } else { y };
                    let want = eval(&t, ty, &env);
                    assert_eq!(want, eval(&u, ty, &env), "{}\n{}", show(&t), show(&u));
                    assert_eq!(want, eval(&h, ty, &env), "{}\n{}", show(&t), show(&h));
                };
                if bits == 8 {
                    (0..1u64 << 16).for_each(|p| check(p & 0xff, p >> 8));
                } else {
                    (0..256).for_each(|_| check(r.next(), r.next()));
                }
            }
        }
        assert!(unshifted > 200 && halved > 200, "unshifted {unshifted}, halved {halved}");
    })
}

/// `a op b` written as a linear MBA in `a`, `b` and `a & b`, with `a_lin`
/// (equal to `a`) where `a` is not under a bitwise operation.
fn mba_op(r: &mut Rng, a: &T, a_lin: &T, b: &T) -> T {
    let op = |o: Op, x: Vec<T>| T::Op(o, x);
    let and = op(Op::And, vec![a.clone(), b.clone()]);
    let sum = op(Op::Add, vec![a_lin.clone(), b.clone()]);
    match r.next() % 3 {
        0 => op(Op::Sub, vec![sum, op(Op::Mul, vec![T::Num(2), and])]),
        1 => op(Op::Sub, vec![sum, and]),
        _ => op(Op::Sub, vec![op(Op::Mul, vec![T::Num(2), op(Op::Or, vec![a.clone(), b.clone()])]), sum]),
    }
}

#[test]
fn relate_preserves_value() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x3c6ef372fe94f82b);
        let op = |o: Op, x: Vec<T>| T::Op(o, x);
        let mut changed = 0;
        for i in 0..60 {
            let vars: &[&str] = if i % 2 == 0 { &["x", "y"] } else { &VARS };
            let (p, q) = (random_term_in(&mut r, 1, vars), random_term_in(&mut r, 1, vars));
            let (l, l_lin) = match r.next() % 3 {
                0 => (op(Op::Add, vec![p.clone(), q.clone()]), op(Op::Sub, vec![p, op(Op::Neg, vec![q])])),
                1 => (op(Op::Sub, vec![p.clone(), q.clone()]), op(Op::Add, vec![p, op(Op::Neg, vec![q])])),
                _ => (op(Op::Mul, vec![p.clone(), q.clone()]), op(Op::Mul, vec![q, p])),
            };
            let depth = 1 + (r.next() % 2) as u32;
            let mut b = random_term_in(&mut r, depth, vars);
            if r.next() % 2 == 0 {
                b = op([Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize], vec![b, T::Num((r.next() % 200) as i64 - 100)]);
            }
            let t = mba_op(&mut r, &l, &l_lin, &b);
            for (bits, signed) in [(8, false), (64, true)] {
                let (wd, ty) = (Ctx::new(bits), NumType { bits, signed });
                let base = rewrite(&t, &wd);
                let alt = relate(&base, &wd);
                changed += (alt != base) as u32;
                fn check(t: &T, alt: &T, ty: NumType, env: &impl Fn(&str) -> u64) {
                    assert_eq!(eval(t, ty, env), eval(alt, ty, env), "{}\n{}", show(t), show(alt));
                }
                if bits == 8 && vars.len() == 2 {
                    (0..1u64 << 16).for_each(|p| check(&t, &alt, ty, &|v: &str| if v == "x" { p & 0xff } else { p >> 8 }));
                } else {
                    for _ in 0..256 {
                        let env: HashMap<String, u64> = VARS.iter().map(|v| (v.to_string(), r.next())).collect();
                        check(&t, &alt, ty, &|v: &str| env[v]);
                    }
                }
            }
        }
        assert!(changed > 20, "only {changed} relations fired");
    })
}

#[test]
fn sum_size_matches_build_sum() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x9e3779b97f4a7c15);
        for w in [8u32, 64] {
            let wd = Ctx::new(w);
            let coef = |r: &mut Rng| [1, wd.mask, 2, wd.mask - 1, 1 << (w - 1), r.next() & wd.mask][(r.next() % 6) as usize];
            for _ in 0..3000 {
                let mut terms = Vec::new();
                for _ in 0..r.next() % 4 {
                    let (c, depth) = (coef(&mut r), (r.next() % 3) as u32);
                    terms.push((c, random_term(&mut r, depth)));
                }
                let konst = match r.next() % 3 {
                    0 => 0,
                    1 => terms.first().map_or(1, |t| t.0),
                    _ => coef(&mut r),
                };
                assert_eq!(sum_size(&terms, konst, &wd), size(&build_sum(&terms, konst, &wd)), "{terms:?} {konst}");
            }
        }
    })
}

#[test]
fn peel_preserves_value() {
    crate::sched::in_default_run(|| {
        let op = |o: Op, a: Vec<T>| T::Op(o, a);
        let var = |s: &str| T::Var(s.into());
        let lv = [var("x"), var("y"), var("z"), var("u"), op(Op::Mul, vec![var("a"), var("b")]), op(Op::Add, vec![var("c"), var("x")]), var("v"), var("w")];
        fn bit_term(r: &mut Rng, depth: u32, lv: &[T]) -> T {
            if depth == 0 {
                return match r.next() % 8 {
                    0 => T::Num([0x55, -0x10, 0x3c][(r.next() % 3) as usize]),
                    _ => lv[(r.next() % lv.len() as u64) as usize].clone(),
                };
            }
            let ops = [Op::And, Op::Or, Op::Xor, Op::Not];
            match ops[(r.next() % 4) as usize] {
                Op::Not => T::Op(Op::Not, vec![bit_term(r, depth - 1, lv)]),
                o => T::Op(o, vec![bit_term(r, depth - 1, lv), bit_term(r, depth - 1, lv)]),
            }
        }
        // A linear sum equal to the bitwise `t`, its outer operations written arithmetically.
        fn lin(t: &T) -> T {
            let op = |o: Op, a: Vec<T>| T::Op(o, a);
            match t {
                T::Op(Op::Or, a) => op(Op::Sub, vec![op(Op::Add, vec![a[0].clone(), lin(&a[1])]), op(Op::And, a.clone())]),
                T::Op(Op::And, a) => op(Op::Sub, vec![op(Op::Add, vec![a[0].clone(), lin(&a[1])]), op(Op::Or, a.clone())]),
                T::Op(Op::Xor, a) => op(Op::Sub, vec![op(Op::Add, vec![a[0].clone(), lin(&a[1])]), op(Op::Mul, vec![T::Num(2), op(Op::And, a.clone())])]),
                T::Op(Op::Not, a) => op(Op::Sub, vec![op(Op::Neg, vec![lin(&a[0])]), T::Num(1)]),
                _ => t.clone(),
            }
        }
        let mut r = Rng(0x7e1e_0ff5_0123_4567);
        let mut peeled = 0;
        for k in 0..200 {
            let w = Ctx::new(if k % 2 == 0 { 8 } else { 64 });
            let mut f = bit_term(&mut r, 4, &lv[..6]);
            for l in &lv[6..] {
                let l = if r.next() % 3 == 0 { op(Op::Not, vec![l.clone()]) } else { l.clone() };
                f = op([Op::And, Op::Or, Op::Xor][(r.next() % 3) as usize], vec![l, f]);
            }
            let t = lin(&f);
            let Some(p) = peel(&t, &w) else { continue };
            peeled += 1;
            for _ in 0..200 {
                let env: HashMap<String, u64> = ["a", "b", "c", "x", "y", "z", "u", "v", "w"].iter().map(|s| (s.to_string(), r.next() & w.mask)).collect();
                assert_eq!(full_eval(&t, &w, &env), full_eval(&p, &w, &env), "{}\n{}", show(&t), show(&p));
            }
        }
        assert!(peeled > 30, "peeled {peeled}");
    })
}

#[test]
fn split_bits_and_wide_regions_preserve_value() {
    let op = |o: Op, a: Vec<T>| T::Op(o, a);
    let mut r = Rng(0x0bad_5eed_1234_5678);
    let ty = NumType { bits: 8, signed: false };
    let mut changed = 0;
    for k in 0..30 {
        let t = if k % 3 == 2 {
            let wide = ["x", "y", "a", "b", "c", "d", "e"];
            let bit = random_term_in(&mut r, 3, &wide);
            op(Op::Add, vec![random_term_in(&mut r, 2, &["x", "y"]), op(Op::Mul, vec![T::Num(0x35), bit])])
        } else {
            (0..2 + r.next() % 2)
                .map(|_| {
                    let a = random_term_in(&mut r, 1, &["x", "y"]);
                    let sel = match r.next() % 4 {
                        0 => op(Op::And, vec![a, T::Num(1)]),
                        1 => op(Op::And, vec![op(Op::Not, vec![a]), T::Num(1)]),
                        2 => op(Op::And, vec![a, T::Num(2)]),
                        _ => op(Op::Not, vec![op(Op::Or, vec![a, T::Num(-3)])]),
                    };
                    op(Op::Mul, vec![sel, random_term_in(&mut r, 2, &["x", "y"])])
                })
                .reduce(|a, b| op(Op::Add, vec![a, b]))
                .unwrap()
        };
        let alt = parse(&simplify_linear(&show(&t), 8));
        if alt == t {
            continue;
        }
        changed += 1;
        let mut names = crate::eval::vars(&t);
        names.extend(crate::eval::vars(&alt));
        for p in (0..1u64 << 16).step_by(3) {
            let env = |v: &str| match v {
                "x" => p & 0xff,
                "y" => p >> 8,
                _ => (p.wrapping_mul(0x9e37_79b9) >> (names.iter().position(|n| n == v).unwrap() * 3)) & 0xff,
            };
            assert_eq!(eval(&t, ty, &env), eval(&alt, ty, &env), "{}\n{}", show(&t), show(&alt));
        }
    }
    assert!(changed > 10, "changed {changed}");
}

#[test]
fn recombined_products_preserve_value() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x1234_5678_9abc_def1);
        let mut changed = 0;
        for k in 0..300 {
            let bits = if k % 2 == 0 { 8 } else { 64 };
            let w = Ctx::new(bits);
            let op = |o: Op, a: Vec<T>| T::Op(o, a);
            let (a, b) = (random_term_in(&mut r, 2, &["x", "y", "z"]), random_term_in(&mut r, 2, &["x", "y", "z"]));
            let b = if k % 3 == 0 { op(Op::And, vec![b, T::Num((r.next() % 64) as i64)]) } else { b };
            let not = |t: &T| op(Op::Not, vec![t.clone()]);
            let t = op(
                Op::Add,
                vec![
                    op(Op::Mul, vec![op(Op::Or, vec![a.clone(), b.clone()]), op(Op::And, vec![a.clone(), b.clone()])]),
                    op(Op::Mul, vec![op(Op::And, vec![a.clone(), not(&b)]), op(Op::And, vec![not(&a), b.clone()])]),
                ],
            );
            let Some(alt) = recombine_products(&t, &w) else { continue };
            changed += 1;
            for _ in 0..64 {
                let env: HashMap<String, u64> = ["x", "y", "z"].iter().map(|v| (v.to_string(), r.next())).collect();
                assert_eq!(full_eval(&t, &w, &env), full_eval(&alt, &w, &env), "{t:?}\n{alt:?}");
            }
        }
        assert!(changed > 100, "changed {changed}");
    })
}

#[test]
fn memoized_rewrites_do_not_depend_on_earlier_settings() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x9e3779b97f4a7c15);
        let mut restricted_differs = 0;
        for w in [8u32, 32] {
            for _ in 0..1500 {
                let depth = 2 + (r.next() % 3) as u32;
                let t = random_term_in(&mut r, depth, &VARS[..4]);
                let shared = Ctx::new(w);
                let narrow = crate::sched::in_scope(|| {
                    crate::sched::bind(crate::sched::SEMI_LEAVES, 2);
                    crate::sched::bind(crate::sched::RELATE_LEAVES, 2);
                    (rewrite(&t, &shared), relate(&t, &shared))
                });
                crate::sched::with_off(&["semi/shapes", "rebuild_values", "common_multiple"], || (rewrite(&t, &shared), relate(&t, &shared)));
                crate::sched::in_scope(|| {
                    crate::sched::bind(crate::sched::REWRITES, 2);
                    rewrite(&t, &shared)
                });
                let again = (rewrite(&t, &shared), relate(&t, &shared));
                let fresh = Ctx::new(w);
                let alone = (rewrite(&t, &fresh), relate(&t, &fresh));
                assert_eq!(again, alone, "w={w} {}", show(&t));
                restricted_differs += (narrow != alone) as usize;
            }
        }
        assert!(restricted_differs > 20, "only {restricted_differs} restricted runs differ");
    })
}

#[test]
fn rewrite_preserves_value() {
    crate::sched::in_default_run(|| {
        let mut r = Rng(0x2545f4914f6cdd1d);
        let mut changed = 0;
        for w in [8u32, 16, 32, 64] {
            let wd = Ctx::new(w);
            for _ in 0..3000 {
                let depth = 1 + (r.next() % 4) as u32;
                let t = random_term(&mut r, depth);
                let alt = rewrite(&t, &wd);
                if alt != t {
                    changed += 1;
                }
                for _ in 0..64 {
                    let env: HashMap<String, u64> =
                        VARS.iter().map(|v| (v.to_string(), r.next())).collect();
                    assert_eq!(
                        full_eval(&t, &wd, &env),
                        full_eval(&alt, &wd, &env),
                        "w={w}\n  {}\n  {}\n  env={env:?}",
                        show(&t),
                        show(&alt)
                    );
                }
            }
        }
        assert!(changed > 1000, "only {changed} rewrites fired");
    })
}

fn b_eval(b: &B, p: usize) -> bool {
    match b {
        B::V(i) => p >> i & 1 == 1,
        B::Not(x) => !b_eval(x, p),
        B::Bin(op, x, y) => {
            let (x, y) = (b_eval(x, p), b_eval(y, p));
            match *op {
                Op::And => x & y,
                Op::Or => x | y,
                _ => x ^ y,
            }
        }
    }
}

fn b_size(b: &B) -> usize {
    match b {
        B::V(_) => 1,
        B::Not(x) => 1 + b_size(x),
        B::Bin(_, x, y) => 1 + b_size(x) + b_size(y),
    }
}

#[test]
fn bool_expr_cache_keeps_decompose_values_apart() {
    // `((w ^ x) | (x & y)) & ~(y ^ z)` over variables 0..4, which `decompose` splits.
    let tt = (0..16usize).filter(|&p| ((p ^ p >> 1) | (p >> 1 & p >> 2)) & !(p >> 2 ^ p >> 3) & 1 == 1).fold(0u64, |t, p| t | 1 << p);
    let cost = |spec: &str| {
        let p = crate::sched::Passes::parse(spec).unwrap();
        crate::pipe::in_run(&p, None, || crate::pipe::Cand::new("(Var \"x\")", "input"), || {
            let BE::E(c, _) = bool_expr_canon(tt, 4) else { panic!("not constant") };
            (c, bool_expr_cached_now(tt, 4))
        })
    };
    let (split, _) = cost("");
    assert_eq!(split, 12);
    let (plain, _) = cost("decompose_max_vars=3");
    assert!(plain > split, "{plain} without decompose");
    assert_eq!(cost(""), (split, true), "the entry under the default values is still there");
    assert_eq!(cost("decompose_max_vars=3"), (plain, true));
}

#[test]
fn bool_expr_matches_table() {
    crate::sched::in_default_run(|| {
        let check = |n: usize, tt: u64| {
            let vars: Vec<usize> = (0..n).collect();
            let BE::E(cost, b) = bool_expr(tt, &vars) else { panic!("n={n} table {tt:#x} not found") };
            assert_eq!(cost, b_size(&b), "n={n} table {tt:#x}: wrong cost");
            for p in 0..1usize << n {
                assert_eq!(b_eval(&b, p), tt >> p & 1 == 1, "n={n} table {tt:#x} point {p}");
            }
        };
        for n in 1..=4usize {
            for tt in 1..table_full(n) {
                check(n, tt);
            }
        }
        let mut r = Rng(0x853c49e6748fea9b);
        for n in 5..=TABLE_LEAVES {
            for _ in 0..3000 {
                let tt = r.next() & table_full(n);
                if tt != 0 && tt != table_full(n) {
                    check(n, tt);
                }
            }
        }
    })
}
