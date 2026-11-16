//! Linear MBA simplification (SiMBA-style). A linear MBA, i.e. a sum of
//! constant multiples of bitwise functions, is fully determined by its values
//! on {0,1}^n, so it can be rebuilt from those values in a minimal form.
//! Subterms that are not linear (`x*y`, `x & 0xff`, `x >> 3`, ...) are treated
//! as opaque variables; the identity holds for any value they take.

use std::sync::OnceLock;

#[derive(Clone, Debug, PartialEq)]
enum T {
    Num(i64),
    Var(String),
    Op(String, Vec<T>),
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    /// Bitwise function of the leaves.
    Bit,
    /// Linear combination of bitwise functions.
    Lin,
    /// Not linear: an opaque leaf for the enclosing region.
    Atom,
}

fn parse(s: &str) -> T {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        if ch == '(' || ch == ')' || ch.is_whitespace() {
            if !cur.is_empty() {
                toks.push(std::mem::take(&mut cur));
            }
            if ch != ' ' && !ch.is_whitespace() {
                toks.push(ch.to_string());
            }
        } else {
            cur.push(ch);
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    let mut i = 0;
    parse_at(&toks, &mut i)
}

fn parse_at(t: &[String], i: &mut usize) -> T {
    assert_eq!(t[*i], "(", "expected '(' in egglog term");
    let head = t[*i + 1].clone();
    *i += 2;
    let node = match head.as_str() {
        "Num" => {
            let v = t[*i].parse().expect("bad Num literal");
            *i += 1;
            T::Num(v)
        }
        "Var" => {
            let v = t[*i].trim_matches('"').to_string();
            *i += 1;
            T::Var(v)
        }
        _ => {
            let mut args = Vec::new();
            while t[*i] != ")" {
                args.push(parse_at(t, i));
            }
            T::Op(head, args)
        }
    };
    *i += 1;
    node
}

fn show(t: &T) -> String {
    match t {
        T::Num(v) => format!("(Num {v})"),
        T::Var(v) => format!("(Var \"{v}\")"),
        T::Op(op, args) => {
            let parts: Vec<String> = args.iter().map(show).collect();
            format!("({op} {})", parts.join(" "))
        }
    }
}

fn size(t: &T) -> usize {
    match t {
        T::Op(_, args) => 1 + args.iter().map(size).sum::<usize>(),
        _ => 1,
    }
}

struct Width {
    w: u32,
    mask: u64,
}

impl Width {
    fn new(w: u32) -> Width {
        Width { w, mask: if w == 64 { u64::MAX } else { (1u64 << w) - 1 } }
    }
    fn signed(&self, v: u64) -> i64 {
        let sh = 64 - self.w;
        ((v << sh) as i64) >> sh
    }
}

fn const_shift(t: &T, w: &Width) -> Option<u32> {
    match t {
        T::Num(k) if (0..w.w as i64).contains(k) => Some(*k as u32),
        _ => None,
    }
}

fn kind(t: &T, w: &Width) -> Kind {
    let bit = |k: Kind| if k == Kind::Atom { Kind::Bit } else { k };
    match t {
        T::Var(_) => Kind::Bit,
        T::Num(c) => {
            let c = *c as u64 & w.mask;
            if c == 0 || c == w.mask { Kind::Bit } else { Kind::Lin }
        }
        T::Op(op, a) => match op.as_str() {
            "Not" => bit(kind(&a[0], w)),
            "Neg" | "Add" | "Sub" => Kind::Lin,
            "And" | "Or" | "Xor" => {
                if bit(kind(&a[0], w)) == Kind::Bit && bit(kind(&a[1], w)) == Kind::Bit {
                    Kind::Bit
                } else {
                    Kind::Atom
                }
            }
            "Mul" if matches!(a[0], T::Num(_)) || matches!(a[1], T::Num(_)) => Kind::Lin,
            "Shl" if const_shift(&a[1], w).is_some() => Kind::Lin,
            _ => Kind::Atom,
        },
    }
}

/// Leaves of the linear region rooted at `t`: variables and atom subterms.
fn leaves(t: &T, w: &Width, out: &mut Vec<T>) {
    match t {
        T::Num(_) => {}
        T::Var(_) => {
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
        T::Op(_, a) => {
            if kind(t, w) == Kind::Atom {
                if !out.contains(t) {
                    out.push(t.clone());
                }
            } else {
                a.iter().for_each(|x| leaves(x, w, out));
            }
        }
    }
}

fn eval(t: &T, w: &Width, leaf_vals: &[(T, u64)]) -> u64 {
    if let Some((_, v)) = leaf_vals.iter().find(|(l, _)| l == t) {
        return *v;
    }
    let m = w.mask;
    let e = |x: &T| eval(x, w, leaf_vals);
    match t {
        T::Num(c) => *c as u64 & m,
        T::Var(_) => unreachable!("variable missing from leaves"),
        T::Op(op, a) => {
            let r = match op.as_str() {
                "Not" => !e(&a[0]),
                "Neg" => e(&a[0]).wrapping_neg(),
                "Add" => e(&a[0]).wrapping_add(e(&a[1])),
                "Sub" => e(&a[0]).wrapping_sub(e(&a[1])),
                "Mul" => e(&a[0]).wrapping_mul(e(&a[1])),
                "And" => e(&a[0]) & e(&a[1]),
                "Or" => e(&a[0]) | e(&a[1]),
                "Xor" => e(&a[0]) ^ e(&a[1]),
                "Shl" => e(&a[0]) << const_shift(&a[1], w).unwrap(),
                _ => unreachable!("non-linear op {op} inside a linear region"),
            };
            r & m
        }
    }
}

#[derive(Clone)]
enum B {
    V(usize),
    Not(Box<B>),
    Bin(&'static str, Box<B>, Box<B>),
}

/// Smallest bitwise expression for every truth table over `n` variables.
/// Table bit `p` is the value at the point whose bit `i` is variable `i`.
fn bool_table(n: usize) -> &'static [Option<(usize, B)>] {
    static TABLES: [OnceLock<Vec<Option<(usize, B)>>>; 4] =
        [OnceLock::new(), OnceLock::new(), OnceLock::new(), OnceLock::new()];
    TABLES[n].get_or_init(|| {
        let pts = 1usize << n;
        let full = (1usize << pts) - 1;
        let mut best: Vec<Option<(usize, B)>> = vec![None; full + 1];
        for i in 0..n {
            let tt = (0..pts).filter(|p| p >> i & 1 == 1).fold(0, |acc, p| acc | 1 << p);
            best[tt] = Some((1, B::V(i)));
        }
        loop {
            let known: Vec<(usize, usize, B)> = best
                .iter()
                .enumerate()
                .filter_map(|(tt, e)| e.as_ref().map(|(c, b)| (tt, *c, b.clone())))
                .collect();
            let mut changed = false;
            let mut offer = |best: &mut Vec<Option<(usize, B)>>, tt: usize, c: usize, b: B| {
                if best[tt].as_ref().is_none_or(|(old, _)| c < *old) {
                    best[tt] = Some((c, b));
                    changed = true;
                }
            };
            for (ta, ca, ba) in &known {
                offer(&mut best, !ta & full, ca + 1, B::Not(Box::new(ba.clone())));
                for (tb, cb, bb) in &known {
                    if ta > tb {
                        continue;
                    }
                    let c = ca + cb + 1;
                    for (op, tt) in [("And", ta & tb), ("Or", ta | tb), ("Xor", ta ^ tb)] {
                        offer(&mut best, tt, c, B::Bin(op, Box::new(ba.clone()), Box::new(bb.clone())));
                    }
                }
            }
            if !changed {
                break best;
            }
        }
    })
}

#[derive(Clone)]
enum BE {
    Zero,
    Ones,
    E(usize, B),
}

/// Largest region (in leaves) that gets rebuilt; truth tables are `u64`.
const MAX_LEAVES: usize = 6;

fn remap(b: &B, vars: &[usize]) -> B {
    match b {
        B::V(i) => B::V(vars[*i]),
        B::Not(x) => B::Not(Box::new(remap(x, vars))),
        B::Bin(op, x, y) => B::Bin(op, Box::new(remap(x, vars)), Box::new(remap(y, vars))),
    }
}

/// Short bitwise expression for truth table `tt` over `vars` (table bit `p`
/// is the value where bit `j` of `p` is `vars[j]`). Exact table lookup up to 3
/// variables; above that, Shannon expansion on the best variable.
fn bool_expr(tt: u64, vars: &[usize]) -> BE {
    match bool_expr_canon(tt, vars.len()) {
        BE::E(c, b) => BE::E(c, remap(&b, vars)),
        other => other,
    }
}

fn table_full(n: usize) -> u64 {
    if n >= 6 { u64::MAX } else { (1u64 << (1 << n)) - 1 }
}

/// `bool_expr` over variables `0..n`, cached.
fn bool_expr_canon(tt: u64, n: usize) -> BE {
    thread_local! {
        static CACHE: std::cell::RefCell<std::collections::HashMap<(u64, usize), BE>> = Default::default();
    }
    if let Some(r) = CACHE.with(|c| c.borrow().get(&(tt, n)).cloned()) {
        return r;
    }
    let r = bool_expr_uncached(tt, n);
    CACHE.with(|c| c.borrow_mut().insert((tt, n), r.clone()));
    r
}

fn bool_expr_uncached(tt: u64, n: usize) -> BE {
    let pts = 1usize << n;
    if tt == 0 {
        return BE::Zero;
    }
    if tt == table_full(n) {
        return BE::Ones;
    }
    if n <= 3 {
        let (c, b) = bool_table(n)[tt as usize].as_ref().expect("non-constant table");
        return BE::E(*c, b.clone());
    }
    let not = |b: B| B::Not(Box::new(b));
    let bin = |op, x: B, y: B| B::Bin(op, Box::new(x), Box::new(y));
    let mut best: Option<(usize, B)> = None;
    for i in 0..n {
        let rest: Vec<usize> = (0..n).filter(|&j| j != i).collect();
        let (mut f0, mut f1) = (0u64, 0u64);
        for p in 0..pts {
            if tt >> p & 1 == 1 {
                let q = (p & ((1 << i) - 1)) | (p >> (i + 1) << i);
                if p >> i & 1 == 0 { f0 |= 1 << q } else { f1 |= 1 << q }
            }
        }
        let x = B::V(i);
        let sub_full = table_full(n - 1);
        let cand = match (bool_expr(f0, &rest), bool_expr(f1, &rest)) {
            (BE::Zero, BE::Ones) => (1, x),
            (BE::Ones, BE::Zero) => (2, not(x)),
            (BE::Zero, BE::E(c, e)) => (c + 2, bin("And", x, e)),
            (BE::E(c, e), BE::Zero) => (c + 3, bin("And", not(x), e)),
            (BE::Ones, BE::E(c, e)) => (c + 3, bin("Or", not(x), e)),
            (BE::E(c, e), BE::Ones) => (c + 2, bin("Or", x, e)),
            (BE::E(c, e), _) if f0 == f1 => (c, e),
            (BE::E(c, e), _) if f1 == !f0 & sub_full => (c + 2, bin("Xor", x, e)),
            (BE::E(c0, e0), BE::E(c1, e1)) => {
                let mux = (c0 + c1 + 6, bin("Or", bin("And", x.clone(), e1), bin("And", not(x.clone()), e0.clone())));
                match bool_expr(f0 ^ f1, &rest) {
                    BE::E(cd, d) if c0 + cd + 3 < mux.0 => (c0 + cd + 3, bin("Xor", e0, bin("And", x, d))),
                    _ => mux,
                }
            }
            (BE::Zero, BE::Zero) | (BE::Ones, BE::Ones) => unreachable!("tt is not constant"),
        };
        if best.as_ref().is_none_or(|(c, _)| cand.0 < *c) {
            best = Some(cand);
        }
    }
    let (c, b) = best.unwrap();
    BE::E(c, b)
}

fn b_to_t(b: &B, leaves: &[T]) -> T {
    match b {
        B::V(i) => leaves[*i].clone(),
        B::Not(x) => T::Op("Not".into(), vec![b_to_t(x, leaves)]),
        B::Bin(op, x, y) => T::Op(op.to_string(), vec![b_to_t(x, leaves), b_to_t(y, leaves)]),
    }
}

/// `Σ coef·term + konst`, using Sub/Neg for negative coefficients.
fn build_sum(terms: &[(u64, T)], konst: u64, w: &Width) -> T {
    let num = |v: u64| T::Num(w.signed(v));
    let scaled = |c: u64, t: &T| if c == 1 { t.clone() } else { T::Op("Mul".into(), vec![num(c), t.clone()]) };
    let mut acc: Option<T> = None;
    for (c, t) in terms {
        let neg = w.signed(*c) < 0 && *c != 1u64 << (w.w - 1);
        acc = Some(match acc {
            None if neg => T::Op("Neg".into(), vec![scaled(c.wrapping_neg() & w.mask, t)]),
            None => scaled(*c, t),
            Some(a) if neg => T::Op("Sub".into(), vec![a, scaled(c.wrapping_neg() & w.mask, t)]),
            Some(a) => T::Op("Add".into(), vec![a, scaled(*c, t)]),
        });
    }
    match acc {
        None => num(konst),
        Some(a) if konst == 0 => a,
        Some(a) if w.signed(konst) < 0 => T::Op("Sub".into(), vec![a, num(konst.wrapping_neg() & w.mask)]),
        Some(a) => T::Op("Add".into(), vec![a, num(konst)]),
    }
}

/// Smallest rebuilt form of the linear region `t`, if it has 1..=MAX_LEAVES leaves.
fn simba(t: &T, w: &Width) -> Option<T> {
    let mut lv = Vec::new();
    leaves(t, w, &mut lv);
    let n = lv.len();
    if n == 0 || n > MAX_LEAVES {
        return None;
    }
    let pts = 1usize << n;
    let m = w.mask;
    let vals: Vec<u64> = (0..pts)
        .map(|p| {
            let env: Vec<(T, u64)> = lv.iter().enumerate().map(|(i, l)| (l.clone(), (p >> i & 1) as u64)).collect();
            eval(t, w, &env)
        })
        .collect();
    // e(x) = Σ_j 2^j g(bit j of x), with g(p) = e(p) - 2e(0); k = g(0).
    let g: Vec<u64> = vals.iter().map(|v| v.wrapping_sub(vals[0].wrapping_mul(2)) & m).collect();
    let k = g[0];
    let gp: Vec<u64> = g.iter().map(|v| v.wrapping_sub(k) & m).collect();
    let konst = k.wrapping_neg() & m;
    let all_vars: Vec<usize> = (0..n).collect();
    let mut best: Option<T> = None;
    for subset in 0..(1usize << n) {
        let mut terms = Vec::new();
        let mut r = gp.clone();
        for i in (0..n).filter(|i| subset >> i & 1 == 1) {
            let c = gp[1 << i];
            if c == 0 {
                continue;
            }
            terms.push((c, lv[i].clone()));
            for (p, rv) in r.iter_mut().enumerate() {
                if p >> i & 1 == 1 {
                    *rv = rv.wrapping_sub(c) & m;
                }
            }
        }
        let mut distinct: Vec<u64> = r.iter().copied().filter(|&u| u != 0).collect();
        distinct.sort_unstable();
        distinct.dedup();
        for u in distinct {
            let tt = (0..pts).filter(|&p| r[p] == u).fold(0u64, |acc, p| acc | 1 << p);
            let BE::E(_, b) = bool_expr(tt, &all_vars) else {
                unreachable!("r[0] == 0, so the table is neither empty nor full")
            };
            terms.push((u, b_to_t(&b, &lv)));
        }
        let cand = build_sum(&terms, konst, w);
        if best.as_ref().is_none_or(|b| size(&cand) < size(b)) {
            best = Some(cand);
        }
    }
    best.filter(|b| size(b) < size(t))
}

/// Replace every linear region (and, recursively, regions inside atoms) by its
/// rebuilt form when that is smaller.
fn rewrite(t: &T, w: &Width) -> T {
    let T::Op(op, args) = t else { return t.clone() };
    if kind(t, w) != Kind::Atom {
        if let Some(best) = simba(t, w) {
            return substitute_atoms(&best, w);
        }
    }
    T::Op(op.clone(), args.iter().map(|a| rewrite(a, w)).collect())
}

/// Rewrite inside the atom leaves of a rebuilt region.
fn substitute_atoms(t: &T, w: &Width) -> T {
    match t {
        T::Op(op, args) => {
            if kind(t, w) == Kind::Atom {
                rewrite(t, w)
            } else {
                T::Op(op.clone(), args.iter().map(|a| substitute_atoms(a, w)).collect())
            }
        }
        _ => t.clone(),
    }
}

/// Rewrite the egglog term `egg` (W-bit wrapping semantics) with every linear
/// MBA region of at most `MAX_LEAVES` leaves rebuilt in a smaller form. Returns `egg`
/// unchanged when nothing gets smaller.
pub fn simplify_linear(egg: &str, w: u32) -> String {
    let w = Width::new(w);
    let t = parse(egg);
    let r = rewrite(&t, &w);
    if r == t { egg.to_string() } else { show(&r) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn full_eval(t: &T, w: &Width, env: &HashMap<String, u64>) -> u64 {
        let m = w.mask;
        let e = |x: &T| full_eval(x, w, env);
        let r = match t {
            T::Num(c) => *c as u64,
            T::Var(v) => env[v],
            T::Op(op, a) => match op.as_str() {
                "Not" => !e(&a[0]),
                "Neg" => e(&a[0]).wrapping_neg(),
                "Add" => e(&a[0]).wrapping_add(e(&a[1])),
                "Sub" => e(&a[0]).wrapping_sub(e(&a[1])),
                "Mul" => e(&a[0]).wrapping_mul(e(&a[1])),
                "And" => e(&a[0]) & e(&a[1]),
                "Or" => e(&a[0]) | e(&a[1]),
                "Xor" => e(&a[0]) ^ e(&a[1]),
                "Shl" | "Shr" => {
                    let k = e(&a[1]);
                    if k >= w.w as u64 {
                        0
                    } else if op == "Shl" {
                        e(&a[0]) << k
                    } else {
                        (e(&a[0]) & m) >> k
                    }
                }
                _ => unreachable!(),
            },
        };
        r & m
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
        let var = |r: &mut Rng| T::Var(VARS[(r.next() % VARS.len() as u64) as usize].into());
        if depth == 0 {
            return match r.next() % 6 {
                0 => T::Num((r.next() % 7) as i64 - 3),
                _ => var(r),
            };
        }
        let sub = |r: &mut Rng| random_term(r, depth - 1);
        match r.next() % 12 {
            0 => T::Op("Not".into(), vec![sub(r)]),
            1 => T::Op("Neg".into(), vec![sub(r)]),
            2 | 3 => T::Op("Add".into(), vec![sub(r), sub(r)]),
            4 => T::Op("Sub".into(), vec![sub(r), sub(r)]),
            5 => T::Op("Mul".into(), vec![T::Num((r.next() % 9) as i64 - 4), sub(r)]),
            6 => T::Op("And".into(), vec![sub(r), sub(r)]),
            7 => T::Op("Or".into(), vec![sub(r), sub(r)]),
            8 => T::Op("Xor".into(), vec![sub(r), sub(r)]),
            9 => T::Op("Mul".into(), vec![sub(r), sub(r)]),
            10 => T::Op("Shl".into(), vec![sub(r), T::Num((r.next() % 10) as i64)]),
            _ => T::Op("Shr".into(), vec![sub(r), T::Num((r.next() % 4) as i64)]),
        }
    }

    #[test]
    fn rewrite_preserves_value() {
        let mut r = Rng(0x2545f4914f6cdd1d);
        let mut changed = 0;
        for w in [8u32, 16, 32, 64] {
            let wd = Width::new(w);
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
    }

    fn b_eval(b: &B, p: usize) -> bool {
        match b {
            B::V(i) => p >> i & 1 == 1,
            B::Not(x) => !b_eval(x, p),
            B::Bin(op, x, y) => {
                let (x, y) = (b_eval(x, p), b_eval(y, p));
                match *op {
                    "And" => x & y,
                    "Or" => x | y,
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
    fn bool_expr_matches_table() {
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
        for n in 5..=MAX_LEAVES {
            for _ in 0..3000 {
                let tt = r.next() & table_full(n);
                if tt != 0 && tt != table_full(n) {
                    check(n, tt);
                }
            }
        }
    }
}
