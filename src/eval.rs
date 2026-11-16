//! Egglog `Expr` terms as a tree, with concrete evaluation that matches the
//! `wrapping-<op>-<type>` primitives in `lib.rs`.

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Num(i64),
    Var(String),
    Op(String, Vec<Term>),
}

/// Parse an egglog term such as `(Add (Var "x") (Num 1))`. Panics on malformed input.
pub fn parse(s: &str) -> Term {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        if ch == '(' || ch == ')' || ch.is_whitespace() {
            if !cur.is_empty() {
                toks.push(std::mem::take(&mut cur));
            }
            if !ch.is_whitespace() {
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

fn parse_at(t: &[String], i: &mut usize) -> Term {
    assert_eq!(t[*i], "(", "expected '(' in egglog term");
    let head = t[*i + 1].clone();
    *i += 2;
    let node = match head.as_str() {
        "Num" => {
            let v = t[*i].parse().expect("bad Num literal");
            *i += 1;
            Term::Num(v)
        }
        "Var" => {
            let v = t[*i].trim_matches('"').to_string();
            *i += 1;
            Term::Var(v)
        }
        _ => {
            let mut args = Vec::new();
            while t[*i] != ")" {
                args.push(parse_at(t, i));
            }
            Term::Op(head, args)
        }
    };
    *i += 1;
    node
}

pub fn show(t: &Term) -> String {
    match t {
        Term::Num(v) => format!("(Num {v})"),
        Term::Var(v) => format!("(Var \"{v}\")"),
        Term::Op(op, args) => {
            let parts: Vec<String> = args.iter().map(show).collect();
            format!("({op} {})", parts.join(" "))
        }
    }
}

/// Number of nodes.
pub fn size(t: &Term) -> usize {
    match t {
        Term::Op(_, args) => 1 + args.iter().map(size).sum::<usize>(),
        _ => 1,
    }
}

/// Distinct variable names, in order of first occurrence.
pub fn vars(t: &Term) -> Vec<String> {
    fn go(t: &Term, out: &mut Vec<String>) {
        match t {
            Term::Var(v) if !out.contains(v) => out.push(v.clone()),
            Term::Op(_, args) => args.iter().for_each(|a| go(a, out)),
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(t, &mut out);
    out
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct NumType {
    pub bits: u32,
    pub signed: bool,
}

impl NumType {
    /// `"i64"`, `"u8"`, ... as accepted by `Cli::num_type`.
    pub fn from_name(name: &str) -> Option<NumType> {
        let signed = match name.as_bytes().first()? {
            b'i' => true,
            b'u' => false,
            _ => return None,
        };
        let bits = name[1..].parse().ok()?;
        matches!(bits, 8 | 16 | 32 | 64).then_some(NumType { bits, signed })
    }

    pub fn mask(&self) -> u64 {
        if self.bits == 64 { u64::MAX } else { (1u64 << self.bits) - 1 }
    }

    fn sext(&self, v: u64) -> i64 {
        let sh = 64 - self.bits;
        ((v << sh) as i64) >> sh
    }
}

/// Value of `t` truncated to `ty.bits` bits, or `None` on division by zero.
pub fn eval(t: &Term, ty: NumType, env: &impl Fn(&str) -> u64) -> Option<u64> {
    let w = ty.bits as u64;
    let r = match t {
        Term::Num(c) => *c as u64,
        Term::Var(v) => env(v),
        Term::Op(op, a) => {
            let x = eval(&a[0], ty, env)?;
            let y = match a.get(1) {
                Some(b) => eval(b, ty, env)?,
                None => 0,
            };
            let (sx, sy) = (ty.sext(x), ty.sext(y));
            match op.as_str() {
                "Add" => x.wrapping_add(y),
                "Sub" => x.wrapping_sub(y),
                "Mul" => x.wrapping_mul(y),
                "And" => x & y,
                "Or" => x | y,
                "Xor" => x ^ y,
                "Not" => !x,
                "Neg" => x.wrapping_neg(),
                "Shl" if y >= w => 0,
                "Shl" => x << y,
                "Shr" if ty.signed => (sx >> y.min(w - 1)) as u64,
                "Shr" if y >= w => 0,
                "Shr" => x >> y,
                "Div" | "Mod" if y == 0 => return None,
                "Div" if ty.signed => sx.wrapping_div(sy) as u64,
                "Div" => x / y,
                "Mod" if ty.signed => sx.wrapping_rem(sy) as u64,
                "Mod" => x % y,
                "Mulhi" if ty.signed => ((sx as i128 * sy as i128) >> w) as u64,
                "Mulhi" => ((x as u128 * y as u128) >> w) as u64,
                _ => panic!("unknown operator {op}"),
            }
        }
    };
    Some(r & ty.mask())
}
