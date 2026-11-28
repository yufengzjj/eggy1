//! Egglog `Expr` terms as a tree, with concrete evaluation that matches the
//! `wrapping-<op>-<type>` primitives in `lib.rs`.

/// Multiply-rotate hasher (as in rustc's FxHash) for the in-memory memo tables, which
/// hash many large terms and never need resistance to chosen keys.
#[derive(Default, Clone, Copy)]
pub(crate) struct FastHasher(u64);

impl FastHasher {
    fn add(&mut self, v: u64) {
        self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl std::hash::Hasher for FastHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut b = [0u8; 8];
            b[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(b) ^ (rest.len() as u64) << 56);
        }
    }
    fn write_u8(&mut self, v: u8) {
        self.add(v as u64);
    }
    fn write_u32(&mut self, v: u32) {
        self.add(v as u64);
    }
    fn write_u64(&mut self, v: u64) {
        self.add(v);
    }
    fn write_usize(&mut self, v: usize) {
        self.add(v as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

pub(crate) type FastMap<K, V> = std::collections::HashMap<K, V, std::hash::BuildHasherDefault<FastHasher>>;
pub(crate) type FastSet<K> = std::collections::HashSet<K, std::hash::BuildHasherDefault<FastHasher>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Num(i64),
    Var(String),
    Op(Op, Vec<Term>),
}

/// An `Expr` constructor other than `Num` and `Var`; `Leaf`, `LeafOperand` and `Slot` are
/// nullary placeholders that `linear_mba` uses internally and never parses. `Slot(i, s)`
/// stands for leaf `i` and counts as `s` nodes in `size`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Mulhi,
    Not,
    Neg,
    Leaf(usize),
    LeafOperand(usize),
    // `u32` keeps `Op` at 16 bytes; a wider payload grows every `Term` node.
    Slot(u32, u32),
}

impl Op {
    const NAMED: [Op; 13] = [
        Op::Add,
        Op::Sub,
        Op::Mul,
        Op::Div,
        Op::Mod,
        Op::And,
        Op::Or,
        Op::Xor,
        Op::Shl,
        Op::Shr,
        Op::Mulhi,
        Op::Not,
        Op::Neg,
    ];

    /// The egglog constructor name; for a placeholder, the prefix `show` puts before its index.
    pub fn name(self) -> &'static str {
        match self {
            Op::Add => "Add",
            Op::Sub => "Sub",
            Op::Mul => "Mul",
            Op::Div => "Div",
            Op::Mod => "Mod",
            Op::And => "And",
            Op::Or => "Or",
            Op::Xor => "Xor",
            Op::Shl => "Shl",
            Op::Shr => "Shr",
            Op::Mulhi => "Mulhi",
            Op::Not => "Not",
            Op::Neg => "Neg",
            Op::Leaf(_) => "\u{2}",
            Op::LeafOperand(_) => "\u{3}",
            Op::Slot(..) => "\u{5}",
        }
    }

    pub fn from_name(name: &str) -> Option<Op> {
        Op::NAMED.into_iter().find(|op| op.name() == name)
    }
}

impl std::fmt::Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Op::Leaf(i) | Op::LeafOperand(i) => write!(f, "{}{i}", self.name()),
            Op::Slot(i, _) => write!(f, "{}{i}", self.name()),
            _ => f.write_str(self.name()),
        }
    }
}

/// Parse an egglog term such as `(Add (Var "x") (Num 1))`. Panics on malformed input or an unknown constructor.
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

/// Why `s` is not an egglog term `parse` reads, if it is not.
pub fn check(s: &str) -> Result<(), String> {
    let toks: Vec<String> = s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
    let mut i = 0;
    check_at(&toks, &mut i)?;
    match toks.get(i) {
        None => Ok(()),
        Some(t) => Err(format!("unexpected '{t}' after the term")),
    }
}

fn check_at(t: &[String], i: &mut usize) -> Result<(), String> {
    let tok = |i: usize| t.get(i).map(String::as_str).ok_or("the term ends early");
    if tok(*i)? != "(" {
        return Err(format!("expected '(', found '{}'", tok(*i)?));
    }
    let head = tok(*i + 1)?;
    *i += 2;
    match head {
        "Num" => {
            tok(*i)?.parse::<i64>().map_err(|_| format!("bad Num literal '{}'", tok(*i).unwrap_or("")))?;
            *i += 1;
        }
        "Var" => {
            let v = tok(*i)?;
            if v == ")" || v == "(" {
                return Err("Var needs a name".into());
            }
            *i += 1;
        }
        _ => {
            Op::from_name(head).ok_or_else(|| format!("unknown constructor {head}"))?;
            let mut n = 0;
            while tok(*i)? != ")" {
                check_at(t, i)?;
                n += 1;
            }
            let want = if matches!(head, "Not" | "Neg") { 1 } else { 2 };
            if n != want {
                return Err(format!("{head} takes {want} operands, found {n}"));
            }
        }
    }
    if tok(*i)? != ")" {
        return Err(format!("expected ')', found '{}'", tok(*i)?));
    }
    *i += 1;
    Ok(())
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
            let op = Op::from_name(&head).unwrap_or_else(|| panic!("unknown constructor {head}"));
            Term::Op(op, args)
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
        Term::Op(Op::Slot(_, s), _) => *s as usize,
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
    match t {
        Term::Num(c) => Some(*c as u64 & ty.mask()),
        Term::Var(v) => Some(env(v) & ty.mask()),
        Term::Op(op, a) => {
            let x = eval(&a[0], ty, env)?;
            let y = match a.get(1) {
                Some(b) => eval(b, ty, env)?,
                None => 0,
            };
            apply(*op, x, y, ty)
        }
    }
}

/// `op` on the operand values `x` and `y` (0 for a unary `op`), or `None` on division by zero.
pub fn apply(op: Op, x: u64, y: u64, ty: NumType) -> Option<u64> {
    let w = ty.bits as u64;
    let (sx, sy) = (ty.sext(x), ty.sext(y));
    let r = match op {
        Op::Add => x.wrapping_add(y),
        Op::Sub => x.wrapping_sub(y),
        Op::Mul => x.wrapping_mul(y),
        Op::And => x & y,
        Op::Or => x | y,
        Op::Xor => x ^ y,
        Op::Not => !x,
        Op::Neg => x.wrapping_neg(),
        Op::Shl if y >= w => 0,
        Op::Shl => x << y,
        Op::Shr if ty.signed => (sx >> y.min(w - 1)) as u64,
        Op::Shr if y >= w => 0,
        Op::Shr => x >> y,
        Op::Div | Op::Mod if y == 0 => return None,
        Op::Div if ty.signed => sx.wrapping_div(sy) as u64,
        Op::Div => x / y,
        Op::Mod if ty.signed => sx.wrapping_rem(sy) as u64,
        Op::Mod => x % y,
        Op::Mulhi if ty.signed => ((sx as i128 * sy as i128) >> w) as u64,
        Op::Mulhi => ((x as u128 * y as u128) >> w) as u64,
        Op::Leaf(_) | Op::LeafOperand(_) | Op::Slot(..) => panic!("unknown operator {op}"),
    };
    Some(r & ty.mask())
}
