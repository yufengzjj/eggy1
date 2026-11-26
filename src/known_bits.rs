//! Known bits of a value in the low `w` bits, shared by the pre-pass (`lowbits`) and the
//! egglog `kz` analysis. `Bits` tracks known zeros and ones; the `kz_*` functions track
//! known zeros alone, as the e-graph stores them, and `Bits` with `k1 = 0` refines them.

/// Bits known to be 0 (`k0`) and known to be 1 (`k1`), both within the width mask.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Bits {
    pub k0: u64,
    pub k1: u64,
}

pub fn lowmask(k: u32) -> u64 {
    if k >= 64 { u64::MAX } else { (1u64 << k) - 1 }
}

impl Bits {
    pub const UNKNOWN: Bits = Bits { k0: 0, k1: 0 };

    pub fn constant(c: u64, w: u32) -> Bits {
        Bits { k0: !c & lowmask(w), k1: c & lowmask(w) }
    }

    /// The value, when every bit is known.
    pub fn value(self, w: u32) -> Option<u64> {
        ((self.k0 | self.k1) & lowmask(w) == lowmask(w)).then_some(self.k1)
    }

    /// Known trailing zeros.
    pub fn tz(self, w: u32) -> u32 {
        self.k0.trailing_ones().min(w)
    }

    /// Largest possible value.
    fn max(self, w: u32) -> u64 {
        !self.k0 & lowmask(w)
    }
}

pub fn not(x: Bits) -> Bits {
    Bits { k0: x.k1, k1: x.k0 }
}

pub fn and(x: Bits, y: Bits) -> Bits {
    Bits { k0: x.k0 | y.k0, k1: x.k1 & y.k1 }
}

pub fn or(x: Bits, y: Bits) -> Bits {
    Bits { k0: x.k0 & y.k0, k1: x.k1 | y.k1 }
}

pub fn xor(x: Bits, y: Bits) -> Bits {
    Bits { k0: x.k0 & y.k0 | x.k1 & y.k1, k1: x.k0 & y.k1 | x.k1 & y.k0 }
}

/// Known bits of `a + b + cin`, bit by bit with the carry known where two of the three inputs agree.
fn add_carry(a: Bits, b: Bits, cin: u64, w: u32) -> Bits {
    let (mut k0, mut k1) = (0, 0);
    let (mut c0, mut c1) = (cin ^ 1, cin);
    for i in 0..w {
        let bit = |k: u64| k >> i & 1;
        let (a0, a1, b0, b1) = (bit(a.k0), bit(a.k1), bit(b.k0), bit(b.k1));
        if (a0 | a1) & (b0 | b1) & (c0 | c1) == 1 {
            let s = a1 ^ b1 ^ c1;
            k0 |= (s ^ 1) << i;
            k1 |= s << i;
        }
        (c0, c1) = (u64::from(a0 + b0 + c0 >= 2), u64::from(a1 + b1 + c1 >= 2));
    }
    Bits { k0, k1 }
}

/// Bits above an upper bound `v` that does not wrap.
fn above(v: Option<u64>, w: u32) -> u64 {
    let m = lowmask(w);
    v.filter(|v| *v <= m).map_or(0, |v| m & !lowmask(64 - v.leading_zeros()))
}

pub fn neg(x: Bits, w: u32) -> Bits {
    add_carry(Bits { k0: lowmask(w), k1: 0 }, not(x), 1, w)
}

pub fn add(x: Bits, y: Bits, w: u32) -> Bits {
    let r = add_carry(x, y, 0, w);
    Bits { k0: r.k0 | above(x.max(w).checked_add(y.max(w)), w), ..r }
}

pub fn sub(x: Bits, y: Bits, w: u32) -> Bits {
    let r = add_carry(x, not(y), 1, w);
    Bits { k0: r.k0 | above((x.k1 >= y.max(w)).then(|| x.max(w) - y.k1), w), ..r }
}

/// `square`: both operands are the same term, so bit 1 is 0 (`a² mod 4` is 0 or 1).
pub fn mul(x: Bits, y: Bits, square: bool, w: u32) -> Bits {
    let l = (x.k0 | x.k1).trailing_ones().min((y.k0 | y.k1).trailing_ones()).min(w);
    let low = x.k1.wrapping_mul(y.k1) & lowmask(l);
    let tzs = lowmask((x.tz(w) + y.tz(w)).min(w));
    let sq = if square { 2 & !low } else { 0 };
    let k0 = !low & lowmask(l) | tzs | sq | above(x.max(w).checked_mul(y.max(w)), w);
    Bits { k0: k0 & lowmask(w), k1: low }
}

/// `a << s` for a known `s`.
pub fn shl(x: Bits, s: u64, w: u32) -> Bits {
    let m = lowmask(w);
    if s >= w as u64 {
        return Bits { k0: m, k1: 0 };
    }
    Bits { k0: (x.k0 << s | lowmask(s as u32)) & m, k1: x.k1 << s & m }
}

/// `a >> s` for a known `s < w`: arithmetic when `signed` is `Some(true)`, logical when
/// `Some(false)`, either when `None` (the high `s` bits then known only as a known-0 sign).
pub fn shr(x: Bits, s: u64, w: u32, signed: Option<bool>) -> Bits {
    let m = lowmask(w);
    let high = m & !(m >> s);
    let sign = |k: u64| if k >> (w - 1) & 1 == 1 { high } else { 0 };
    let (f0, f1) = match signed {
        Some(false) => (high, 0),
        Some(true) => (sign(x.k0), sign(x.k1)),
        None => (sign(x.k0), 0),
    };
    Bits { k0: (x.k0 & m) >> s | f0, k1: (x.k1 & m) >> s | f1 }
}

/// `a << b` for any `b`: the trailing known zeros of `a` stay.
pub fn shl_any(x: Bits, w: u32) -> Bits {
    Bits { k0: lowmask(x.tz(w)), k1: 0 }
}

/// Known-zero mask of `a << k` given known-zero mask `z` of `a`; None unless 0 <= k < w.
pub fn kz_shl(z: i64, k: i64, w: i64) -> Option<i64> {
    (0..w).contains(&k).then(|| (z << k) | lowmask(k as u32) as i64)
}

/// Known-zero mask of `a >> k` (arithmetic if `signed`); None unless 0 <= k < w.
pub fn kz_shr(z: i64, k: i64, w: i64, signed: bool) -> Option<i64> {
    (0..w).contains(&k).then(|| {
        if signed {
            let sh = 64 - w;
            ((z << sh) >> sh) >> k
        } else {
            let m = lowmask(w as u32);
            (((z as u64 & m) >> k) | !(m >> k)) as i64
        }
    })
}

/// Trailing known zeros of `z`, as a mask (kept by `-a` and by `a * b`).
pub fn kz_low(z: i64, w: i64) -> i64 {
    lowmask(z.trailing_ones().min(w as u32)) as i64
}

/// Known-zero mask of `a + b` or `a - b`: the shorter run of trailing known zeros.
pub fn kz_add(za: i64, zb: i64, w: i64) -> i64 {
    lowmask(za.trailing_ones().min(zb.trailing_ones()).min(w as u32)) as i64
}

/// Known-zero mask of `a * b`: trailing known zeros add up.
pub fn kz_mul(za: i64, zb: i64, w: i64) -> i64 {
    lowmask((za.trailing_ones() + zb.trailing_ones()).min(w as u32)) as i64
}
