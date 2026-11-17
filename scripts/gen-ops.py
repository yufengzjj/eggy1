"""Generate cases with shifts, division and mulhi for one numeric type, as
`obfuscated, groundtruth` lines for examples/bench.rs (run it with the same -n).

Sections:
- linear MBA inside a shift, division, remainder or mulhi;
- shift identities ((x >> k) << k, 2^k * x, ...) under MBA noise;
- division by a constant written with a magic multiplier (Hacker's Delight 10);
- terms with disjoint known bits joined by +, | or ^;
- variable shift amounts hidden in MBA.

Semantics follow src/eval.rs: shifts by >= width give 0 (arithmetic right
shift saturates), signed division truncates. Every case is checked on random
and boundary inputs.

Usage: python scripts/gen-ops.py TYPE [cases-per-section] > bench-data/ops_TYPE.txt
"""

import random
import sys

TY = sys.argv[1] if len(sys.argv) > 1 else "u64"
SIGNED = TY[0] == "i"
W = int(TY[1:])
M = (1 << W) - 1


def sx(v):
    v &= M
    return v - (1 << W) if SIGNED and v >> (W - 1) else v


def ev(e, env):
    t = e[0]
    if t == "var":
        return env[e[1]]
    if t == "num":
        return e[1] & M
    if t == "not":
        return ~ev(e[1], env) & M
    if t == "neg":
        return -ev(e[1], env) & M
    a, b = ev(e[1], env), ev(e[2], env)
    if t in ("and", "or", "xor", "add", "sub", "mul"):
        return {"and": a & b, "or": a | b, "xor": a ^ b, "add": a + b, "sub": a - b, "mul": a * b}[t] & M
    if t == "shl":
        return 0 if b >= W else (a << b) & M
    if t == "shr":
        if SIGNED:
            return (sx(a) >> min(b, W - 1)) & M
        return 0 if b >= W else a >> b
    if t == "mulhi":
        return ((sx(a) * sx(b)) >> W) & M
    if b == 0:
        raise ZeroDivisionError
    if SIGNED:
        q = abs(sx(a)) // abs(sx(b))
        q = q if (sx(a) < 0) == (sx(b) < 0) else -q
        return (q if t == "div" else sx(a) - sx(b) * q) & M
    return (a // b if t == "div" else a % b) & M


def bitwise(r, vars, depth):
    if depth == 0:
        return ("var", r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", bitwise(r, vars, depth - 1))
    return (op, bitwise(r, vars, depth - 1), bitwise(r, vars, depth - 1))


def expand(e, r, p):
    t = e[0]
    if r.random() >= p or t not in ("and", "or", "xor", "not"):
        return e
    if t == "not":
        return ("sub", ("neg", expand(e[1], r, p)), ("num", 1))
    a, b = e[1], e[2]
    if t == "and":
        return ("sub", ("add", expand(a, r, p), expand(b, r, p)), ("or", a, b))
    if t == "or":
        return ("sub", ("add", expand(a, r, p), expand(b, r, p)), ("and", a, b))
    return ("sub", ("or", a, b), ("and", a, b))


def sum_tree(terms):
    out = None
    for c, e in terms:
        t = e if abs(c) == 1 else ("mul", ("num", abs(c)), e)
        if out is None:
            out = ("neg", t) if c < 0 else t
        else:
            out = ("sub" if c < 0 else "add", out, t)
    return out


def zero_terms(r, vars, k):
    out = []
    for _ in range(k):
        c = r.choice([1, 2, 3, 5, -1, -2, -3, -7])
        f = bitwise(r, r.sample(vars, min(len(vars), r.choice([2, 3]))), 2)
        out += [(c, f), (-c, expand(f, r, 1.0))]
    return out


def mba(r, e, vars, k):
    """e written as a linear MBA plus k zero pairs."""
    obf = [(1, expand(e, r, 0.9))] + zero_terms(r, vars, k)
    r.shuffle(obf)
    return sum_tree(obf)


def with_noise(r, obf, gt, vars, k=2):
    terms = [(1, obf)] + zero_terms(r, vars, k)
    r.shuffle(terms)
    return sum_tree(terms), gt


def num(v):
    return ("num", v & M)


def show(e):
    t = e[0]
    if t == "var":
        return e[1]
    if t == "num":
        return hex(e[1])
    if t == "not":
        return f"~({show(e[1])})"
    if t == "neg":
        return f"-({show(e[1])})"
    if t == "mulhi":
        return f"mulhi({show(e[1])}, {show(e[2])})"
    sym = {"and": "&", "or": "|", "xor": "^", "add": "+", "sub": "-", "mul": "*", "shl": "<<", "shr": ">>", "div": "/", "mod": "%"}[t]
    return f"({show(e[1])} {sym} {show(e[2])})"


def edge_values():
    return [0, 1, 2, M, M - 1, M >> 1, (M >> 1) + 1, 0x80, 0xFF, 0x7F] if W > 8 else [0, 1, 2, 0x7F, 0x80, 0xFE, 0xFF]


def emit(r, obf, gt, vars):
    envs = [{v: r.getrandbits(W) for v in vars} for _ in range(200)]
    envs += [{v: r.choice(edge_values()) & M for v in vars} for _ in range(200)]
    for env in envs:
        try:
            a = ev(obf, env)
        except ZeroDivisionError:
            continue
        assert a == ev(gt, env), (TY, show(obf), show(gt), env)
    return f"{show(obf)},{show(gt)}"


def inside_op(r):
    vs = ["x", "y", "z"]
    inner = sum_tree([(r.choice([1, 2, -1]), bitwise(r, ["x", "y"], 1)), (r.choice([1, -1]), ("var", r.choice(["x", "y"])))])
    obf_inner = mba(r, inner, ["x", "y"], 2) if r.random() < 0.5 else sum_tree([(1, inner)] + zero_terms(r, ["x", "y"], 2))
    op = r.choice(["shl", "shr", "div", "mod", "mulhi", "mul"])
    if op in ("shl", "shr"):
        other = num(r.randrange(1, W))
    elif op in ("div", "mod"):
        other = num(r.choice([3, 5, 7, 10, 12, 0x10]))
    else:
        other = ("var", "z")
    obf, gt = with_noise(r, (op, obf_inner, other), (op, inner, other), vs)
    return emit(r, obf, gt, vs)


def shift_identity(r):
    vs = ["x", "y"]
    x, y = ("var", "x"), ("var", "y")
    k = r.randrange(1, W - 1)
    j = r.randrange(1, W - k)
    low = (1 << k) - 1
    shapes = [
        (("shl", ("shr", x, num(k)), num(k)), ("and", x, num(~low))),
        (("mul", num(1 << k), x), ("shl", x, num(k))),
        (("shl", ("shl", x, num(k)), num(j)), ("shl", x, num(k + j))),
        (("and", ("shl", x, num(k)), num(low)), num(0)),
        (("add", ("shl", x, num(k)), ("shl", x, num(k))), ("shl", x, num(k + 1))),
        (("shl", ("add", x, y), num(k)), ("add", ("shl", x, num(k)), ("shl", y, num(k)))),
        (("shr", ("shl", x, num(k)), num(k)), ("and", x, num(M >> k)) if not SIGNED else None),
        (("shr", ("and", x, num(~low)), num(k)), ("shr", x, num(k))),
    ]
    obf, gt = r.choice([s for s in shapes if s[1] is not None])
    obf = subst_var(obf, "x", lambda: mba(r, x, vs, 1)) if r.random() < 0.5 else obf
    obf, gt = with_noise(r, obf, gt, vs)
    return emit(r, obf, gt, vs)


def subst_var(e, name, f):
    if e[0] == "var":
        return f() if e[1] == name else e
    if e[0] == "num":
        return e
    return (e[0],) + tuple(subst_var(a, name, f) for a in e[1:])


def magic_u(d):
    """Smallest s with m = ceil(2^(W+s) / d) exact for all W-bit x (Granlund-Montgomery);
    m may need W + 1 bits."""
    for s in range(0, W + 1):
        m = ((1 << (W + s)) + d - 1) // d
        if m * d - (1 << (W + s)) <= 1 << s:
            return m, s


def magic_s(d):
    """(M, s) for signed division by d >= 2 (Hacker's Delight figure 10-1)."""
    two = 1 << (W - 1)
    anc = two - 1 - two % d
    p = W - 1
    q1, r1 = divmod(two, anc)
    q2, r2 = divmod(two, d)
    while True:
        p += 1
        q1, r1 = 2 * q1, 2 * r1
        if r1 >= anc:
            q1, r1 = q1 + 1, r1 - anc
        q2, r2 = 2 * q2, 2 * r2
        if r2 >= d:
            q2, r2 = q2 + 1, r2 - d
        delta = d - r2
        if not (q1 < delta or (q1 == delta and r1 == 0)):
            break
    return (q2 + 1) & M, p - W


def magic_div(r):
    vs = ["x", "y"]
    d = r.choice([3, 5, 6, 7, 9, 10, 11, 12, 13, 25, 100, 1000])
    if d >= M >> 1:
        d = 3
    x = ("var", "x")
    xo = mba(r, x, vs, 1) if r.random() < 0.5 else x
    if not SIGNED:
        m, s = magic_u(d)
        if m >> W:
            # m has W + 1 bits: the usual (((x - t) >> 1) + t) >> (s - 1) sequence.
            t = ("mulhi", xo, num(m))
            q = ("shr", ("add", ("shr", ("sub", xo, t), num(1)), t), num(s - 1))
        else:
            q = ("shr", ("mulhi", xo, num(m)), num(s)) if s else ("mulhi", xo, num(m))
    else:
        m, s = magic_s(d)
        hi = ("mulhi", xo, num(m))
        if sx(m) < 0:
            hi = ("add", hi, xo)
        q = ("sub", ("shr", hi, num(s)), ("shr", xo, num(W - 1)))
    gt = ("div", x, num(d))
    if r.random() < 0.4:
        q, gt = ("sub", xo, ("mul", q, num(d))), ("mod", x, num(d))
    obf, gt = with_noise(r, q, gt, vs, 1)
    return emit(r, obf, gt, vs)


def disjoint_bits(r):
    vs = ["x", "y", "z"]
    k = r.randrange(2, W - 2)
    hi = ("shl", ("var", "x"), num(k))
    lo = ("and", ("var", "y"), num((1 << k) - 1)) if r.random() < 0.5 else ("shr", ("var", "y"), num(W - k)) if not SIGNED else ("and", ("var", "y"), num((1 << k) - 1))
    gt = ("or", hi, lo)
    form = r.choice(["add", "xor", "or", "sum3"])
    if form == "sum3":
        obf = ("sub", ("add", hi, lo), ("and", hi, lo))
    else:
        obf = (form, hi, lo)
    if r.random() < 0.5:
        obf = ("add", obf, ("mul", num(r.choice([1, 2, 3])), ("and", ("shl", ("var", "z"), num(k)), num((1 << k) - 1))))
    obf, gt = with_noise(r, obf, gt, vs)
    return emit(r, obf, gt, vs)


def variable_shift(r):
    vs = ["x", "y"]
    amt = ("and", ("var", "y"), num(W - 1))
    amt_obf = sum_tree([(1, amt)] + zero_terms(r, vs, 1))
    val = sum_tree([(1, bitwise(r, vs, 1))])
    val_obf = mba(r, val, vs, 1)
    op = r.choice(["shl", "shr"])
    obf, gt = with_noise(r, (op, val_obf, amt_obf), (op, val, amt), vs, 1)
    return emit(r, obf, gt, vs)


def main():
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    r = random.Random(1)
    sections = [
        ("linear MBA inside shift/div/mod/mulhi,groundtruth", inside_op),
        ("shift identities,groundtruth", shift_identity),
        ("magic-number division,groundtruth", magic_div),
        ("disjoint known bits,groundtruth", disjoint_bits),
        ("variable shift amounts,groundtruth", variable_shift),
    ]
    for name, f in sections:
        print(f"#{name}")
        for _ in range(n):
            print(f(r))


main()
