"""Generate MBA cases past the current benchmark for one numeric type, as
`obfuscated, groundtruth` lines for examples/bench.rs (run it with the same -n).

Sections (the name before the colon says the kind, so failures can be attributed):
- lin*: linear MBA over 9-20 variables with 3- to 5-variable terms, and one
  bitwise term over 7 or 10 variables;
- enc*: encoding applied 1-5 times: every operation (+ - * & | ^ ~ neg) of a
  small ground truth rewritten by an MBA identity whose operands may be
  arithmetic (non-polynomial MBA, as Tigress EncodeArithmetic), then the result
  encoded again, every operation or with lower probability;
- nonpoly*, pushed*: random ground truths of + - * & | ^ over 4-8 variables,
  encoded once or twice; pushed* also moves ~ and neg into arithmetic operands
  (~(a + b) = ~a - b), so complements of arithmetic leaves are not written as ~;
- core-*: non-linear cores wrapped in MBA: products, squares and cubes, shifts
  by a variable amount, division and remainder by a constant (half written with
  a magic multiplier), mulhi; product4, product-wide, poly-gt,
  bitwise-of-products, div-nested: larger polynomial and non-linear cores;
- mix: linear, polynomial and non-polynomial MBA in one expression;
- noise-*: zero noise that is a polynomial (degree 2 or 3) or non-polynomial
  identity, zero MBAs as factors, bitwise operands and shift amounts, and terms
  zero by number theory (x*(x+1) is even);
- semi-*: semi-linear MBA under encoding, over 4-7 variables;
- affine, perm-poly*: an affine data encoding and invertible polynomials
  (P(v) = b*v + a*v^2 with a*a = 0) applied and undone;
- shared*: one subterm used several times, each use obfuscated differently.

Semantics follow src/eval.rs (shifts by >= width give 0, arithmetic right shift
for signed types, signed division truncates). Every case is checked on random
and boundary inputs; inputs over MAX_SIZE nodes are drawn again.

Usage: python -I scripts/gen-deep.py TYPE [cases-per-section] > bench-data/deep_TYPE.txt
"""

import random
import sys

sys.setrecursionlimit(100000)

TY = sys.argv[1] if len(sys.argv) > 1 else "u64"
SIGNED = TY[0] == "i"
W = int(TY[1:])
M = (1 << W) - 1
MAX_SIZE = 50000
VARS = list("abcdefghijklmnopqrstuvwx")


def sx(v):
    v &= M
    return v - (1 << W) if SIGNED and v >> (W - 1) else v


def num(v):
    return ("num", v & M)


def var(v):
    return ("var", v)


def ev(e, env, memo=None):
    if memo is None:
        memo = {}
    k = id(e)
    if k in memo:
        return memo[k]
    t = e[0]
    if t == "var":
        v = env[e[1]]
    elif t == "num":
        v = e[1] & M
    elif t == "not":
        v = ~ev(e[1], env, memo) & M
    elif t == "neg":
        v = -ev(e[1], env, memo) & M
    else:
        a, b = ev(e[1], env, memo), ev(e[2], env, memo)
        if t in ("and", "or", "xor", "add", "sub", "mul"):
            v = {"and": a & b, "or": a | b, "xor": a ^ b, "add": a + b, "sub": a - b, "mul": a * b}[t] & M
        elif t == "shl":
            v = 0 if b >= W else (a << b) & M
        elif t == "shr":
            if SIGNED:
                v = (sx(a) >> min(b, W - 1)) & M
            else:
                v = 0 if b >= W else a >> b
        elif t == "mulhi":
            v = ((sx(a) * sx(b)) >> W) & M
        else:
            if b == 0:
                raise ZeroDivisionError
            if SIGNED:
                q = abs(sx(a)) // abs(sx(b))
                q = q if (sx(a) < 0) == (sx(b) < 0) else -q
                v = (q if t == "div" else sx(a) - sx(b) * q) & M
            else:
                v = (a // b if t == "div" else a % b) & M
    memo[k] = v
    return v


SYM = {"and": "&", "or": "|", "xor": "^", "add": "+", "sub": "-", "mul": "*", "shl": "<<", "shr": ">>", "div": "/",
       "mod": "%"}


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
    return f"({show(e[1])} {SYM[t]} {show(e[2])})"


def size(e, memo=None):
    if memo is None:
        memo = {}
    if e[0] in ("var", "num"):
        return 1
    if id(e) not in memo:
        memo[id(e)] = 1 + sum(size(a, memo) for a in e[1:])
    return memo[id(e)]


def bitwise(r, vars, depth, cprob=0.0):
    if depth == 0:
        return var(r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", bitwise(r, vars, depth - 1, cprob))
    other = num(const(r)) if r.random() < cprob else bitwise(r, vars, depth - 1, cprob)
    return (op, bitwise(r, vars, depth - 1, cprob), other)


def covering_bitwise(r, vars):
    """A bitwise expression using every variable of vars once, random tree shape."""
    items = [var(v) for v in vars]
    r.shuffle(items)
    while len(items) > 1:
        i = r.randrange(len(items) - 1)
        a, b = items[i], items[i + 1]
        if r.random() < 0.2:
            a = ("not", a)
        items[i : i + 2] = [(r.choice(["and", "or", "xor"]), a, b)]
    return items[0]


def const(r):
    if W == 8:
        return r.randrange(1, 256)
    return r.choice([r.randrange(1, 256), r.randrange(1, 1 << 16), r.getrandbits(W),
                     r.choice([0xF0, 0x0F, 0x5C, 0x33, 0xCC, 0xFF00])])


def expand(e, r, p):
    """Rewrite bitwise operations in arithmetic context into arithmetic of their operands."""
    t = e[0]
    if r.random() >= p or t not in ("and", "or", "xor", "not"):
        return e
    if t == "not":
        return ("sub", ("neg", expand(e[1], r, p)), num(1))
    a, b = e[1], e[2]
    if t == "and":
        return ("sub", ("add", expand(a, r, p), expand(b, r, p)), ("or", a, b))
    if t == "or":
        return ("sub", ("add", expand(a, r, p), expand(b, r, p)), ("and", a, b))
    return ("sub", ("or", a, b), ("and", a, b))


def mulc(c, e):
    return e if c == 1 else ("mul", num(c), e)


def sum_tree(terms):
    out = None
    for c, e in terms:
        c = sx(c) if SIGNED else (c if abs(c) < 1 << (W - 1) else c - (1 << W))
        t = e if abs(c) == 1 else ("mul", num(abs(c)), e)
        if out is None:
            out = ("neg", t) if c < 0 else t
        else:
            out = ("sub" if c < 0 else "add", out, t)
    return out


def coef(r, small=False):
    return r.choice([1, 2, 3, -1, -2] if small else [1, 2, 3, 5, -1, -2, -3, -7])


def zero_terms(r, vars, k, cprob=0.0):
    out = []
    for _ in range(k):
        c = coef(r)
        f = bitwise(r, r.sample(vars, min(len(vars), r.choice([2, 3]))), 2, cprob)
        out += [(c, f), (-c, expand(f, r, 1.0))]
    return out


def lin(r, e, vars, k=1):
    """e plus a linear zero MBA of k pairs, bitwise operations of e expanded."""
    z = zero_terms(r, vars, k)
    terms = [(1, expand(e, r, 0.9))] + z
    r.shuffle(terms)
    return sum_tree(terms)


def identity(r, t, a, b):
    """One MBA identity for the operation t on a and b (any terms)."""
    if t == "add":
        return r.choice([
            lambda: ("add", ("xor", a, b), mulc(2, ("and", a, b))),
            lambda: ("add", ("or", a, b), ("and", a, b)),
            lambda: ("sub", mulc(2, ("or", a, b)), ("xor", a, b)),
            lambda: ("sub", a, ("add", ("not", b), num(1))),
        ])()
    if t == "sub":
        return r.choice([
            lambda: ("sub", ("xor", a, b), mulc(2, ("and", ("not", a), b))),
            lambda: ("sub", ("and", a, ("not", b)), ("and", ("not", a), b)),
            lambda: ("sub", mulc(2, ("and", a, ("not", b))), ("xor", a, b)),
            lambda: ("add", ("add", a, ("not", b)), num(1)),
        ])()
    if t == "xor":
        return r.choice([
            lambda: ("sub", ("or", a, b), ("and", a, b)),
            lambda: ("sub", ("add", a, b), mulc(2, ("and", a, b))),
            lambda: ("add", ("and", a, ("not", b)), ("and", ("not", a), b)),
        ])()
    if t == "and":
        return r.choice([
            lambda: ("sub", ("add", a, b), ("or", a, b)),
            lambda: ("sub", ("or", ("not", a), b), ("not", a)),
            lambda: ("sub", a, ("and", a, ("not", b))),
        ])()
    if t == "or":
        return r.choice([
            lambda: ("add", ("xor", a, b), ("and", a, b)),
            lambda: ("sub", ("add", a, b), ("and", a, b)),
            lambda: ("add", ("and", a, ("not", b)), b),
        ])()
    if t == "mul":
        return ("add", ("mul", ("and", a, b), ("or", a, b)), ("mul", ("and", a, ("not", b)), ("and", ("not", a), b)))
    if t == "not":
        return ("sub", ("neg", a), num(1))
    if t == "neg":
        return ("add", ("not", a), num(1))
    raise ValueError(t)


def encode(e, r, p, cache=None):
    """Rewrite each + - * & | ^ ~ neg with probability p by an MBA identity, children first."""
    if cache is None:
        cache = {}
    if id(e) in cache:
        return cache[id(e)]
    t = e[0]
    if t in ("var", "num"):
        out = e
    else:
        kids = [encode(a, r, p, cache) for a in e[1:]]
        out = (t,) + tuple(kids)
        constant = t == "mul" and any(k[0] == "num" for k in kids)
        if t in ("add", "sub", "xor", "and", "or", "mul", "not", "neg") and not constant and r.random() < p:
            out = identity(r, t, kids[0], kids[1] if len(kids) > 1 else None)
    cache[id(e)] = out
    return out


def noise(r, obf, vars, k=2):
    terms = [(1, obf)] + zero_terms(r, vars, k)
    r.shuffle(terms)
    return sum_tree(terms)


def edge_values():
    return [0, 1, 2, M, M - 1, M >> 1, (M >> 1) + 1, 0x80, 0xFF, 0x7F] if W > 8 else [0, 1, 2, 0x7F, 0x80, 0xFE, 0xFF]


class TooBig(Exception):
    pass


def emit(r, obf, gt, vars):
    if size(obf) > MAX_SIZE:
        raise TooBig
    envs = [{v: r.getrandbits(W) for v in vars} for _ in range(100)]
    envs += [{v: r.choice(edge_values()) & M for v in vars} for _ in range(100)]
    for env in envs:
        try:
            a = ev(obf, env)
        except ZeroDivisionError:
            continue
        assert a == ev(gt, env), (TY, show(obf), show(gt), env)
    return f"{show(obf)},{show(gt)}"


def linear_9(r):
    vs = VARS[:9]
    gt = [(coef(r, True), covering_bitwise(r, r.sample(vs, 3))) for _ in range(4)]
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 5)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def linear_10(r):
    vs = VARS[:10]
    gt = [(coef(r, True), covering_bitwise(r, r.sample(vs, 4))) for _ in range(3)]
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 5)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def linear_one_term_7(r):
    vs = VARS[:7]
    gt = [(coef(r, True), covering_bitwise(r, vs))]
    if r.random() < 0.5:
        gt.append((coef(r, True), var(r.choice(vs))))
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 3)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def small_gt(r, vs):
    """A small linear ground truth: c1*B + c2*v or (u op v) op' w."""
    if r.random() < 0.5:
        return sum_tree([(coef(r, True), bitwise(r, vs, 1)), (coef(r, True), var(r.choice(vs)))])
    a, b, c = (var(v) for v in r.sample(vs, 3))
    return (r.choice(["add", "sub", "xor"]), (r.choice(["and", "or", "xor", "add"]), a, b), c)


def product_core(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    gt = r.choice([
        ("add", ("mul", x, y), z),
        ("mul", ("mul", x, y), z),
        ("mul", ("add", x, y), ("xor", x, z)),
        ("add", ("mul", x, x), y),
        ("mul", ("xor", x, y), ("xor", x, y)),
        ("sub", ("mul", ("and", x, y), z), x),
    ])
    obf = encode(gt, r, 0.8)
    return emit(r, noise(r, obf, vs, 1), gt, vs)


def cube_core(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    u = r.choice([x, ("add", x, y), ("xor", x, y), ("sub", x, z)])
    gt = ("mul", ("mul", u, u), u)
    if r.random() < 0.5:
        gt = ("add", gt, r.choice([y, z, ("and", y, z)]))
    f = lambda: lin(r, u, vs, 1)
    obf = ("mul", ("mul", f(), f()), f())
    if gt[0] == "add":
        obf = ("add", obf, encode(gt[2], r, 1.0))
    return emit(r, noise(r, obf, vs, 2), gt, vs)


def var_shift_core(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    amt = ("and", y, num(W - 1))
    sh = (r.choice(["shl", "shr"]), r.choice([x, ("xor", x, z), ("add", x, z)]), amt)
    gt = (r.choice(["add", "xor", "sub", "or"]), sh, z)
    shown = (sh[0], encode(sh[1], r, 1.0), encode(amt, r, 1.0))
    obf = identity(r, gt[0], shown, z)
    return emit(r, noise(r, obf, vs, 2), gt, vs)


def magic_u(d):
    for s in range(0, W + 1):
        m = ((1 << (W + s)) + d - 1) // d
        if m * d - (1 << (W + s)) <= 1 << s:
            return m, s


def magic_s(d):
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


def magic_div(xo, d):
    if not SIGNED:
        m, s = magic_u(d)
        if m >> W:
            t = ("mulhi", xo, num(m))
            return ("shr", ("add", ("shr", ("sub", xo, t), num(1)), t), num(s - 1))
        return ("shr", ("mulhi", xo, num(m)), num(s)) if s else ("mulhi", xo, num(m))
    m, s = magic_s(d)
    hi = ("mulhi", xo, num(m))
    if sx(m) < 0:
        hi = ("add", hi, xo)
    return ("sub", ("shr", hi, num(s)), ("shr", xo, num(W - 1)))


def div_core(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    d = r.choice([3, 5, 6, 7, 9, 10, 12, 25] + ([100, 1000] if W > 8 else []))
    u = r.choice([x, ("add", x, y), ("xor", x, y)])
    uo = encode(u, r, 1.0) if u is not x else lin(r, x, vs, 1)
    q, qo = ("div", u, num(d)), ("div", uo, num(d))
    if r.random() < 0.5:
        qo = magic_div(uo, d)
    if r.random() < 0.3:
        q, qo = ("mod", u, num(d)), ("sub", uo, ("mul", qo, num(d)))
    t = r.choice(["add", "xor", "and", "sub"])
    gt = (t, q, z)
    obf = identity(r, t, qo, encode(z, r, 1.0))
    return emit(r, noise(r, obf, vs, 2), gt, vs)


def mulhi_core(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    b = r.choice([y, num(const(r) | 1)])
    h = ("mulhi", x, b)
    t = r.choice(["add", "xor", "or", "sub"])
    gt = (t, h, z)
    ho = ("mulhi", lin(r, x, vs, 1), lin(r, b, vs, 1) if b[0] == "var" else b)
    obf = identity(r, t, ho, z)
    return emit(r, noise(r, encode(obf, r, 0.4), vs, 2), gt, vs)


def mixed_kinds(r):
    vs = ["x", "y", "z", "w"]
    x, y, z, w = map(var, vs)
    a, b = r.sample(vs, 2)
    lin_part = (coef(r, True), bitwise(r, [a, b], 1))
    p1, p2 = bitwise(r, vs, 1), bitwise(r, vs, 1)
    poly_part = (1, ("mul", p1, p2))
    u, v, s = map(var, r.sample(vs, 3))
    np_part = (1, (r.choice(["and", "or", "xor"]), ("add", u, v), s))
    gt = sum_tree([lin_part, poly_part, np_part])
    obf_terms = [
        (lin_part[0], expand(lin_part[1], r, 1.0)),
        (1, ("mul", lin(r, p1, vs, 1), lin(r, p2, vs, 1))),
        (1, encode(np_part[1], r, 1.0)),
    ] + zero_terms(r, vs, 2)
    r.shuffle(obf_terms)
    obf = encode(sum_tree(obf_terms), r, 0.3)
    return emit(r, obf, gt, vs)


def poly_zero_noise(r):
    vs = ["x", "y", "z"]
    gt = small_gt(r, vs)
    terms = [(1, expand(gt, r, 0.8))]
    for _ in range(2):
        c = coef(r)
        f, g = bitwise(r, vs, 1), bitwise(r, vs, 1)
        terms += [(c, ("mul", f, g)), (-c, ("mul", lin(r, f, vs, 1), lin(r, g, vs, 1)))]
    a, b = map(var, r.sample(vs, 2))
    c = coef(r)
    terms += [(c, ("mul", a, b)), (-c, identity(r, "mul", a, b))]
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def nonpoly_zero_noise(r):
    vs = ["x", "y", "z"]
    gt = small_gt(r, vs)
    terms = [(1, encode(gt, r, 0.7))]
    for _ in range(2):
        c = coef(r)
        a, b, s = map(var, r.sample(vs, 3))
        arith = r.choice([("add", a, b), ("sub", a, b), ("mul", a, b), ("add", a, num(const(r)))])
        e = (r.choice(["and", "or", "xor"]), arith, s)
        terms += [(c, e), (-c, encode(e, r, 1.0))]
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def semi_encode(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    k1, k2 = num(const(r)), num(const(r))
    gt = r.choice([
        ("add", ("and", x, k1), ("xor", y, k2)),
        ("xor", ("or", x, k1), y),
        ("add", ("xor", ("and", x, y), k1), z),
        ("sub", ("or", ("xor", x, y), k1), ("and", z, k2)),
    ])
    obf = encode(gt, r, 1.0)
    obf = encode(obf, r, 0.3)
    terms = [(1, obf)] + zero_terms(r, vs, 2, cprob=0.4)
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def affine_encoding(r):
    """x and y kept as a*v + b (a odd), the operation done on decoded values under MBA."""
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    a = r.getrandbits(W) | 1
    ainv = pow(a, -1, 1 << W)
    b1, b2 = r.getrandbits(W), r.getrandbits(W)
    enc = lambda v, b: encode(("add", ("mul", num(a), v), num(b)), r, 1.0)
    dec = lambda e, b: ("mul", num(ainv), encode(("sub", e, num(b)), r, 1.0))
    t = r.choice(["add", "xor", "and", "or", "sub"])
    gt = (t, x, y)
    if r.random() < 0.5:
        gt = ("add", gt, z)
    inner = identity(r, t, dec(enc(x, b1), b1), dec(enc(y, b2), b2))
    obf = inner if gt[0] == t and gt[1] is x else ("add", inner, z)
    return emit(r, noise(r, obf, vs, 1), gt, vs)


def shared_subterm(r):
    vs = ["x", "y", "z", "w"]
    x, y, z, w = map(var, vs)
    t = (r.choice(["add", "xor", "sub"]), x, y)
    gt = sum_tree([(coef(r, True), t), (1, (r.choice(["and", "or", "xor"]), t, z)), (1, ("mul", t, w))])
    forms = lambda: encode(t, r, 1.0) if r.random() < 0.5 else lin(r, t, ["x", "y"], 1)
    parts, node = [], gt
    while node[0] in ("add", "sub"):
        parts.append((node[0], node[2]))
        node = node[1]
    parts.append(("add", node))

    def obf_part(e):
        if e is t:
            return forms()
        if e[0] in ("var", "num"):
            return e
        return (e[0],) + tuple(obf_part(a) for a in e[1:])

    terms = [(-1 if op == "sub" else 1, obf_part(e)) for op, e in parts] + zero_terms(r, vs, 1)
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def linear_wide(nvars, terms, k, noise_pairs):
    def gen(r):
        vs = VARS[:nvars]
        gt = [(coef(r, True), covering_bitwise(r, r.sample(vs, k))) for _ in range(terms)]
        z = []
        for _ in range(noise_pairs):
            c = coef(r)
            f = covering_bitwise(r, r.sample(vs, 3))
            z += [(c, f), (-c, expand(f, r, 1.0))]
        obf = [(c, expand(e, r, 0.9)) for c, e in gt] + z
        r.shuffle(obf)
        return emit(r, sum_tree(obf), sum_tree(gt), vs)

    return gen


def linear_one_term(nvars):
    def gen(r):
        vs = VARS[:nvars]
        gt = [(coef(r, True), covering_bitwise(r, vs))]
        obf = [(c, expand(e, r, 1.0)) for c, e in gt] + zero_terms(r, vs, 3)
        r.shuffle(obf)
        return emit(r, sum_tree(obf), sum_tree(gt), vs)

    return gen


def encoded_probs(probs):
    def gen(r):
        vs = ["x", "y", "z"]
        gt = small_gt(r, vs)
        obf = gt
        for p in probs:
            obf = encode(obf, r, p)
        return emit(r, noise(r, obf, vs, 1), gt, vs)

    return gen


def nonpoly_gt(probs):
    def gen(r):
        vs = ["x", "y", "z", "w"]
        gt = mixed_tree_n(r, vs, r.choice([2, 3]), 1)
        obf = gt
        for p in probs:
            obf = encode(obf, r, p)
        return emit(r, noise(r, obf, vs, 2), gt, vs)

    return gen


def lin_zero(r, vs, k=1):
    z = zero_terms(r, vs, k)
    r.shuffle(z)
    return sum_tree(z)


def nonpoly_zero(r, vs):
    a, b, s = map(var, r.sample(vs, 3))
    e = (r.choice(["and", "or", "xor"]), r.choice([("add", a, b), ("mul", a, b), ("sub", a, b)]), s)
    return ("sub", e, encode(e, r, 1.0))


def mult_noise(r):
    """Zero MBAs in non-additive positions: factors, bitwise operands and shift amounts."""
    vs = ["x", "y", "z"]
    gt = small_gt(r, vs)
    zero = lambda: lin_zero(r, vs, 1) if r.random() < 0.5 else nonpoly_zero(r, vs)
    g = encode(gt, r, 0.5)
    obf = r.choice([
        lambda: ("mul", g, ("add", num(1), zero())),
        lambda: ("xor", g, zero()),
        lambda: ("or", zero(), g),
        lambda: ("add", g, ("and", zero(), var(r.choice(vs)))),
        lambda: ("add", g, ("mul", zero(), var(r.choice(vs)))),
        lambda: ("shl", g, ("and", zero(), num(W - 1))),
    ])()
    if r.random() < 0.5:
        obf = ("add", ("mul", g, zero()), obf)
    return emit(r, noise(r, obf, vs, 1), gt, vs)


def opaque(r):
    """Terms zero for every input by number theory, not by an MBA identity: x*(x+1) is even, x*x mod 4 < 2."""
    vs = ["x", "y", "z"]
    gt = small_gt(r, vs)
    terms = [(1, encode(gt, r, 0.6))]
    for _ in range(2):
        x, y = map(var, r.sample(vs, 2))
        u = r.choice([x, lin(r, x, vs, 1)])
        z = r.choice([
            ("and", ("mul", u, ("add", u, num(1))), num(1)),
            ("and", ("mul", u, u), num(2)),
            ("and", ("mul", ("mul", u, ("add", u, num(1))), ("add", u, num(2))), num(1)),
            ("and", ("sub", ("mul", u, u), u), num(1)),
        ])
        terms.append((coef(r), r.choice([z, ("mul", z, y), ("and", y, ("neg", z))])))
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def poly3_noise(r):
    vs = ["x", "y", "z"]
    gt = small_gt(r, vs)
    terms = [(1, expand(gt, r, 0.8))]
    c = coef(r)
    f, g, h = (bitwise(r, vs, 1) for _ in range(3))
    terms += [(c, ("mul", ("mul", f, g), h)), (-c, ("mul", ("mul", lin(r, f, vs), lin(r, g, vs)), lin(r, h, vs)))]
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def replace(e, t, f):
    if e is t:
        return f()
    if e[0] in ("var", "num"):
        return e
    return (e[0],) + tuple(replace(a, t, f) for a in e[1:])


def shared_nonlinear(r):
    vs = ["x", "y", "z", "w"]
    x, y, z, w = map(var, vs)
    t = r.choice([("mul", x, y), ("and", ("add", x, y), z), ("shl", x, ("and", y, num(W - 1))), ("xor", ("mul", x, x), y)])
    uses = [(coef(r, True), t), (1, (r.choice(["and", "or", "xor"]), t, w)), (-1, (r.choice(["add", "mul"]), t, z))]
    gt = sum_tree(uses)
    obf = [(c, replace(e, t, lambda: encode(t, r, 1.0))) for c, e in uses] + zero_terms(r, vs, 1)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), gt, vs)


def product4(r):
    vs = ["x", "y", "z", "w"]
    fs = [bitwise(r, r.sample(vs, 2), 1) for _ in range(4)]
    gt = ("mul", ("mul", fs[0], fs[1]), ("mul", fs[2], fs[3]))
    obf = ("mul", ("mul", lin(r, fs[0], vs), lin(r, fs[1], vs)), ("mul", lin(r, fs[2], vs), lin(r, fs[3], vs)))
    return emit(r, noise(r, obf, vs, 1), gt, vs)


def nested_div(r):
    vs = ["x", "y", "z"]
    x, y, z = map(var, vs)
    d1, d2 = r.choice([3, 5, 7, 10]), r.choice([3, 6, 9, 12])
    u = ("add", x, y)
    q1o = magic_div(encode(u, r, 1.0), d1)
    gt = ("div", ("xor", ("div", u, num(d1)), z), num(d2))
    obf = magic_div(identity(r, "xor", q1o, lin(r, z, vs)), d2)
    return emit(r, noise(r, obf, vs, 1), gt, vs)


def semi_deep(r):
    vs = ["x", "y", "z", "w"]
    gt = sum_tree([(coef(r, True), bitwise(r, vs, 3, cprob=0.5)), (1, num(const(r)))])
    obf = encode(encode(gt, r, 1.0), r, 0.4)
    terms = [(1, obf)] + zero_terms(r, vs, 2, cprob=0.4)
    r.shuffle(terms)
    return emit(r, sum_tree(terms), gt, vs)


def mixed_tree_n(r, vs, depth, muls):
    """Random tree of + - * & | ^ with at most `muls` products, leaves distinct while they last."""
    left = list(vs)
    r.shuffle(left)
    budget = [muls]

    def go(d):
        if d == 0:
            return var(left.pop()) if left else var(r.choice(vs))
        t = r.choice(["add", "sub", "and", "or", "xor"] + (["mul"] if budget[0] else []))
        if t == "mul":
            budget[0] -= 1
        return (t, go(d - 1), go(d - 1))

    return go(depth)


def nonpoly_wide(probs, nvars=6, depth=4, muls=2):
    def gen(r):
        vs = VARS[:nvars]
        gt = mixed_tree_n(r, vs, depth, muls)
        obf = gt
        for p in probs:
            obf = encode(obf, r, p)
        return emit(r, noise(r, obf, vs, 2), gt, vs)

    return gen


def perm_poly(r):
    """(P, Q) with Q(P(v)) = v: P(v) = b*v + a*v^2, a*a = 0 mod 2^W, Q(v) = b^-1*v - a*b^-3*v^2."""
    a = (r.getrandbits(W) << ((W + 1) // 2)) & M or 1 << ((W + 1) // 2)
    b = r.getrandbits(W) | 1
    bi = pow(b, -1, 1 << W)
    p = lambda v: ("add", ("mul", num(b), v), ("mul", num(a), ("mul", v, v)))
    q = lambda v: ("sub", ("mul", num(bi), v), ("mul", num(a * bi * bi * bi), ("mul", v, v)))
    return p, q


def perm_poly_case(layers):
    def gen(r):
        vs = ["x", "y", "z"]
        gt = small_gt(r, vs)
        pqs = [perm_poly(r) for _ in range(layers)]
        e = encode(gt, r, 1.0)
        for p, _ in pqs:
            e = encode(p(e), r, 0.3)
        for _, q in reversed(pqs):
            e = q(e)
        return emit(r, noise(r, e, vs, 1), gt, vs)

    return gen


def product_wide(r):
    vs = VARS[:10]
    left = sum_tree([(coef(r, True), covering_bitwise(r, r.sample(vs[:5], 3))) for _ in range(2)])
    right = sum_tree([(coef(r, True), covering_bitwise(r, r.sample(vs[5:], 3))) for _ in range(2)])
    gt = ("mul", left, right)
    obf = ("mul", lin(r, left, vs[:5], 2), lin(r, right, vs[5:], 2))
    return emit(r, noise(r, obf, vs, 2), gt, vs)


def bitwise_of_products(r):
    vs = ["x", "y", "z", "w"]
    x, y, z, w = map(var, vs)
    gt = (r.choice(["add", "xor", "sub"]), (r.choice(["and", "or", "xor"]), ("mul", x, y), ("mul", z, w)), ("add", x, z))
    return emit(r, noise(r, encode(gt, r, 1.0), vs, 2), gt, vs)


def push_in(e, r, p):
    """Move ~ and neg into + - * operands with probability p: ~(a + b) = ~a - b, -(a * b) = -a * b, ..."""
    t = e[0]
    if t in ("var", "num"):
        return e
    if t in ("not", "neg") and e[1][0] in ("add", "sub", "mul", "neg", "not") and r.random() < p:
        a = e[1]
        if t == "not":
            if a[0] == "add":
                return ("sub", push_in(("not", a[1]), r, p), push_in(a[2], r, p))
            if a[0] == "sub":
                return ("add", push_in(("not", a[1]), r, p), push_in(a[2], r, p))
            if a[0] == "neg":
                return ("sub", push_in(a[1], r, p), num(1))
            if a[0] == "not":
                return push_in(a[1], r, p)
            return ("sub", push_in(("neg", a), r, p), num(1))
        if a[0] == "add":
            return ("sub", push_in(("neg", a[1]), r, p), push_in(a[2], r, p))
        if a[0] == "sub":
            return ("sub", push_in(a[2], r, p), push_in(a[1], r, p))
        if a[0] == "mul":
            return ("mul", push_in(("neg", a[1]), r, p), push_in(a[2], r, p))
        if a[0] == "neg":
            return push_in(a[1], r, p)
        return ("add", push_in(a[1], r, p), num(1))
    return (t,) + tuple(push_in(a, r, p) for a in e[1:])


def nonpoly_pushed(nvars, depth, muls):
    def gen(r):
        vs = VARS[:nvars]
        gt = mixed_tree_n(r, vs, depth, muls)
        obf = push_in(encode(gt, r, 1.0), r, 0.8)
        return emit(r, noise(r, obf, vs, 2), gt, vs)

    return gen


def semi_wide(nvars):
    def gen(r):
        vs = VARS[:nvars]
        b = covering_bitwise(r, vs)

        def consts(e):
            if e[0] == "var":
                return ("and", e, num(const(r))) if r.random() < 0.3 else e
            if e[0] in ("and", "or", "xor") and r.random() < 0.3:
                return (r.choice(["and", "or", "xor"]), (e[0], consts(e[1]), consts(e[2])), num(const(r)))
            return (e[0],) + tuple(consts(a) for a in e[1:])

        gt = sum_tree([(coef(r, True), consts(b)), (1, num(const(r)))])
        obf = encode(gt, r, 0.7)
        terms = [(1, obf)] + zero_terms(r, vs, 2, cprob=0.4)
        r.shuffle(terms)
        return emit(r, sum_tree(terms), gt, vs)

    return gen


def poly_gt(r):
    """Sum of three products of bitwise terms over 4 variables, factors as linear MBAs."""
    vs = ["x", "y", "z", "w"]
    gt = [(coef(r, True), ("mul", covering_bitwise(r, r.sample(vs, 2)), covering_bitwise(r, r.sample(vs, 2)))) for _ in range(3)]
    obf = [(c, ("mul", lin(r, e[1], vs), lin(r, e[2], vs))) for c, e in gt] + zero_terms(r, vs, 1)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def arith_operand(r, vs):
    a, b, c = (var(v) for v in r.sample(vs, 3))
    return r.choice([("add", a, b), ("sub", a, b), ("mul", a, b), ("add", ("mul", a, b), c), ("sub", a, ("and", b, c)),
                     ("add", ("xor", a, b), c)])


def complement_case(t):
    """One identity for t on two arithmetic operands, with every ~ and neg pushed into them."""
    def gen(r):
        vs = ["x", "y", "z", "w"]
        a, b = arith_operand(r, vs), arith_operand(r, vs)
        gt = (t, a, b)
        obf = push_in(identity(r, t, a, b), r, 1.0)
        if r.random() < 0.5:
            c = var(r.choice(vs))
            gt, obf = ("add", gt, c), ("add", obf, c)
        return emit(r, noise(r, obf, vs, 1), gt, vs)

    return gen


SECTIONS = [
    ("lin9: linear MBA, 9 variables, 3-variable terms", linear_9),
    ("lin10: linear MBA, 10 variables, 4-variable terms", linear_10),
    ("lin7one: one bitwise term over 7 variables", linear_one_term_7),
    ("enc1: encoding applied once", encoded_probs([1.0])),
    ("enc2: encoding applied twice", encoded_probs([1.0, 0.5])),
    ("enc3: encoding applied three times", encoded_probs([1.0, 0.5, 0.3])),
    ("core-product: products and squares under encoding", product_core),
    ("core-cube: cubes of linear MBAs", cube_core),
    ("core-varshift: shift by a variable amount", var_shift_core),
    ("core-div: division and remainder by a constant", div_core),
    ("core-mulhi: mulhi", mulhi_core),
    ("mix: linear + polynomial + non-polynomial", mixed_kinds),
    ("noise-poly: polynomial zero identities", poly_zero_noise),
    ("noise-nonpoly: non-polynomial zero identities", nonpoly_zero_noise),
    ("semi-enc: semi-linear under encoding", semi_encode),
    ("affine: affine data encoding round trip", affine_encoding),
    ("shared: one subterm obfuscated differently per use", shared_subterm),
    ("lin16: linear MBA, 16 variables, 4-variable terms", linear_wide(16, 5, 4, 6)),
    ("lin20: linear MBA, 20 variables, 4-variable terms", linear_wide(20, 6, 4, 6)),
    ("lin10one: one bitwise term over 10 variables", linear_one_term(10)),
    ("enc3full: encoding applied three times, every operation", encoded_probs([1.0, 1.0, 1.0])),
    ("enc5: encoding applied five times", encoded_probs([1.0, 0.6, 0.5, 0.4, 0.3])),
    ("nonpoly-gt: non-polynomial ground truth, encoded once", nonpoly_gt([1.0])),
    ("nonpoly-gt2: non-polynomial ground truth, encoded twice", nonpoly_gt([1.0, 0.5])),
    ("noise-mult: zero MBAs as factors, bitwise operands and shift amounts", mult_noise),
    ("noise-opaque: terms zero by number theory, x*(x+1) even", opaque),
    ("noise-poly3: degree-3 polynomial zero identities", poly3_noise),
    ("shared-nonlinear: non-linear subterm obfuscated differently per use", shared_nonlinear),
    ("product4: product of four linear MBAs", product4),
    ("div-nested: division of a bitwise term of a quotient", nested_div),
    ("semi-deep: depth-3 semi-linear over 4 variables, encoded", semi_deep),
    ("nonpoly-wide: depth-4 non-polynomial ground truth over 6 variables, encoded once", nonpoly_wide([1.0])),
    ("nonpoly-wide2: depth-4 non-polynomial ground truth over 6 variables, encoded twice", nonpoly_wide([1.0, 0.5])),
    ("perm-poly1: invertible polynomial and its inverse, one layer", perm_poly_case(1)),
    ("perm-poly2: invertible polynomials and their inverses, two layers", perm_poly_case(2)),
    ("product-wide: product of two linear MBAs over 5 variables each", product_wide),
    ("bitwise-of-products: bitwise operation of two products, encoded", bitwise_of_products),
    ("lin12x5: linear MBA, 12 variables, 5-variable terms", linear_wide(12, 4, 5, 6)),
    ("nonpoly8: depth-5 non-polynomial ground truth over 8 variables, encoded once", nonpoly_wide([1.0], 8, 5, 3)),
    ("pushed4: non-polynomial over 4 variables, encoded, ~ and neg pushed into arithmetic", nonpoly_pushed(4, 3, 1)),
    ("pushed6: non-polynomial over 6 variables, encoded, ~ and neg pushed into arithmetic", nonpoly_pushed(6, 4, 2)),
    ("semi-wide5: semi-linear bitwise term over 5 variables", semi_wide(5)),
    ("semi-wide7: semi-linear bitwise term over 7 variables", semi_wide(7)),
    ("poly-gt: sum of three products of bitwise terms", poly_gt),
    ("nonpoly8x2: depth-5 non-polynomial ground truth over 8 variables, encoded twice", nonpoly_wide([1.0, 0.5], 8, 5, 3)),
    ("nonpoly10: depth-5 non-polynomial ground truth over 10 variables, encoded once", nonpoly_wide([1.0], 10, 5, 4)),
    ("nonpoly12: depth-6 non-polynomial ground truth over 12 variables, encoded once", nonpoly_wide([1.0], 12, 6, 6)),
    ("lin24x6: linear MBA, 24 variables, 6-variable terms", linear_wide(24, 6, 6, 8)),
    ("enc4full: encoding applied four times, every operation", encoded_probs([1.0, 1.0, 1.0, 1.0])),
    ("cmpl-xor: xor of arithmetic operands, complements pushed into them", complement_case("xor")),
    ("cmpl-or: or of arithmetic operands, complements pushed into them", complement_case("or")),
    ("cmpl-and: and of arithmetic operands, complements pushed into them", complement_case("and")),
    ("cmpl-mul: product identity on arithmetic operands, complements pushed into them", complement_case("mul")),
]


def main():
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    r = random.Random(f"deep-{TY}")
    for name, f in SECTIONS:
        print(f"#{name},groundtruth")
        done = 0
        while done < n:
            try:
                print(f(r))
            except TooBig:
                continue
            done += 1


main()
