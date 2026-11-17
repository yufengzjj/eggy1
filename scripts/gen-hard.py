"""Generate harder MBA cases as `obfuscated, groundtruth` lines for examples/bench.rs.

Sections:
- linear MBA over 8 variables (more leaves than the linear rebuild takes);
- variables inside bitwise operations replaced by (v + Z), Z a zero MBA;
- products, with x*y written as (x&y)*(x|y) + (x&~y)*(~x&y);
- one obfuscated subterm repeated, also inside bitwise operations;
- two levels of (v + Z) substitution;
- 8 variables in overlapping pairs, deeper bitwise terms, noisy product
  operands, sums of products, and arithmetic leaves over 4 variables;
- semi-linear MBA (bitwise operations with constants): 4 variables, 64-bit
  constants, depth 3, a constant offset, and semi-linear arithmetic leaves.

Zero MBAs are sums c*(f - g), with g the bitwise expression f rewritten by
identities such as a&b = a+b-(a|b). Every case is checked on random inputs.

Usage: python scripts/gen-hard.py [cases-per-section] > bench-data/hard.txt
"""

import random
import sys

M = (1 << 64) - 1
VARS8 = list("abcdefgh")


def bitwise(r, vars, depth):
    if depth == 0:
        return ("var", r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", bitwise(r, vars, depth - 1))
    return (op, bitwise(r, vars, depth - 1), bitwise(r, vars, depth - 1))


def expand(e, r, p):
    """Rewrite bitwise operations in arithmetic context into arithmetic of
    their operands, each with probability p; operands stay bitwise."""
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


def subst(e, f):
    """Replace each variable node v by f(v)."""
    if e[0] == "var":
        return f(e[1])
    if e[0] == "num":
        return e
    return (e[0],) + tuple(subst(a, f) for a in e[1:])


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


def noisy(r, v, vars, k):
    """v + Z with Z a zero MBA of k pairs."""
    z = zero_terms(r, vars, k)
    r.shuffle(z)
    return ("add", ("var", v), sum_tree(z))


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
    sym = {"and": "&", "or": "|", "xor": "^", "add": "+", "sub": "-", "mul": "*"}[t]
    return f"({show(e[1])} {sym} {show(e[2])})"


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
    return {"and": a & b, "or": a | b, "xor": a ^ b, "add": a + b, "sub": a - b, "mul": a * b}[t] & M


def emit(r, obf, gt, vars):
    for _ in range(64):
        env = {v: r.getrandbits(64) for v in vars}
        assert ev(obf, env) == ev(gt, env), (show(obf), show(gt))
    return f"{show(obf)},{show(gt)}"


def many_vars(r):
    vs = r.sample(VARS8, 8)
    gt = [(r.choice([1, 2, 3, -1, -2]), bitwise(r, vs[2 * i : 2 * i + 2], 1)) for i in range(4)]
    obf = [(c, expand(e, r, 0.8)) for c, e in gt] + zero_terms(r, VARS8, 4)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), VARS8)


def arith_leaves(r):
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1]), bitwise(r, vs, r.choice([1, 2]))), (r.choice([1, 3, -1]), ("var", r.choice(vs)))]
    obf = [(c, subst(expand(e, r, 0.7), lambda v: noisy(r, v, vs, 1))) for c, e in gt] + zero_terms(r, vs, 2)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def product(r):
    vs = ["x", "y", "z"]
    x, y = r.sample(vs, 2)
    a, b = ("var", x), ("var", y)
    pieces = [
        (("and", a, b), ("or", a, b)),
        (("and", a, ("not", b)), ("and", ("not", a), b)),
    ]
    prod = sum_tree([(1, ("mul", expand(p, r, 0.8), expand(q, r, 0.8))) for p, q in pieces])
    c = r.choice([1, 2, 3, -1])
    w = r.choice(vs)
    gt = sum_tree([(1, ("mul", a, b)), (c, ("var", w))])
    obf = sum_tree([(1, prod), (c, ("var", w))] + zero_terms(r, vs, 2))
    return emit(r, obf, gt, vs)


def repeated(r):
    vs = ["x", "y", "z", "w"]
    inner = bitwise(r, ["x", "y"], 1)
    t = sum_tree([(1, expand(inner, r, 1.0))] + zero_terms(r, ["x", "y"], 2))
    other = ("var", r.choice(["z", "w"]))
    op = r.choice(["and", "or", "xor"])
    c = r.choice([2, 3, -1, -2])
    gt = sum_tree([(c, inner), (1, (op, inner, other))])
    obf = sum_tree([(c, t), (1, (op, t, other))] + zero_terms(r, vs, 1))
    return emit(r, obf, gt, vs)


def two_level(r):
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1]), bitwise(r, vs, 1)), (r.choice([1, -1, 2]), ("var", r.choice(vs)))]
    z = zero_terms(r, vs, 2)
    z = [(c, subst(e, lambda v: noisy(r, v, vs, 1))) for c, e in z]
    obf = [(c, expand(e, r, 0.7)) for c, e in gt] + z
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def chained_vars(r):
    """Terms over overlapping variable pairs, so all 8 leaves form one group."""
    vs = r.sample(VARS8, 8)
    gt = [(r.choice([1, 2, 3, -1, -2]), bitwise(r, [vs[i], vs[i + 1]], 1)) for i in range(0, 7, 2)]
    gt += [(r.choice([1, -1, 2]), bitwise(r, [vs[i], vs[i + 1]], 1)) for i in (1, 3, 5)]
    obf = [(c, expand(e, r, 0.8)) for c, e in gt] + zero_terms(r, VARS8, 4)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), VARS8)


def deep_bitwise(r):
    """Depth-3 bitwise terms over 4 variables, fully expanded, plus noise."""
    vs = ["x", "y", "z", "w"]
    gt = [(r.choice([1, 2, -1, 3]), bitwise(r, vs, 3)) for _ in range(2)]
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 3)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def noisy_product(r):
    """x*y written with the product identity, with noisy operands."""
    vs = ["x", "y", "z"]
    x, y = r.sample(vs, 2)
    a, b = ("var", x), ("var", y)
    pieces = [
        (("and", a, b), ("or", a, b)),
        (("and", a, ("not", b)), ("and", ("not", a), b)),
    ]
    noise = lambda v: noisy(r, v, vs, 1)
    prod = sum_tree([(1, ("mul", subst(expand(p, r, 0.8), noise), subst(expand(q, r, 0.8), noise))) for p, q in pieces])
    c = r.choice([1, 2, 3, -1])
    w = r.choice(vs)
    gt = sum_tree([(1, ("mul", a, b)), (c, ("var", w))])
    obf = sum_tree([(1, prod), (c, ("var", w))] + zero_terms(r, vs, 1))
    return emit(r, obf, gt, vs)


def poly_degree2(r):
    """Sum of two products of bitwise terms, each factor written as a linear MBA."""
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1]), ("mul", bitwise(r, vs, 1), bitwise(r, vs, 1))) for _ in range(2)]

    def lin(e):
        return sum_tree([(1, expand(e, r, 0.9))] + zero_terms(r, vs, 1))

    obf = [(c, ("mul", lin(e[1]), lin(e[2]))) for c, e in gt] + zero_terms(r, vs, 1)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def wide_arith_leaves(r):
    """Arithmetic leaves over 4 variables inside bitwise terms of depth 2."""
    vs = ["x", "y", "z", "w"]
    gt = [(r.choice([1, 2, -1]), bitwise(r, vs, 2)), (r.choice([1, 3, -1]), ("var", r.choice(vs)))]
    obf = [(c, subst(expand(e, r, 0.7), lambda v: noisy(r, v, vs, 2))) for c, e in gt] + zero_terms(r, vs, 2)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def const(r, wide):
    if wide:
        return r.getrandbits(64)
    return r.choice([r.randrange(1, 256), r.randrange(1, 1 << 16), r.choice([0xF0, 0x0F, 0x5C, 0x33, 0xCC, 0xFF00])])


def cbitwise(r, vars, depth, wide=False):
    """Bitwise expression where an operand is a constant half of the time."""
    if depth == 0:
        return ("var", r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", cbitwise(r, vars, depth - 1, wide))
    other = ("num", const(r, wide)) if r.random() < 0.5 else cbitwise(r, vars, depth - 1, wide)
    return (op, cbitwise(r, vars, depth - 1, wide), other)


def czero_terms(r, vars, k, depth=2, wide=False):
    out = []
    for _ in range(k):
        c = r.choice([1, 2, 3, 5, -1, -2, -3, -7])
        f = cbitwise(r, vars, depth, wide)
        out += [(c, f), (-c, expand(f, r, 0.9))]
    return out


def semi_case(r, vs, depth, k, wide=False, konst=False):
    gt = [(r.choice([1, 1, 2, 3, -1, -2]), cbitwise(r, vs, depth, wide))]
    if r.random() < 0.5:
        gt.append((r.choice([1, 2, -1, 3]), ("var", r.choice(vs))))
    if konst:
        gt.append((1, ("num", const(r, wide))))
    obf = [(c, expand(e, r, 0.7)) for c, e in gt] + czero_terms(r, vs, k, 2, wide)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def semi_4vars(r):
    return semi_case(r, ["x", "y", "z", "w"], 2, 3)


def semi_wide_consts(r):
    return semi_case(r, ["x", "y"], 2, 3, wide=True)


def semi_deep(r):
    return semi_case(r, ["x", "y", "z"], 3, 3)


def semi_offset(r):
    return semi_case(r, ["x", "y"], 2, 3, konst=True)


def semi_arith_leaves(r):
    """Semi-linear ground truth with variables replaced by v + Z, Z a semi-linear zero."""
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1]), cbitwise(r, vs, 2)), (r.choice([1, 3, -1]), ("var", r.choice(vs)))]

    def noise(v):
        z = czero_terms(r, vs, 1, 1)
        return ("add", ("var", v), sum_tree(z))

    obf = [(c, subst(expand(e, r, 0.7), noise)) for c, e in gt] + czero_terms(r, vs, 2)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    r = random.Random(1)
    sections = [
        ("8-variable linear MBA,groundtruth", many_vars),
        ("arithmetic leaves (v + zero MBA),groundtruth", arith_leaves),
        ("product identity x*y,groundtruth", product),
        ("repeated obfuscated subterm,groundtruth", repeated),
        ("two-level zero MBA substitution,groundtruth", two_level),
        ("8 variables in one chained group,groundtruth", chained_vars),
        ("depth-3 bitwise over 4 variables,groundtruth", deep_bitwise),
        ("product with noisy operands,groundtruth", noisy_product),
        ("sum of products of linear MBA,groundtruth", poly_degree2),
        ("4-variable arithmetic leaves,groundtruth", wide_arith_leaves),
        ("semi-linear over 4 variables,groundtruth", semi_4vars),
        ("semi-linear with 64-bit constants,groundtruth", semi_wide_consts),
        ("depth-3 semi-linear over 3 variables,groundtruth", semi_deep),
        ("semi-linear with a constant offset,groundtruth", semi_offset),
        ("semi-linear arithmetic leaves,groundtruth", semi_arith_leaves),
    ]
    for name, f in sections:
        print(f"#{name}")
        for _ in range(n):
            print(f(r))


main()
