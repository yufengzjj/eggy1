"""Generate MBA cases past the current limits of the pre-pass, as
`obfuscated, groundtruth` lines for examples/bench.rs.

Sections:
- linear MBA over 12 variables in chained pairs (more than pairwise takes);
- linear MBA over 7 variables with 3-variable terms (degree 3, more than 6 leaves);
- depth-3 semi-linear MBA over 4 variables;
- products of three linear MBAs (degree 3);
- bitwise operations of two obfuscated arithmetic terms, (x + y) & (x ^ z);
- three levels of (v + Z) substitution;
- products of semi-linear factors, (x & K) * (y | C);
- depth-4 bitwise terms over 3 variables.

Zero MBAs are sums c*(f - g), with g the bitwise expression f rewritten by
identities such as a&b = a+b-(a|b). Every case is checked on random inputs.

Usage: python -I scripts/gen-harder.py [cases-per-section] > bench-data/harder.txt
"""

import random
import sys

M = (1 << 64) - 1
VARS = list("abcdefghijkl")


def const(r):
    return r.choice([r.randrange(1, 256), r.randrange(1, 1 << 16), r.choice([0xF0, 0x0F, 0x5C, 0x33, 0xCC, 0xFF00])])


def bitwise(r, vars, depth, cprob=0.0):
    """Random bitwise expression; an operand is a constant with probability cprob."""
    if depth == 0:
        return ("var", r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", bitwise(r, vars, depth - 1, cprob))
    other = ("num", const(r)) if r.random() < cprob else bitwise(r, vars, depth - 1, cprob)
    return (op, bitwise(r, vars, depth - 1, cprob), other)


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


def zero_terms(r, vars, k, cprob=0.0):
    out = []
    for _ in range(k):
        c = r.choice([1, 2, 3, 5, -1, -2, -3, -7])
        f = bitwise(r, r.sample(vars, min(len(vars), r.choice([2, 3]))), 2, cprob)
        out += [(c, f), (-c, expand(f, r, 1.0))]
    return out


def lin(r, e, vars, k=1, cprob=0.0):
    """e written as a linear MBA: expanded, plus a zero MBA of k pairs."""
    z = zero_terms(r, vars, k, cprob)
    r.shuffle(z)
    return sum_tree([(1, expand(e, r, 0.9))] + z)


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


def wide_chain(r):
    vs = r.sample(VARS, 12)
    gt = [(r.choice([1, 2, 3, -1, -2]), bitwise(r, [vs[i], vs[i + 1]], 1)) for i in range(11)]
    obf = [(c, expand(e, r, 0.8)) for c, e in gt] + zero_terms(r, vs, 4)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def triple_terms(r):
    vs = VARS[:7]
    gt = [(r.choice([1, 2, -1, 3]), bitwise(r, vs[i : i + 3], 2)) for i in (0, 2, 4)]
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 3)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def semi_deep4(r):
    vs = ["x", "y", "z", "w"]
    gt = [(r.choice([1, 1, 2, 3, -1, -2]), bitwise(r, vs, 3, 0.5))]
    if r.random() < 0.5:
        gt.append((r.choice([1, 2, -1, 3]), ("var", r.choice(vs))))
    obf = [(c, expand(e, r, 0.7)) for c, e in gt] + zero_terms(r, vs, 3, 0.5)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def product3(r):
    vs = ["x", "y", "z"]
    fs = [bitwise(r, vs, 1) for _ in range(3)]
    gt = ("mul", ("mul", fs[0], fs[1]), fs[2])
    obf = ("mul", ("mul", lin(r, fs[0], vs), lin(r, fs[1], vs)), lin(r, fs[2], vs))
    return emit(r, sum_tree([(1, obf)] + zero_terms(r, vs, 1)), gt, vs)


def bitwise_of_arith(r):
    vs = ["x", "y", "z"]
    x, y, z = r.sample(vs, 3)
    a = r.choice([("add", ("var", x), ("var", y)), ("sub", ("var", x), ("var", y)), ("mul", ("num", 3), ("var", x))])
    b = bitwise(r, [x, z], 1)
    op = r.choice(["and", "or", "xor"])
    gt = (op, a, b)

    def obf_arith(e):
        if e[0] == "mul":
            return ("mul", e[1], lin(r, e[2], vs))
        return (e[0], lin(r, e[1], vs), lin(r, e[2], vs))

    obf = (op, obf_arith(a), lin(r, b, vs))
    return emit(r, sum_tree([(1, obf)] + zero_terms(r, vs, 2)), gt, vs)


def three_level(r):
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1]), bitwise(r, vs, 1)), (r.choice([1, -1, 2]), ("var", r.choice(vs)))]
    z = zero_terms(r, vs, 2)
    z = [(c, subst(e, lambda v: noisy(r, v, vs, 1))) for c, e in z]
    z = [(c, subst(e, lambda v: noisy(r, v, vs, 1))) for c, e in z]
    obf = [(c, expand(e, r, 0.7)) for c, e in gt] + z
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def semi_product(r):
    vs = ["x", "y"]
    f = (r.choice(["and", "or", "xor"]), ("var", "x"), ("num", const(r)))
    g = (r.choice(["and", "or", "xor"]), ("var", "y"), ("num", const(r)))
    gt = ("mul", f, g)
    obf = ("mul", lin(r, f, vs, 1, 0.5), lin(r, g, vs, 1, 0.5))
    return emit(r, sum_tree([(1, obf)] + zero_terms(r, vs, 1, 0.5)), gt, vs)


def deep4(r):
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1, 3]), bitwise(r, vs, 4))]
    obf = [(c, expand(e, r, 0.9)) for c, e in gt] + zero_terms(r, vs, 3)
    r.shuffle(obf)
    return emit(r, sum_tree(obf), sum_tree(gt), vs)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    r = random.Random(1)
    sections = [
        ("12 variables in chained pairs,groundtruth", wide_chain),
        ("7 variables with 3-variable terms,groundtruth", triple_terms),
        ("depth-3 semi-linear over 4 variables,groundtruth", semi_deep4),
        ("product of three linear MBAs,groundtruth", product3),
        ("bitwise operation of arithmetic terms,groundtruth", bitwise_of_arith),
        ("three-level zero MBA substitution,groundtruth", three_level),
        ("product of semi-linear factors,groundtruth", semi_product),
        ("depth-4 bitwise over 3 variables,groundtruth", deep4),
    ]
    for name, f in sections:
        print(f"#{name}")
        for _ in range(n):
            print(f(r))


if __name__ == "__main__":
    main()
