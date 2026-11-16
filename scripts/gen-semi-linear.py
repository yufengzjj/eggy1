"""Generate semi-linear MBA cases (bitwise operations with constants) as
`obfuscated, groundtruth` lines for examples/bench.rs.

Each case is a small ground truth plus zero terms c*(f - g): f is a random
bitwise expression with constants and g is f rewritten by identities such as
a&b = a+b-(a|b). The ground truth is rewritten the same way.

Usage: python scripts/gen-semi-linear.py [cases-per-section] > bench-data/semi_linear.txt
"""

import random
import sys

M = (1 << 64) - 1


def const(r):
    return r.choice([r.randrange(1, 256), r.randrange(1, 1 << 16), r.choice([0xF0, 0x0F, 0x5C, 0x33, 0xCC, 0xFF00])])


def bitwise(r, vars, depth):
    if depth == 0:
        return ("var", r.choice(vars))
    op = r.choice(["and", "or", "xor", "not", "and", "or", "xor"])
    if op == "not":
        return ("not", bitwise(r, vars, depth - 1))
    other = ("num", const(r)) if r.random() < 0.5 else bitwise(r, vars, depth - 1)
    return (op, bitwise(r, vars, depth - 1), other)


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
    sym = {"and": "&", "or": "|", "xor": "^", "add": "+", "sub": "-"}[t]
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
    return {"and": a & b, "or": a | b, "xor": a ^ b, "add": a + b, "sub": a - b}[t] & M


def terms_str(terms):
    out = ""
    for c, e in terms:
        s = show(e) if c in (1, -1) else f"{abs(c)}*{show(e)}"
        out += (" - " if c < 0 else " + ") + s if out else ("-" if c < 0 else "") + s
    return out


def case(r, vars):
    gt = [(r.choice([1, 1, 2, 3, -1, -2]), bitwise(r, vars, r.choice([1, 2])))]
    if r.random() < 0.5:
        gt.append((r.choice([1, 2, -1, 3]), ("var", r.choice(vars))))
    obf = [(c, expand(e, r, 0.7)) for c, e in gt]
    for _ in range(r.randint(2, 4)):
        c = r.choice([1, 2, 3, 5, -1, -2, -3, -7])
        f = bitwise(r, vars, 2)
        obf += [(c, f), (-c, expand(f, r, 0.9))]
    r.shuffle(obf)
    total = lambda ts, env: sum(c * ev(e, env) for c, e in ts) & M
    for _ in range(64):
        env = {v: r.getrandbits(64) for v in vars}
        assert total(obf, env) == total(gt, env)
    return terms_str(obf), terms_str(gt)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    r = random.Random(1)
    for vars in (["x"], ["x", "y"], ["x", "y", "z"]):
        print(f"#{len(vars)}-variable semi-linear MBA,groundtruth")
        for _ in range(n):
            print(",".join(case(r, vars)))


main()
