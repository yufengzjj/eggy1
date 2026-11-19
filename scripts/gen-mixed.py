"""Generate MBA cases that combine the pre-pass techniques, as
`obfuscated, groundtruth` lines for examples/bench.rs (64-bit).

Sections:
- linear MBA whose bitwise terms are hidden by the T-function identity
  p & q = p & -(p & -(p & q));
- nested polynomial MBA, f1 * (f2 * f3 + f4);
- semi-linear MBA over 5 and 6 variables;
- semi-linear MBA inside a left shift;
- bitwise operations of two semi-linear terms, (x + K) & (y ^ C);
- linear MBA with a product of a variable and a linear MBA, x * L(y, z) + L'.

Helpers come from gen-harder.py. Every case is checked on random inputs.

Usage: python -I scripts/gen-mixed.py [cases-per-section] > bench-data/mixed.txt
"""

import importlib.util
import os
import random
import sys

sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location("gen_harder", os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen-harder.py"))
H = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(H)
M = H.M


def show(e):
    if e[0] == "shl":
        return f"({show(e[1])} << {hex(e[2])})"
    if e[0] in ("var", "num"):
        return H.show(e)
    if e[0] in ("not", "neg"):
        return ("~" if e[0] == "not" else "-") + f"({show(e[1])})"
    sym = {"and": "&", "or": "|", "xor": "^", "add": "+", "sub": "-", "mul": "*"}[e[0]]
    return f"({show(e[1])} {sym} {show(e[2])})"


def ev(e, env):
    t = e[0]
    if t == "shl":
        return ev(e[1], env) << e[2] & M
    if t in ("var", "num"):
        return H.ev(e, env)
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


def hide_and(r, e):
    """Rewrite some p & q into p & -(p & -(p & q)), a T-function identity."""
    if e[0] in ("var", "num"):
        return e
    sub = (e[0],) + tuple(hide_and(r, a) if isinstance(a, tuple) else a for a in e[1:])
    if sub[0] == "and" and r.random() < 0.7:
        p, q = sub[1], sub[2]
        return ("and", p, ("neg", ("and", p, ("neg", ("and", p, q)))))
    return sub


def tfunc_linear(r):
    vs = ["x", "y", "z"]
    gt = [(r.choice([1, 2, -1, 3]), H.bitwise(r, vs, 2)) for _ in range(2)]
    obf = [(c, hide_and(r, H.expand(e, r, 0.5))) for c, e in gt] + H.zero_terms(r, vs, 2)
    r.shuffle(obf)
    return emit(r, H.sum_tree(obf), H.sum_tree(gt), vs)


def nested_poly(r):
    vs = ["x", "y", "z"]
    f = [H.bitwise(r, vs, 1) for _ in range(4)]
    gt = ("mul", f[0], ("add", ("mul", f[1], f[2]), f[3]))
    inner = ("add", ("mul", H.lin(r, f[1], vs), H.lin(r, f[2], vs)), H.lin(r, f[3], vs))
    obf = ("mul", H.lin(r, f[0], vs), inner)
    return emit(r, H.sum_tree([(1, obf)] + H.zero_terms(r, vs, 1)), gt, vs)


def semi_wide(n):
    def gen(r):
        vs = ["x", "y", "z", "w", "v", "u"][:n]
        gt = [(r.choice([1, 2, 3, -1, -2]), H.bitwise(r, r.sample(vs, 3), 2, 0.5)) for _ in range(2)]
        obf = [(c, H.expand(e, r, 0.7)) for c, e in gt] + H.zero_terms(r, vs, 3, 0.5)
        r.shuffle(obf)
        return emit(r, H.sum_tree(obf), H.sum_tree(gt), vs)

    return gen


def semi_shift(r):
    vs = ["x", "y", "z"]
    k = r.randrange(1, 9)
    inner = [(r.choice([1, 2, -1]), H.bitwise(r, vs, 2, 0.5)), (r.choice([1, -1]), ("var", r.choice(vs)))]
    gt = ("shl", H.sum_tree(inner), k)
    obf_inner = [(c, H.expand(e, r, 0.7)) for c, e in inner] + H.zero_terms(r, vs, 2, 0.5)
    r.shuffle(obf_inner)
    obf = H.sum_tree([(1, ("shl", H.sum_tree(obf_inner), k))] + H.zero_terms(r, vs, 1))
    return emit(r, obf, gt, vs)


def bitwise_of_semi(r):
    vs = ["x", "y", "z"]
    x, y, z = r.sample(vs, 3)
    a = ("add", ("var", x), ("num", H.const(r)))
    b = (r.choice(["xor", "and", "or"]), ("var", y), ("num", H.const(r)))
    op = r.choice(["and", "or", "xor"])
    gt = (op, a, b)
    obf = (op, ("add", H.lin(r, ("var", x), vs, 1, 0.5), ("num", a[2][1])), H.lin(r, b, vs, 1, 0.5))
    return emit(r, H.sum_tree([(1, obf)] + H.zero_terms(r, vs, 1, 0.5)), gt, vs)


def var_times_linear(r):
    vs = ["x", "y", "z"]
    f = H.bitwise(r, ["y", "z"], 1)
    g = H.bitwise(r, vs, 2)
    c = r.choice([1, 2, -1, 3])
    gt = H.sum_tree([(1, ("mul", ("var", "x"), f)), (c, g)])
    obf = [(1, ("mul", ("var", "x"), H.lin(r, f, vs))), (c, H.expand(g, r, 0.8))] + H.zero_terms(r, vs, 2)
    r.shuffle(obf)
    return emit(r, H.sum_tree(obf), gt, vs)


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    r = random.Random(2)
    sections = [
        ("linear MBA with T-function identities,groundtruth", tfunc_linear),
        ("nested polynomial MBA,groundtruth", nested_poly),
        ("semi-linear over 5 variables,groundtruth", semi_wide(5)),
        ("semi-linear over 6 variables,groundtruth", semi_wide(6)),
        ("semi-linear inside a shift,groundtruth", semi_shift),
        ("bitwise operation of semi-linear terms,groundtruth", bitwise_of_semi),
        ("variable times linear MBA,groundtruth", var_times_linear),
    ]
    for name, f in sections:
        print(f"#{name}")
        for _ in range(n):
            print(f(r))


main()
