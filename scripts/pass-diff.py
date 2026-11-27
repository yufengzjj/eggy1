"""Where the time goes when a pass is turned off: compare the per-pass counts of a run with
the default pipeline to a run with `--passes off=NAME` (or any other change), both with
`--stats`.

    python -I scripts/pass-diff.py out/base-stats.tsv out/no_lowbits-stats.tsv [--top 25]
        [--by mul] [--min-cases 20] [--all]

Only cases in both files that did not time out in either are compared. Each row is a key's
time and count in the first run, in the second, and the change (second - first), sorted by
the size of the time change: a pass turned off shows its own time saved, and the passes
whose inputs it changed show the time they gained or lost (`lowbits` off: `semi_linear`
runs less often). Two tables whose times do not overlap within each: the stages of a run
(egglog rounds, pre-pass candidates, polish passes), and the passes inside the pre-pass with
their own time (`pass/NAME/self`, which the candidates' times include). --all adds the
times with nested passes and the run from the printed result (which repeats the stages).
--by repeats the tables per group of an input feature (powers of two).
"""

import argparse
from collections import defaultdict


def bucket(v):
    v = int(v)
    if v < 2:
        return f"{v:>6}"
    lo = 1 << (v.bit_length() - 1)
    return f"{lo}-{2 * lo - 1}".rjust(6)


def read(path):
    cases = {}
    for line in open(path, encoding="utf-8"):
        cols = line.rstrip("\n").split("\t")
        if len(cols) < 10:
            continue
        counts = {}
        for cell in filter(None, cols[9].split(";")):
            key, _, val = cell.partition("=")
            n, _, secs = val.partition(":")
            counts[key] = (int(n), float(secs))
        feats = dict(f.split("=") for f in cols[8].split(",") if "=" in f)
        cases[tuple(cols[:4])] = (cols[4], feats, counts)
    return cases


def stage(key):
    return key.startswith("egglog/") or (key.startswith("pre/") and key.endswith("/made")) or (key.startswith("polish_") and key.endswith("/run"))


def own(key):
    return key.startswith("pass/") and key.endswith("/self")


def table(title, pairs, top, every):
    a, b = defaultdict(lambda: [0, 0.0]), defaultdict(lambda: [0, 0.0])
    for ca, cb in pairs:
        for side, counts in ((a, ca), (b, cb)):
            for key, (n, secs) in counts.items():
                side[key][0] += n
                side[key][1] += secs
    keys = set(a) | set(b)
    parts = [("stages", stage), ("passes, own time", own)]
    if every:
        parts.append(("other times", lambda k: not stage(k) and not own(k) and (a[k][1] or b[k][1])))
    print(f"## {title}: {len(pairs)} cases")
    for name, pick in parts:
        ks = [k for k in keys if pick(k)]
        ta, tb = sum(a[k][1] for k in ks), sum(b[k][1] for k in ks)
        print(f"  {name}: {ta:.1f}s -> {tb:.1f}s ({tb - ta:+.1f}s)")
        print(f"    {'key':40s} {'secs':>9s} {'secs':>9s} {'change':>9s} {'count':>9s} {'count':>9s} {'change':>9s}")
        for k in sorted(ks, key=lambda k: -abs(b[k][1] - a[k][1]))[:top]:
            print(f"    {k:40s} {a[k][1]:9.2f} {b[k][1]:9.2f} {b[k][1] - a[k][1]:+9.2f} {a[k][0]:9d} {b[k][0]:9d} {b[k][0] - a[k][0]:+9d}")
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("first", help="stats file of the first run (e.g. the default pipeline)")
    ap.add_argument("second", help="stats file of the second run (e.g. a pass turned off)")
    ap.add_argument("--top", type=int, default=25, help="rows per table")
    ap.add_argument("--by", help="also one table per group of this input feature")
    ap.add_argument("--min-cases", type=int, default=1, help="hide groups with fewer cases")
    ap.add_argument("--all", action="store_true", help="also show times with nested passes")
    a = ap.parse_args()
    first, second = read(a.first), read(a.second)
    common = [k for k in first if k in second and "timeout" not in (first[k][0], second[k][0])]
    pairs = [(first[k][2], second[k][2]) for k in common]
    table("all", pairs, a.top, a.all)
    if a.by:
        groups = defaultdict(list)
        for k in common:
            v = first[k][1].get(a.by)
            groups[bucket(v) if v is not None else "     ?"].append((first[k][2], second[k][2]))
        for g in sorted(groups, key=lambda g: (0, int(g.strip().split("-")[0])) if g.strip()[0].isdigit() else (1, 0)):
            if len(groups[g]) >= a.min_cases:
                table(f"{a.by} {g.strip()}", groups[g], a.top, a.all)


if __name__ == "__main__":
    main()
