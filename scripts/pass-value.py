"""What a pass is worth to the final results: compare a run with the default pipeline to
runs with one pass (or a group) turned off by `--passes`.

    python -I scripts/pass-value.py out/base rerun_input=out/no_rerun printed=out/no_printed \
        [--features stats.tsv --by mul] [--min-cases 20]

Each directory holds a bench run's results.tsv. Per case, loss = max(0, log2(out / gt))
(0 when solved; an error counts as the input unchanged), so large expressions do not
outweigh small ones. Cases that time out in either run are only counted (timeouts with
and without the pass), since a case near the time limit times out by chance. For the pass:
  benefit = loss without it - loss with it   (summed over cases; negative: it hurts)
  cost    = seconds with it - seconds without it
  ROI     = benefit per second of cost
also the cases where keeping it gives a smaller or larger result, the output nodes it saves
(counting gains past the ground truth, which benefit does not), and solved with/without.
With --features (a stats file of any run over the same cases, `bench --stats`), --by
groups the cases by an input feature in powers of two.
"""

import argparse
import csv
import math
from collections import defaultdict


def bucket(v):
    v = int(v)
    if v < 2:
        return f"{v:>6}"
    lo = 1 << (v.bit_length() - 1)
    return f"{lo}-{2 * lo - 1}".rjust(6)


def key(ty, file, section, index):
    return (ty, file, section, index)


def load(d):
    rows = {}
    for r in csv.DictReader(open(f"{d}/results.tsv", encoding="utf-8"), delimiter="\t"):
        if r["status"] in ("wrong", "badgt"):
            continue
        s_in, s_gt = int(r["size_in"] or 0), int(r["size_gt"] or 0)
        out = int(r["size_out"]) if r["size_out"] and r["status"] not in ("timeout", "error") else s_in
        loss = max(0.0, math.log2(out / s_gt)) if s_gt and out else 0.0
        rows[key(r["type"], r["file"], r["section"], r["index"])] = (loss, float(r["secs"] or 0), out, r["status"] == "solved", r["status"] == "timeout")
    return rows


def features(path):
    out = {}
    for line in open(path, encoding="utf-8"):
        cols = line.rstrip("\n").split("\t")
        if len(cols) >= 10:
            out[key(*cols[:4])] = dict(f.split("=") for f in cols[8].split(",") if "=" in f)
    return out


def row(name, pairs):
    t_on, t_off = sum(on[4] for on, _ in pairs), sum(off[4] for _, off in pairs)
    pairs = [(on, off) for on, off in pairs if not on[4] and not off[4]]
    benefit = sum(off[0] - on[0] for on, off in pairs)
    cost = sum(on[1] - off[1] for on, off in pairs)
    smaller = sum(on[2] < off[2] for on, off in pairs)
    larger = sum(on[2] > off[2] for on, off in pairs)
    nodes = sum(off[2] - on[2] for on, off in pairs)
    solved_on, solved_off = sum(on[3] for on, _ in pairs), sum(off[3] for _, off in pairs)
    off_timeouts, t_off = t_off, sum(off[1] for _, off in pairs)
    roi = f"{benefit / cost:8.3f}" if cost > 0 else ("    free" if benefit > 0 else "       -")
    print(f"  {name:24s} {len(pairs):7d} {solved_on - solved_off:+6d} {smaller:6d} {larger:6d} {benefit:+9.2f} {nodes:+8d} {cost:+8.1f}s {100 * cost / max(t_off, 1e-9):+6.1f}% {roi}  {t_on}/{off_timeouts}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("base", help="run with the default pipeline")
    ap.add_argument("off", nargs="+", help="NAME=DIR: a run with NAME turned off")
    ap.add_argument("--features", help="stats file with the cases' input features")
    ap.add_argument("--by", help="group by this input feature (needs --features)")
    ap.add_argument("--min-cases", type=int, default=1, help="hide groups with fewer cases")
    a = ap.parse_args()
    base = load(a.base)
    feats = features(a.features) if a.features else {}
    header = "cases solved smaller larger  benefit    nodes     cost  cost%     ROI  timeouts with/without"
    for spec in a.off:
        name, _, d = spec.partition("=")
        off = load(d)
        common = [k for k in base if k in off]
        print(f"## {name}: {header}")
        row("all", [(base[k], off[k]) for k in common])
        if a.by:
            groups = defaultdict(list)
            for k in common:
                v = feats.get(k, {}).get(a.by)
                groups[bucket(v) if v is not None else "?"].append((base[k], off[k]))
            for g in sorted(groups, key=lambda g: (0, int(g.strip().split("-")[0])) if g.strip()[0].isdigit() else (1, 0)):
                if len(groups[g]) >= a.min_cases:
                    row(f"{a.by} {g.strip()}", groups[g])
        print()


if __name__ == "__main__":
    main()
