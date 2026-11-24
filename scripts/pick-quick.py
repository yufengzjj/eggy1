"""Pick a small bench set from full runs: a few cases of different form per section.

    python -I scripts/pick-quick.py out/full out/h3 -o scripts/quick-cases.tsv [-k 3] [--keep scripts/quick-regressions.tsv --keep scripts/quick-hard.tsv]

Each argument is a bench-shards.py output directory (its results.tsv). Per dataset section,
cases are grouped by form (operators used, number of variables, size to a factor of 2); the
-k most common forms each give the case nearest their median time, and every case not solved
in the run is added, as is every case listed in a --keep file (cases that once regressed or
were unsolved). Run the set with `bench-shards.py --cases scripts/quick-cases.tsv`.
"""

import argparse
import math
import re
import sys
from collections import defaultdict
from pathlib import Path

OPS = ["mulhi", "<<", ">>", "+", "-", "*", "/", "%", "&", "|", "^", "~"]
TOKEN = re.compile(r"mulhi|<<|>>|0x[0-9a-fA-F]+|\d+|[A-Za-z_]\w*|\S")


def split_cols(line):
    depth = 0
    for i, ch in enumerate(line):
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            return line[:i].strip(), line[i + 1 :]
    return None


def inputs(path):
    """(section, index) -> input of a dataset file, indices counted as bench-shards.py does."""
    out = {}
    header, index = "", None
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            header, index = line[1:].strip(), None
            continue
        if index is None:
            index = 0
        cols = split_cols(line)
        if cols is None:
            continue
        out[(header, index)] = cols[0]
        index += 1
    return out


def form(text, size):
    toks = TOKEN.findall(text)
    ops = frozenset(t for t in toks if t in OPS)
    names = {t for t in toks if re.fullmatch(r"[A-Za-z_]\w*", t) and t != "mulhi"}
    return (tuple(sorted(ops)), len(names), int(math.log2(max(size, 1))))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("runs", nargs="+")
    ap.add_argument("-o", "--out", required=True)
    ap.add_argument("-k", type=int, default=3, help="forms per section")
    ap.add_argument("--data", default="bench-data")
    ap.add_argument("--keep", action="append", default=[], help="TSV of cases (type, file, section, index) always included; repeatable")
    args = ap.parse_args()
    keep = set()
    for path in args.keep:
        for line in Path(path).read_text(encoding="utf-8").splitlines()[1:]:
            if line:
                ty, f, sec, idx = line.split("	")[:4]
                keep.add((ty, f, sec, int(idx)))

    rows = []
    for run in args.runs:
        p = Path(run)
        p = p / "results.tsv" if p.is_dir() else p
        lines = p.read_text(encoding="utf-8").splitlines()
        cols = lines[0].split("\t")
        rows += [dict(zip(cols, l.split("\t"))) for l in lines[1:] if l]

    texts = {}
    sections = defaultdict(list)
    for r in rows:
        f = r["file"]
        if f not in texts:
            texts[f] = inputs(Path(args.data) / f"{f}.txt")
        r["form"] = form(texts[f][(r["section"], int(r["index"]))], int(r["size_in"] or 0))
        sections[(r["type"], f, r["section"])].append(r)

    picked, secs = [], 0.0
    for key in sorted(sections):
        cases = sections[key]
        groups = defaultdict(list)
        for r in cases:
            groups[r["form"]].append(r)
        order = sorted(groups.values(), key=lambda g: (-len(g), min(int(r["index"]) for r in g)))
        chosen = []
        for g in order[: args.k]:
            g = sorted(g, key=lambda r: (float(r["secs"]), int(r["index"])))
            chosen.append(g[len(g) // 2])
        chosen += [r for r in cases if (r["status"] != "solved" or (r["type"], r["file"], r["section"], int(r["index"])) in keep) and r not in chosen]
        chosen.sort(key=lambda r: int(r["index"]))
        picked += chosen
        secs += sum(float(r["secs"]) for r in chosen)

    cols = ["type", "file", "section", "index", "hash"]
    with open(args.out, "w", encoding="utf-8", newline="\n") as f:
        f.write("\t".join(cols) + "\n")
        for r in picked:
            f.write("\t".join(r[c] for c in cols) + "\n")
    print(f"{len(picked)} cases from {len(rows)} in {len(sections)} sections, {secs:.0f} s in the runs",
          file=sys.stderr)


if __name__ == "__main__":
    main()
