"""Compare two bench runs case by case.

    python -I scripts/bench-diff.py out/old out/new [-l 20] [--show [-w 300]]
    python -I scripts/bench-diff.py out/run          # size totals of one run only

Each argument is a bench-shards.py output directory (its results.tsv) or a file written by
bench -r. Cases are matched by type, dataset, section and input hash. Lists status changes and,
for cases whose status did not change, output size changes, worse first, then totals and the
average seconds per section, and a size table per section: summed output and ground-truth
sizes, the cases strictly below / above ground truth, and the summed size_out - size_gt (cases
without an output, such as timeouts, count with their input size). --show prints each listed case's input (from fails.txt next to the
results, else the dataset file under --data) and both outputs.
"""

import argparse
import sys
from collections import defaultdict
from pathlib import Path

RANK = {"solved": 0, "badgt": 1, "partial": 1, "unchanged": 2, "cut": 2, "timeout": 3, "error": 4, "wrong": 5}
SIZED = {"solved", "partial", "unchanged", "cut", "badgt"}


def case_hash(text):
    """Same as case_hash in examples/bench.rs."""
    h = 0xcbf29ce484222325
    for b in text.encode("utf-8"):
        h = ((h ^ b) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return f"{h >> 16:012x}"


def split_cols(line):
    depth = 0
    for i, ch in enumerate(line):
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            return line[:i].strip(), line[i + 1 :]
    return None


def results_path(arg):
    p = Path(arg)
    return p / "results.tsv" if p.is_dir() else p


def load(arg):
    """Rows keyed by (type, file, section, hash, n), n counting repeated inputs."""
    path = results_path(arg)
    lines = path.read_text(encoding="utf-8").splitlines()
    cols = lines[0].split("\t")
    rows, seen = {}, defaultdict(int)
    for line in lines[1:]:
        r = dict(zip(cols, line.split("\t")))
        if len(r) != len(cols):
            continue
        r["secs"] = float(r["secs"])
        base = (r["type"], r["file"], r["section"], r["hash"])
        rows[base + (seen[base],)] = r
        seen[base] += 1
    return rows


def size(r):
    return int(r["size_out"]) if r["status"] in SIZED and r["size_out"] else None


def out_size(r):
    """Output size, or the input size when the case has no output (timeout, error, wrong)."""
    s = size(r)
    return int(r["size_in"]) if s is None else s


def size_totals(rows):
    """Per section and in total: [cases, sum out, sum gt, below gt, above gt, sum out - gt, no output]."""
    tot = defaultdict(lambda: [0] * 7)
    for key, r in rows.items():
        if not r.get("size_gt"):
            continue
        so, sg = out_size(r), int(r["size_gt"])
        for k in (key[:3], ("total", "", "")):
            t = tot[k]
            t[0] += 1
            t[1] += so
            t[2] += sg
            t[3] += so < sg
            t[4] += so > sg
            t[5] += so - sg
            t[6] += size(r) is None
    return tot


def size_table(runs):
    """runs: list of (label, rows); one column group per run."""
    tots = [size_totals(rows) for _, rows in runs]
    keys = sorted(set().union(*tots) - {("total", "", "")}) + [("total", "", "")]
    groups = ["sum out", "sum gt", "below gt", "above gt", "out - gt", "no output"]
    labels = [g if len(runs) == 1 else f"{g} {label}" for g in groups for label, _ in runs]
    print("| type | dataset | section | cases | " + " | ".join(labels) + " |")
    print("|---|---|---|---" + "|---" * len(labels) + "|")
    for k in keys:
        cells = [str(max(t[k][0] for t in tots))]
        for i in range(1, 7):
            cells += [str(t[k][i]) if k in t else "-" for t in tots]
        print(f"| {k[0]} | {k[1]} | {k[2]} | " + " | ".join(cells) + " |")


def compare(o, n):
    """Negative when the new result is better."""
    so, sn = size(o), size(n)
    if (o["status"] == n["status"] or "badgt" in (o["status"], n["status"])) and so is not None and sn is not None:
        return sn - so
    return RANK[n["status"]] - RANK[o["status"]]


class Inputs:
    """Finds a case's input in fails.txt next to the results, else in the dataset file."""

    def __init__(self, dirs, data):
        self.data = Path(data)
        self.known = {}
        for d in dirs:
            fp = results_path(d).parent / "fails.txt"
            if not fp.exists():
                continue
            for line in fp.read_text(encoding="utf-8").splitlines():
                if line.startswith("  in:  "):
                    self.known.setdefault(case_hash(line[7:].strip()), line[7:].strip())
        self.files = {}

    def get(self, stem, h):
        if h in self.known:
            return self.known[h]
        if stem not in self.files:
            self.files[stem] = {}
            p = self.data / f"{stem}.txt"
            if p.exists():
                for line in p.read_text(encoding="utf-8").splitlines():
                    line = line.strip()
                    cols = split_cols(line) if line and not line.startswith("#") else None
                    if cols:
                        self.files[stem].setdefault(case_hash(cols[0]), cols[0])
        return self.files[stem].get(h, "(input not found)")


def fmt_size(r):
    s = size(r)
    return "-" if s is None else str(s)


def describe(key, o, n):
    t, f, sec, h, _ = key
    return (f"{t} {f} / {sec} #{n['index']} {h}: {o['status']} {fmt_size(o)} -> {n['status']} {fmt_size(n)}"
            f"  ({o['secs']:.2f}s -> {n['secs']:.2f}s)")


def cut(text, width):
    return text if width <= 0 or len(text) <= width else text[:width] + f" ... ({len(text)} chars)"


def listing(title, items, limit, show, inputs, width):
    print(f"{title} ({len(items)}):")
    for key, o, n in items[:limit] if limit > 0 else items:
        print("  " + describe(key, o, n))
        if show:
            print(f"      in:  {cut(inputs.get(key[1], key[3]), width)}")
            print(f"      old: {cut(o['output'] or '-', width)}")
            print(f"      new: {cut(n['output'] or '-', width)}")
    if 0 < limit < len(items):
        print(f"  ... {len(items) - limit} more")
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("old", help="old run: bench-shards.py output directory or bench -r file")
    ap.add_argument("new", nargs="?", help="new run, same forms (omitted: only the size table of old)")
    ap.add_argument("-l", "--limit", type=int, default=20, help="cases listed per listing (0: all)")
    ap.add_argument("--show", action="store_true", help="print input and both outputs of listed cases")
    ap.add_argument("--data", default="bench-data", help="dataset directory for inputs not in fails.txt")
    ap.add_argument("-w", "--width", type=int, default=300, help="cut shown expressions to this many characters (0: no cut)")
    ap.add_argument("--no-sizes", action="store_true", help="leave out the size table")
    a = ap.parse_args()
    if a.new is None:
        size_table([("", load(a.old))])
        return
    old, new = load(a.old), load(a.new)
    inputs = Inputs([a.old, a.new], a.data)

    status_changes, size_worse, size_better = [], [], []
    transitions = defaultdict(lambda: defaultdict(int))
    sections = defaultdict(lambda: {"n": 0, "better": 0, "worse": 0, "old_s": [0.0, 0], "new_s": [0.0, 0]})
    better = worse = same = 0
    for key, r in old.items():
        s = sections[key[:3]]["old_s"]
        s[0] += r["secs"]
        s[1] += 1
    for key, r in new.items():
        s = sections[key[:3]]["new_s"]
        s[0] += r["secs"]
        s[1] += 1
    for key in old.keys() & new.keys():
        o, n = old[key], new[key]
        c = compare(o, n)
        sec = sections[key[:3]]
        sec["n"] += 1
        if c < 0:
            better += 1
            sec["better"] += 1
        elif c > 0:
            worse += 1
            sec["worse"] += 1
        else:
            same += 1
        if o["status"] != n["status"]:
            status_changes.append((c, key, o, n))
            transitions[key[:3]][f"{o['status']}->{n['status']}"] += 1
        elif c > 0:
            size_worse.append((c, key, o, n))
        elif c < 0:
            size_better.append((c, key, o, n))

    status_changes.sort(key=lambda x: (-x[0], x[1]))
    size_worse.sort(key=lambda x: (-x[0], x[1]))
    size_better.sort(key=lambda x: (x[0], x[1]))
    strip = lambda items: [x[1:] for x in items]
    print(f"status changes by section ({len(status_changes)}):")
    for sec in sorted(transitions):
        moves = ", ".join(f"{k} {v}" for k, v in sorted(transitions[sec].items(), key=lambda kv: -kv[1]))
        print(f"  {sec[0]} {sec[1]} / {sec[2]}: {moves}")
    print()
    listing("status changes, worse first", strip(status_changes), a.limit, a.show, inputs, a.width)
    listing("size worse, same status", strip(size_worse), a.limit, a.show, inputs, a.width)
    listing("size better, same status", strip(size_better), a.limit, a.show, inputs, a.width)

    print("| type | dataset | section | cases | better | worse | avg s old | avg s new | change |")
    print("|---|---|---|---|---|---|---|---|---|")
    for sec in sorted(sections):
        s = sections[sec]
        avg_o = s["old_s"][0] / s["old_s"][1] if s["old_s"][1] else float("nan")
        avg_n = s["new_s"][0] / s["new_s"][1] if s["new_s"][1] else float("nan")
        print(f"| {sec[0]} | {sec[1]} | {sec[2]} | {s['n']} | {s['better']} | {s['worse']} | {avg_o:.2f} | {avg_n:.2f}"
              f" | {avg_n - avg_o:+.2f} |")
    only_old, only_new = len(old.keys() - new.keys()), len(new.keys() - old.keys())
    print(f"\nbetter {better}, worse {worse}, same {same}"
          + (f"; only in old {only_old}, only in new {only_new}" if only_old or only_new else ""))


if __name__ == "__main__":
    sys.exit(main())
