"""Summarize the candidate-source counts `bench` writes with EGGY_STATS=FILE.

    EGGY_STATS=out/run/stats.tsv python -I scripts/bench-shards.py ... -o out/run ...
    python -I scripts/stats.py out/run/stats.tsv [--by section] [--status partial]

Each line is one case: type, file, section, index, status, sizes in/gt/out, then
`key=count:secs;...`. Keys:
  pre/NAME/made     pre-pass candidate NAME computed (count = calls, time spent)
  pre/NAME/differs  it gave a form other than the first rebuild
  pre/NAME/main     it was the candidate the round started from (smallest)
  pre/NAME/kept     it was unioned beside the main one
  egglog/first|later|rerun_input  saturation rounds and their time
  round/minimal     rounds skipped because the rebuild was proved minimal
  round/extra       extra rounds while the pre-pass still changed the result
  polish/NAME/run|won  final-polish pass runs and runs that made the result smaller
  rerun_printed/run, rerun_printed/won/ORIGIN  the second run from the printed result
  final/ORIGIN      where the returned result came from (one per case)
Times of the second run from the printed result also appear under its inner keys.
"""

import argparse
import sys
from collections import defaultdict


def read(paths, status):
    for path in paths:
        for line in open(path, encoding="utf-8"):
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 9:
                continue
            ty, file, section, index, st, s_in, s_gt, s_out, cells = cols[:9]
            if status and st not in status:
                continue
            counts = {}
            for cell in filter(None, cells.split(";")):
                key, _, val = cell.partition("=")
                n, _, secs = val.partition(":")
                counts[key] = (int(n), float(secs))
            yield {"type": ty, "file": file, "section": section.split(",")[0], "status": st}, counts


def summarize(cases, title):
    total = defaultdict(lambda: [0, 0.0, 0])
    for _, counts in cases:
        for key, (n, secs) in counts.items():
            t = total[key]
            t[0] += n
            t[1] += secs
            t[2] += 1
    n_cases = len(cases)
    print(f"## {title}: {n_cases} cases")
    final = {k[len("final/"):]: v[0] for k, v in total.items() if k.startswith("final/")}
    print("\nfinal result from (cases):")
    for origin, n in sorted(final.items(), key=lambda kv: -kv[1]):
        print(f"  {n:7d}  {100 * n / max(n_cases, 1):5.1f}%  {origin}")
    names = sorted({k.split("/")[1] for k in total if k.startswith("pre/")})
    print("\npre-pass candidates: calls, seconds, differs, main, kept, final")
    for name in sorted(names, key=lambda m: -total[f"pre/{m}/made"][1]):
        g = lambda f: total[f"pre/{name}/{f}"]
        print(f"  {name:20s} {g('made')[0]:7d} {g('made')[1]:9.1f}s {g('differs')[0]:7d} {g('main')[0]:7d} {g('kept')[0]:7d} {final.get('pre/' + name, 0):7d}")
    print("\nrounds: count, seconds")
    for key in sorted(k for k in total if k.startswith(("egglog/", "round/", "rerun_printed/"))):
        print(f"  {key:40s} {total[key][0]:7d} {total[key][1]:9.1f}s")
    passes = sorted({k.split("/")[1] for k in total if k.startswith("polish/")})
    print("\npolish passes: runs, seconds, won, final")
    for name in sorted(passes, key=lambda p: -total[f"polish/{p}/run"][1]):
        run, won = total[f"polish/{name}/run"], total[f"polish/{name}/won"]
        print(f"  {name:20s} {run[0]:7d} {run[1]:9.1f}s {won[0]:7d} {final.get('polish/' + name, 0):7d}")
    print()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--by", choices=["type", "file", "section"], help="also summarize per group")
    ap.add_argument("--status", action="append", help="only cases with this status (repeatable)")
    a = ap.parse_args()
    cases = list(read(a.files, a.status))
    if not cases:
        sys.exit("no cases")
    summarize(cases, "all")
    if a.by:
        groups = defaultdict(list)
        for c in cases:
            groups[c[0][a.by]].append(c)
        for g in sorted(groups):
            summarize(groups[g], g)


if __name__ == "__main__":
    main()
