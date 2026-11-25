"""Summarize the per-pass counts `bench --stats FILE` (or EGGY_STATS=FILE) writes.

    python -I scripts/bench-shards.py ... -o out/run --stats=/abs/out/run-stats.tsv ...
    python -I scripts/stats.py out/run-stats.tsv [--by section|vars|mul|...] [--status partial]
    python -I scripts/stats.py out/run-stats.tsv --pass semi_linear --by vars

Each line is one case: type, file, section, index, status, sizes in/gt/out, the input's
features (size, vars, depth, mul, bitconst, arith_in_bit, shift, div), then
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
  pass/NAME         a pass inside a rebuild (time includes the passes it calls)
  pass/NAME/self    its time without the passes it calls
  pass/NAME/smaller its result was smaller than its input
  pass/NAME/won     it gave the form kept among alternatives (semi/NAME: semi_linear's
                    candidate sources)
  pass/NAME/gain, pre/NAME/gain, polish/NAME/gain  nodes saved (in the count): a pass in
                    a chain its input's size less its result's, one of several
                    alternatives the next best one's size (or the input's) less the kept
                    one's, a pre-pass candidate the first rebuild's size less its own, a
                    polish pass the size it removed
survived is the part of gain in forms the final result still contains (a lower bound:
forms the rules rewrote count as lost); ROI is nodes saved per millisecond of the pass's time with the passes it calls (its
gain comes from them too); hit is the share of calls
that saved nodes. Gains are local: whether they reach the final result is measured by
scripts/pass-value.py from runs with the pass turned off.
Numeric features are grouped in powers of two (0, 1, 2-3, 4-7, ...) by --by.
"""

import argparse
import sys
from collections import defaultdict

SUFFIXES = ("/self", "/smaller", "/won", "/gain", "/survived")


def bucket(v):
    v = int(v)
    if v < 2:
        return f"{v:>6}"
    lo = 1 << (v.bit_length() - 1)
    return f"{lo}-{2 * lo - 1}".rjust(6)


def order(item):
    head = item[0].strip().split("-")[0]
    return (0, int(head), "") if head.isdigit() else (1, 0, item[0])


def read(paths, status):
    for path in paths:
        for line in open(path, encoding="utf-8"):
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 9:
                continue
            ty, file, section, index, st, s_in, s_gt, s_out = cols[:8]
            feats, cells = (cols[8], cols[9]) if len(cols) >= 10 else ("", cols[8])
            if status and st not in status:
                continue
            counts = {}
            for cell in filter(None, cells.split(";")):
                key, _, val = cell.partition("=")
                n, _, secs = val.partition(":")
                counts[key] = (int(n), float(secs))
            info = {"type": ty, "file": file, "section": section.split(",")[0], "status": st}
            for f in filter(None, feats.split(",")):
                k, _, v = f.partition("=")
                info[k] = bucket(v)
            yield info, counts


def totals(cases):
    total = defaultdict(lambda: [0, 0.0, 0])
    for _, counts in cases:
        for key, (n, secs) in counts.items():
            t = total[key]
            t[0] += n
            t[1] += secs
            t[2] += 1
    return total


def roi(gain, secs):
    return f"{gain / (1000 * secs):9.2f}" if secs > 0 else "        -"


def summarize(cases, title):
    total = totals(cases)
    n_cases = len(cases)
    print(f"## {title}: {n_cases} cases")
    final = {k[len("final/"):]: v[0] for k, v in total.items() if k.startswith("final/")}
    print("\nfinal result from (cases):")
    for origin, n in sorted(final.items(), key=lambda kv: -kv[1]):
        print(f"  {n:7d}  {100 * n / max(n_cases, 1):5.1f}%  {origin}")
    names = sorted({k.split("/")[1] for k in total if k.startswith("pre/")})
    print("\npre-pass candidates: calls, seconds, differs, main, kept, final, gain, ROI")
    for name in sorted(names, key=lambda m: -total[f"pre/{m}/made"][1]):
        g = lambda f: total[f"pre/{name}/{f}"]
        print(f"  {name:20s} {g('made')[0]:7d} {g('made')[1]:9.1f}s {g('differs')[0]:7d} {g('main')[0]:7d} {g('kept')[0]:7d} {final.get('pre/' + name, 0):7d} {g('gain')[0]:8d} {roi(g('gain')[0], g('made')[1])}")
    print("\nrounds: count, seconds")
    for key in sorted(k for k in total if k.startswith(("egglog/", "round/", "rerun_printed/"))):
        print(f"  {key:40s} {total[key][0]:7d} {total[key][1]:9.1f}s")
    passes = sorted({k.split("/")[1] for k in total if k.startswith("polish/")})
    print("\npolish passes: runs, seconds, won, final, gain, survived, ROI")
    for name in sorted(passes, key=lambda p: -total[f"polish/{p}/run"][1]):
        run, won, gain, surv = total[f"polish/{name}/run"], total[f"polish/{name}/won"], total[f"polish/{name}/gain"], total[f"polish/{name}/survived"]
        print(f"  {name:20s} {run[0]:7d} {run[1]:9.1f}s {won[0]:7d} {final.get('polish/' + name, 0):7d} {gain[0]:8d} {surv[0]:8d} {roi(gain[0], run[1])}")
    inner(total)
    print()


def inner(total, only=None):
    names = {k[len("pass/"):] for k in total if k.startswith("pass/")}
    names = [n for n in names if not n.endswith(SUFFIXES) and (only is None or n == only)]
    if not names:
        return
    print("\npasses inside rebuilds: calls, cases, seconds with nested passes, own seconds, smaller, won, gain, survived, ROI, survived ROI, hit")
    for name in sorted(names, key=lambda n: -total[f"pass/{n}/self"][1]):
        g = lambda f: total[f"pass/{name}{f}"]
        run, own, gain, surv = g(""), g("/self"), g("/gain")[0], g("/survived")[0]
        hits = g("/won")[0] if g("/won")[0] else (g("/smaller")[0] if gain else 0)
        print(f"  {name:22s} {run[0]:9d} {run[2]:6d} {run[1]:8.1f}s {own[1]:8.1f}s {g('/smaller')[0]:8d} {g('/won')[0]:8d} {gain:9d} {surv:8d} {roi(gain, run[1])} {roi(surv, run[1])} {100 * hits / max(run[0], 1):5.1f}%")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--by", help="also summarize per group: type, file, section, status or an input feature")
    ap.add_argument("--status", action="append", help="only cases with this status (repeatable)")
    ap.add_argument("--pass", dest="only", help="show only this pass of the inner-pass table, per --by group")
    a = ap.parse_args()
    cases = list(read(a.files, a.status))
    if not cases:
        sys.exit("no cases")
    groups = defaultdict(list)
    if a.by:
        for c in cases:
            groups[c[0].get(a.by, "?")].append(c)
    if a.only:
        for g, cs in [("all", cases)] + sorted(groups.items(), key=order):
            print(f"## {a.by or ''} {g}: {len(cs)} cases", end="")
            inner(totals(cs), a.only)
            print()
        return
    summarize(cases, "all")
    for g, _ in sorted(groups.items(), key=order):
        summarize(groups[g], f"{a.by} {g}")


if __name__ == "__main__":
    main()
