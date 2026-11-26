"""Run examples/bench over datasets split into small shards, many shards at a time.

Each shard is one bench process with -j 1 on a few cases, sized from the timings so far to
finish in about --target seconds, so htop shows one process per running shard and the shard
directory in its command line. Results are merged into one table in the bench format.

    python -I scripts/bench-shards.py -j 26 -o out/run1 bench-data/a.txt bench-data/b_u32.txt@u32

A file may end in @TYPE to bench it with that numeric type (default: -n). With --cases LIST
(written by scripts/pick-quick.py) only the listed cases run, with their indices in the whole
section, so the results compare with a full run in bench-diff.py:

    python -I scripts/bench-shards.py -j 26 -o out/quick --cases scripts/quick-cases.tsv

Timeouts are timing-sensitive under load, so after the main pass every timed-out case is run
again on its own, --retry-jobs at a time, and the table counts the retry's result; the first
pass's table is kept in table-first.txt. results.tsv has one line per case (bench -r format, the
index counted in the whole dataset section), with the retry's line for retried cases.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

STATUSES = ["solved", "partial", "unchanged", "cut", "timeout", "error", "wrong", "badgt", "total"]
RESULT_COLUMNS = ["type", "file", "section", "index", "hash", "status", "size_in", "size_gt", "size_out", "secs",
                  "output"]


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


def load(spec, default_type, limit):
    path, _, ty = spec.partition("@")
    ty = ty or default_type
    stem = Path(path).stem
    sections = []
    header, in_data = "", False
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("#"):
                header, in_data = line[1:].strip(), False
                continue
            if not in_data:
                sections.append((header, []))
                in_data = True
            if split_cols(line) is None:
                continue
            sections[-1][1].append(line)
    cases = []
    for header, lines in sections:
        n = len(lines)
        keep = min(limit or n, n)
        for k in range(keep):
            cases.append((ty, stem, header, lines[k * n // keep], k * n // keep))
    return cases


class Runner:
    def __init__(self, args, cases):
        self.args = args
        self.cases = cases
        self.next = 0
        self.lock = threading.Lock()
        self.done_cases = 0
        self.done_secs = 0.0
        self.done_bytes = 0
        self.running = {}
        self.rows = {}
        self.fails = []
        self.results = {}
        self.shard_id = 0
        self.failed_shards = []
        self.start = time.time()

    def take(self):
        """Next shard: consecutive cases of one type, sized by the per-case and per-byte rate so far."""
        with self.lock:
            if self.next >= len(self.cases):
                return None
            a = self.args
            if self.done_cases:
                per_case = self.done_secs / self.done_cases
                per_byte = self.done_secs / max(self.done_bytes, 1)
            else:
                per_case, per_byte = None, None
            ty = self.cases[self.next][0]
            i, est = self.next, 0.0
            while i < len(self.cases) and self.cases[i][0] == ty and i - self.next < a.max_cases:
                size = len(self.cases[i][3])
                if per_case is None:
                    cost = a.target / a.first_cases
                else:
                    cost = max(per_case * 0.5, per_byte * size)
                if i > self.next and est + cost > a.target:
                    break
                est += cost
                i += 1
            shard = (self.shard_id, ty, self.cases[self.next : i], est)
            self.next = i
            self.shard_id += 1
            return shard

    def run_shard(self, shard):
        sid, ty, cases, _ = shard
        d = Path(self.args.out) / "shards" / (f"{sid:05d}" if isinstance(sid, int) else sid)
        d.mkdir(parents=True, exist_ok=True)
        by_file = {}
        for c in cases:
            by_file.setdefault(c[1], []).append((c[2], c[3]))
        files = []
        for stem, items in by_file.items():
            p = d / f"{stem}.txt"
            out, last = [], None
            for header, line in items:
                if header != last:
                    out.append("#" + header)
                    last = header
                out.append(line)
            p.write_text("\n".join(out) + "\n", encoding="utf-8")
            files.append(str(p))
        cmd = [self.args.bench, "-j", "1", "-n", ty, "-t", str(self.args.timeout),
               "-f", str(d / "fails.txt"), "-r", str(d / "results.tsv")] + self.args.extra + files
        with self.lock:
            self.running[sid] = (time.time(), len(cases))
        t0 = time.time()
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding="utf-8")
        secs = time.time() - t0
        (d / "out.txt").write_text(r.stdout + r.stderr, encoding="utf-8")
        rows = parse_table(r.stdout)
        with self.lock:
            del self.running[sid]
            if r.returncode != 0 or not rows:
                self.failed_shards.append(sid)
            for key, (counts, s) in rows.items():
                key = (ty,) + key
                old = self.rows.setdefault(key, ([0] * len(STATUSES), 0.0))
                self.rows[key] = ([x + y for x, y in zip(old[0], counts)], old[1] + s)
            rp = d / "results.tsv"
            if rp.exists():
                self.add_results(cases, rp.read_text(encoding="utf-8"))
            fp = d / "fails.txt"
            if fp.exists():
                for entry in split_fails(fp.read_text(encoding="utf-8")):
                    self.fails.append((sid, ty, entry))
            self.done_cases += len(cases)
            self.done_secs += secs
            self.done_bytes += sum(len(c[3]) for c in cases)
            if not self.args.keep:
                shutil.rmtree(d, ignore_errors=True)

    def add_results(self, cases, text):
        slots = {}
        for c in cases:
            slots.setdefault((c[1], c[2], case_hash(split_cols(c[3])[0])), []).append(c)
        for line in text.splitlines()[1:]:
            cols = line.split("\t")
            if len(cols) != len(RESULT_COLUMNS):
                continue
            queue = slots.get((cols[1], cols[2], cols[4]))
            if queue:
                c = queue.pop(0)
                cols[3] = str(c[4])
                self.results[c] = cols

    def worker(self):
        while True:
            shard = self.take()
            if shard is None:
                return
            self.run_shard(shard)

    def progress(self):
        with self.lock:
            el = time.time() - self.start
            n = len(self.cases)
            rate = self.done_cases / el if el > 0 and self.done_cases else 0
            eta = (n - self.done_cases) / rate if rate else 0
            bad = sum(self.rows[k][0][STATUSES.index("wrong")] + self.rows[k][0][STATUSES.index("error")]
                      for k in self.rows)
            oldest = max((time.time() - t for t, _ in self.running.values()), default=0)
            return (f"{self.done_cases}/{n} cases, {len(self.running)} shards running "
                    f"(oldest {oldest:.0f}s), {el:.0f}s elapsed, ETA {eta:.0f}s, wrong+error {bad}")


FAIL_HEAD = re.compile(r"\[(\w+)\] (.*?) / (.*)")


def split_fails(text):
    entries = []
    for line in text.splitlines(keepends=True):
        if line.startswith("[") or not entries:
            entries.append(line)
        else:
            entries[-1] += line
    return entries


# Statuses of cases that ran out of time (`cut`: stopped at bench --time-limit), rerun alone.
RETRIED = ("timeout", "cut")


def timeout_case(ty, entry):
    """(type, stem, section, line) of a RETRIED entry in a bench fails file, else None."""
    lines = entry.splitlines()
    m = FAIL_HEAD.fullmatch(lines[0])
    if not m or m.group(1) not in RETRIED or len(lines) < 3:
        return None
    if not (lines[1].startswith("  in:  ") and lines[2].startswith("  gt:  ")):
        return None
    return (ty, m.group(2), m.group(3), lines[1][7:] + "," + lines[2][7:])


def retry_timeouts(runner):
    """Run each case that ran out of time again on its own and replace its count and fail entry."""
    a = runner.args
    timed_out = {}
    for c, cols in runner.results.items():
        if cols[5] in RETRIED:
            timed_out.setdefault((c[0], c[1], c[2], cols[4]), []).append(c)
    todo = []
    for i, (sid, ty, entry) in enumerate(runner.fails):
        case = timeout_case(ty, entry)
        if case:
            same = timed_out.get(case[:3] + (case_hash(split_cols(case[3])[0]),))
            todo.append((i, same.pop(0) if same else case + (-1,)))
    if not todo or a.retry_jobs <= 0:
        return None
    ra = argparse.Namespace(**vars(a))
    ra.timeout = a.retry_timeout or a.timeout
    retry = Runner(ra, [c for _, c in todo])
    retry.next = len(todo)
    shards = [(f"retry{k:05d}", c[0], [c], 0.0) for k, (_, c) in enumerate(todo)]
    lock = threading.Lock()

    def worker():
        while True:
            with lock:
                if not shards:
                    return
                shard = shards.pop(0)
            retry.run_shard(shard)

    threads = [threading.Thread(target=worker, daemon=True) for _ in range(a.retry_jobs)]
    for t in threads:
        t.start()
    out = Path(a.out)
    while any(t.is_alive() for t in threads):
        time.sleep(5)
        line = f"retrying {len(todo)} cases out of time, {a.retry_jobs} at a time: {retry.done_cases} done"
        (out / "progress.txt").write_text(line + "\n", encoding="utf-8")
        print(line, file=sys.stderr, flush=True)
    removed = {}
    for _, c in todo:
        cols = runner.results.get(c)
        status, secs = (cols[5], float(cols[9] or a.timeout)) if cols else ("timeout", a.timeout)
        r = removed.setdefault((c[0], c[1], c[2]), ([0] * len(STATUSES), [0.0]))
        r[0][STATUSES.index(status)] += 1
        r[0][-1] += 1
        r[1][0] += secs
    for key, (counts, secs) in retry.rows.items():
        old = runner.rows[key]
        rm, rs = removed.get(key, ([0] * len(STATUSES), [0.0]))
        runner.rows[key] = ([x + y - z for x, y, z in zip(old[0], counts, rm)], old[1] - rs[0] + secs)
    new_fails = {}
    for sid, ty, entry in retry.fails:
        new_fails.setdefault(sid, []).append((sid, ty, entry))
    drop = {i for i, _ in todo}
    kept = [f for i, f in enumerate(runner.fails) if i not in drop]
    for k, (i, _) in enumerate(todo):
        kept += [(runner.fails[i][0], ty, e) for _, ty, e in new_fails.get(f"retry{k:05d}", [])]
    runner.fails = kept
    runner.results.update(retry.results)
    runner.failed_shards += retry.failed_shards
    still = sum(c[STATUSES.index(st)] for c, _ in retry.rows.values() for st in RETRIED)
    return f"retried {len(todo)} cases out of time on their own, {a.retry_jobs} at a time: {still} still out of time\n"


def parse_table(text):
    """Rows of a bench table by (dataset, section): counts in the order of STATUSES (columns
    by the header's names, so a bench with fewer statuses reads too) and summed seconds."""
    rows, names = {}, None
    for line in text.splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if line.startswith("| dataset"):
            names = cells[2:-1]
            continue
        if names is None or not line.startswith("| ") or line.startswith("| TOTAL") or len(cells) != 3 + len(names):
            continue
        got = dict(zip(names, cells[2:-1]))
        counts = [int(got.get(s, 0)) for s in STATUSES]
        rows[(cells[0], cells[1])] = (counts, float(cells[-1]) * counts[-1])
    return rows


def table(rows):
    out = ["| type | dataset | section | " + " | ".join(STATUSES) + " | avg s |",
           "|---|---|---|" + "---|" * len(STATUSES) + "---|"]
    totals = {}
    for key in sorted(rows):
        counts, secs = rows[key]
        out.append(f"| {key[0]} | {key[1]} | {key[2]} | " + " | ".join(map(str, counts))
                   + f" | {secs / max(counts[-1], 1):.2f} |")
        for t in (key[0], "ALL"):
            old = totals.setdefault(t, ([0] * len(STATUSES), 0.0))
            totals[t] = ([x + y for x, y in zip(old[0], counts)], old[1] + secs)
    types = sorted(t for t in totals if t != "ALL")
    for t in (types if len(types) > 1 else []) + (["ALL"] if totals else []):
        counts, secs = totals[t]
        out.append(f"| TOTAL | {t} |  | " + " | ".join(map(str, counts)) + f" | {secs / max(counts[-1], 1):.2f} |")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", help="dataset files, optionally FILE@TYPE")
    ap.add_argument("-n", "--num-type", default="i64")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    ap.add_argument("-t", "--timeout", type=float, default=10.0, help="seconds per case")
    ap.add_argument("-l", "--limit", type=int, help="at most this many cases per section, evenly spaced")
    ap.add_argument("--cases", help="only these cases (scripts/pick-quick.py output); files default to its datasets")
    ap.add_argument("--data", default="bench-data", help="dataset directory for --cases without files")
    ap.add_argument("-o", "--out", required=True, help="output directory (table.txt, fails.txt, progress.txt)")
    ap.add_argument("--target", type=float, default=45.0, help="estimated seconds per shard")
    ap.add_argument("--max-cases", type=int, default=400, help="at most this many cases per shard")
    ap.add_argument("--first-cases", type=int, default=20, help="shard size before any timing is known")
    ap.add_argument("--bench", help="bench binary (default: build it with cargo and use target/release/examples/bench)")
    ap.add_argument("--keep", action="store_true", help="keep the shard directories")
    ap.add_argument("--retry-jobs", type=int, default=4, help="timed-out cases rerun at a time (0: no retry)")
    ap.add_argument("--retry-timeout", type=float, help="seconds per case in the retry (default: -t)")
    args, args.extra = ap.parse_known_args()
    if args.bench is None:
        subprocess.run(["cargo", "build", "--release", "-q", "--example", "bench"], check=True)
        meta = subprocess.run(["cargo", "metadata", "--format-version", "1", "--no-deps"],
                              stdout=subprocess.PIPE, text=True, check=True).stdout
        target = json.loads(meta)["target_directory"]
        args.bench = str(Path(target) / "release" / "examples" / ("bench.exe" if os.name == "nt" else "bench"))
    out = Path(args.out)
    if (out / "shards").exists():
        shutil.rmtree(out / "shards")
    out.mkdir(parents=True, exist_ok=True)

    if args.cases:
        keep = set()
        for line in Path(args.cases).read_text(encoding="utf-8").splitlines()[1:]:
            ty, stem, section, index, _ = line.split("	")
            keep.add((ty, stem, section, int(index)))
        specs = args.files or sorted({f"{Path(args.data) / stem}.txt@{ty}" for ty, stem, _, _ in keep})
        cases = [c for spec in specs for c in load(spec, args.num_type, None) if (c[0], c[1], c[2], c[4]) in keep]
    else:
        cases = [c for spec in args.files for c in load(spec, args.num_type, args.limit)]
    runner = Runner(args, cases)
    print(f"{len(cases)} cases, {args.jobs} shards at a time", file=sys.stderr, flush=True)
    threads = [threading.Thread(target=runner.worker, daemon=True) for _ in range(args.jobs)]
    for t in threads:
        t.start()
    while any(t.is_alive() for t in threads):
        time.sleep(5)
        line = runner.progress()
        (out / "progress.txt").write_text(line + "\n", encoding="utf-8")
        print(line, file=sys.stderr, flush=True)
    runner.fails.sort(key=lambda f: f[0])
    first = table(runner.rows)
    note = retry_timeouts(runner)
    text = table(runner.rows)
    if note:
        (out / "table-first.txt").write_text(first, encoding="utf-8")
        text += "\n" + note
    if runner.failed_shards:
        text += f"\nshards without a result (see shards/*/out.txt with --keep): {runner.failed_shards}\n"
    (out / "table.txt").write_text(text, encoding="utf-8")
    (out / "fails.txt").write_text("".join(e for _, _, e in runner.fails), encoding="utf-8")
    rows = ["\t".join(RESULT_COLUMNS)] + ["\t".join(runner.results[c]) for c in cases if c in runner.results]
    (out / "results.tsv").write_text("\n".join(rows) + "\n", encoding="utf-8")
    (out / "progress.txt").write_text(runner.progress() + "\nDONE\n", encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
