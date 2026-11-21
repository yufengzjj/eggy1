"""Run examples/bench over datasets split into small shards, many shards at a time.

Each shard is one bench process with -j 1 on a few cases, sized from the timings so far to
finish in about --target seconds, so htop shows one process per running shard and the shard
directory in its command line. Results are merged into one table in the bench format.

    python -I scripts/bench-shards.py -j 26 -o out/run1 bench-data/a.txt bench-data/b_u32.txt@u32

A file may end in @TYPE to bench it with that numeric type (default: -n).
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

STATUSES = ["solved", "partial", "unchanged", "timeout", "error", "wrong", "badgt", "total"]


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
            cases.append((ty, stem, header, lines[k * n // keep]))
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
        d = Path(self.args.out) / "shards" / f"{sid:05d}"
        d.mkdir(parents=True, exist_ok=True)
        by_file = {}
        for _, stem, header, line in cases:
            by_file.setdefault(stem, []).append((header, line))
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
               "-f", str(d / "fails.txt")] + self.args.extra + files
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
            fp = d / "fails.txt"
            if fp.exists():
                self.fails.append((sid, fp.read_text(encoding="utf-8")))
            self.done_cases += len(cases)
            self.done_secs += secs
            self.done_bytes += sum(len(c[3]) for c in cases)
            if not self.args.keep:
                shutil.rmtree(d, ignore_errors=True)

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


def parse_table(text):
    rows = {}
    for line in text.splitlines():
        if not line.startswith("| ") or line.startswith("| dataset") or line.startswith("| TOTAL"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 3 + len(STATUSES):
            continue
        counts = [int(c) for c in cells[2:2 + len(STATUSES)]]
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
    for t in (types if len(types) > 1 else []) + ["ALL"]:
        counts, secs = totals[t]
        out.append(f"| TOTAL | {t} |  | " + " | ".join(map(str, counts)) + f" | {secs / max(counts[-1], 1):.2f} |")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+", help="dataset files, optionally FILE@TYPE")
    ap.add_argument("-n", "--num-type", default="i64")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count())
    ap.add_argument("-t", "--timeout", type=float, default=10.0, help="seconds per case")
    ap.add_argument("-l", "--limit", type=int, help="at most this many cases per section, evenly spaced")
    ap.add_argument("-o", "--out", required=True, help="output directory (table.txt, fails.txt, progress.txt)")
    ap.add_argument("--target", type=float, default=45.0, help="estimated seconds per shard")
    ap.add_argument("--max-cases", type=int, default=400, help="at most this many cases per shard")
    ap.add_argument("--first-cases", type=int, default=20, help="shard size before any timing is known")
    ap.add_argument("--bench", help="bench binary (default: build it with cargo and use target/release/examples/bench)")
    ap.add_argument("--keep", action="store_true", help="keep the shard directories")
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
    text = table(runner.rows)
    if runner.failed_shards:
        text += f"\nshards without a result (see shards/*/out.txt with --keep): {runner.failed_shards}\n"
    (out / "table.txt").write_text(text, encoding="utf-8")
    (out / "fails.txt").write_text("".join(f for _, f in sorted(runner.fails)), encoding="utf-8")
    (out / "progress.txt").write_text(runner.progress() + "\nDONE\n", encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
