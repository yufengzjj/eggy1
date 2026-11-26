//! Benchmark on MBA datasets: simplify each case and compare it with the ground truth.
//!
//! Dataset lines are `obfuscated, groundtruth[, ...]`. Lines starting with `#` are
//! comments; the last comment before a run of data lines names that section.
//! Each case runs in a child process (this binary with `--one`) so it can be killed
//! on timeout and a panic only fails that case.

use clap::Parser;
use eggy1::dag::{NodeId, NodeTable};
use eggy1::eval::{self, NumType, Term};
use eggy1::expr_convert::infix_to_egglog;
use eggy1::{Cli, simplify};
use std::collections::BTreeMap;
use std::io::{BufRead, Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Parser, Clone)]
struct Args {
    /// Dataset files.
    files: Vec<String>,
    #[arg(short, long, default_value = "i64")]
    num_type: String,
    #[arg(short, long, default_value_t = 10)]
    iter_limit: usize,
    #[arg(short, long, default_value_t = 2)]
    max_restarts: usize,
    /// Seconds per case.
    #[arg(short, long, default_value_t = 10.0)]
    timeout: f64,
    /// Fraction of `--timeout` after which a case stops starting passes and gives the smallest
    /// form so far (`time_limit` in `--passes`, which can override it); such a result not
    /// solved is `cut`. 0: no limit.
    #[arg(long, default_value_t = 0.8)]
    time_limit: f64,
    /// Parallel cases (default: number of CPUs).
    #[arg(short, long)]
    jobs: Option<usize>,
    /// At most this many cases per section, evenly spaced.
    #[arg(short, long)]
    limit: Option<usize>,
    /// Write every case that is not `solved` to this file.
    #[arg(short, long)]
    fails: Option<String>,
    /// Write one tab-separated line per case to this file (columns in `RESULT_COLUMNS`).
    #[arg(short, long)]
    results: Option<String>,
    /// Print pre-pass statistics to stderr (child mode).
    #[arg(long)]
    trace: bool,
    /// Pass pipeline changes, as `eggy1 --passes`.
    #[arg(long, default_value = "")]
    passes: String,
    /// Append each case's per-pass counts and times to this file (`scripts/stats.py`
    /// summarizes it); the `EGGY_STATS` environment variable does the same.
    #[arg(long)]
    stats: Option<String>,
    /// Child mode: read input and ground truth from stdin, print one result line.
    #[arg(long, hide = true)]
    one: bool,
}

const RESULT_COLUMNS: &str = "type\tfile\tsection\tindex\thash\tstatus\tsize_in\tsize_gt\tsize_out\tsecs\toutput";

const STATUSES: [&str; 9] = ["solved", "partial", "unchanged", "cut", "timeout", "error", "wrong", "badgt", "total"];

struct Case {
    file: String,
    section: String,
    index: usize,
    input: String,
    truth: String,
}

struct Outcome {
    status: String,
    secs: f64,
    detail: String,
}

fn main() {
    let args = Args::parse();
    match eggy1::sched::Passes::parse_noting(&args.passes) {
        Err(e) => {
            eprintln!("--passes: {e}");
            std::process::exit(2);
        }
        Ok((_, warnings)) if !args.one => warnings.iter().for_each(|w| eprintln!("--passes: warning: {w}")),
        Ok(_) => {}
    }
    if args.one {
        run_one(&args);
    } else {
        run_all(&args);
    }
}

fn load(args: &Args) -> Vec<Case> {
    let mut cases = Vec::new();
    for file in &args.files {
        let text = std::fs::read_to_string(file).unwrap_or_else(|e| panic!("{file}: {e}"));
        let name = std::path::Path::new(file).file_stem().unwrap().to_string_lossy().to_string();
        let mut sections: Vec<(String, Vec<Case>)> = Vec::new();
        let mut header = String::new();
        let mut in_data = false;
        for line in text.lines().map(str::trim).filter(|l| !l.is_empty()) {
            if let Some(c) = line.strip_prefix('#') {
                header = c.trim().to_string();
                in_data = false;
                continue;
            }
            if !in_data {
                sections.push((header.clone(), Vec::new()));
                in_data = true;
            }
            let mut depth = 0i32;
            let mut cols = line.split(|ch| {
                depth += (ch == '(') as i32 - (ch == ')') as i32;
                ch == ',' && depth == 0
            });
            let (Some(input), Some(truth)) = (cols.next(), cols.next()) else {
                eprintln!("{file}: skipped line without ground truth: {line}");
                continue;
            };
            let section = header.clone();
            let sec = &mut sections.last_mut().unwrap().1;
            sec.push(Case {
                file: name.clone(),
                section,
                index: sec.len(),
                input: input.trim().to_string(),
                truth: truth.trim().to_string(),
            });
        }
        for (_, sec) in sections {
            let n = sec.len();
            let keep = args.limit.unwrap_or(n).min(n);
            let picks: Vec<usize> = (0..keep).map(|k| k * n / keep).collect();
            cases.extend(sec.into_iter().enumerate().filter(|(i, _)| picks.contains(i)).map(|(_, c)| c));
        }
    }
    cases
}

fn run_all(args: &Args) {
    let cases = Arc::new(load(args));
    let jobs = args.jobs.unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get()));
    let next = Arc::new(AtomicUsize::new(0));
    let results: Arc<Mutex<Vec<Option<Outcome>>>> =
        Arc::new(Mutex::new((0..cases.len()).map(|_| None).collect()));
    let started = Instant::now();
    eprintln!("{} cases, {jobs} jobs", cases.len());
    let workers: Vec<_> = (0..jobs)
        .map(|_| {
            let (cases, next, results, args) = (cases.clone(), next.clone(), results.clone(), args.clone());
            std::thread::spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    let Some(case) = cases.get(i) else { break };
                    let outcome = run_child(&args, case);
                    let mut r = results.lock().unwrap();
                    r[i] = Some(outcome);
                    let done = r.iter().filter(|o| o.is_some()).count();
                    if done % 100 == 0 || done == cases.len() {
                        eprintln!("{done}/{} ({:.0}s)", cases.len(), started.elapsed().as_secs_f64());
                    }
                }
            })
        })
        .collect();
    workers.into_iter().for_each(|w| w.join().unwrap());

    let results: Vec<Outcome> = Arc::try_unwrap(results).ok().unwrap().into_inner().unwrap().into_iter().map(Option::unwrap).collect();
    report(&cases, &results);
    if let Some(path) = &args.fails {
        let mut out = String::new();
        for (c, o) in cases.iter().zip(&results).filter(|(_, o)| o.status != "solved") {
            out += &format!("[{}] {} / {}\n  in:  {}\n  gt:  {}\n  {}\n", o.status, c.file, c.section, c.input, c.truth, o.detail);
        }
        std::fs::write(path, out).unwrap_or_else(|e| panic!("{path}: {e}"));
    }
    if let Some(path) = &args.results {
        let mut out = format!("{RESULT_COLUMNS}\n");
        for (c, o) in cases.iter().zip(&results) {
            out += &result_line(&args.num_type, c, o);
        }
        std::fs::write(path, out).unwrap_or_else(|e| panic!("{path}: {e}"));
    }
}

/// FNV-1a of the input, the case key within its file and section.
fn case_hash(input: &str) -> String {
    let h = input.bytes().fold(0xcbf29ce484222325u64, |h, b| (h ^ b as u64).wrapping_mul(0x100000001b3));
    format!("{:012x}", h >> 16)
}

fn result_line(ty: &str, c: &Case, o: &Outcome) -> String {
    let clean = |s: &str| s.replace(['\t', '\n', '\r'], " ");
    let (sizes, output) = match o.detail.strip_prefix("size in/gt/out ").and_then(|d| d.split_once(": ")) {
        Some((s, out)) => (s.split('/').map(str::to_string).collect::<Vec<_>>(), out),
        None => (vec![String::new(); 3], ""),
    };
    let (s_in, s_gt) = if sizes[0].is_empty() { term_sizes(c) } else { (sizes[0].clone(), sizes[1].clone()) };
    format!(
        "{ty}\t{}\t{}\t{}\t{}\t{}\t{s_in}\t{s_gt}\t{}\t{:.3}\t{}\n",
        clean(&c.file),
        clean(&c.section),
        c.index,
        case_hash(&c.input),
        o.status,
        sizes[2],
        o.secs,
        clean(output)
    )
}

fn term_sizes(c: &Case) -> (String, String) {
    let size = |s: &str| {
        std::panic::catch_unwind(|| {
            let egg = infix_to_egglog(s, true);
            if egg.is_empty() { String::new() } else { eval::size(&eval::parse(&egg)).to_string() }
        })
        .unwrap_or_default()
    };
    (size(&c.input), size(&c.truth))
}

fn report(cases: &[Case], results: &[Outcome]) {
    let mut rows: BTreeMap<(String, String), BTreeMap<&str, usize>> = BTreeMap::new();
    let mut secs: BTreeMap<(String, String), f64> = BTreeMap::new();
    for (c, o) in cases.iter().zip(results) {
        for key in [(c.file.clone(), c.section.clone()), ("TOTAL".to_string(), String::new())] {
            let row = rows.entry(key.clone()).or_default();
            *row.entry(STATUSES.iter().copied().find(|s| *s == o.status).unwrap()).or_default() += 1;
            *row.entry("total").or_default() += 1;
            *secs.entry(key).or_default() += o.secs;
        }
    }
    println!("| dataset | section | {} | avg s |", STATUSES.join(" | "));
    println!("|---|---|{}---|", "---|".repeat(STATUSES.len()));
    let total_key = ("TOTAL".to_string(), String::new());
    let total = rows.remove(&total_key).unwrap_or_default();
    for (key, row) in rows.iter().chain([(&total_key, &total)]) {
        let cells: Vec<String> = STATUSES.iter().map(|s| row.get(s).copied().unwrap_or(0).to_string()).collect();
        let avg = secs[key] / row["total"] as f64;
        println!("| {} | {} | {} | {avg:.2} |", key.0, key.1, cells.join(" | "));
    }
}

fn run_child(args: &Args, case: &Case) -> Outcome {
    let start = Instant::now();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--one", "-n", &args.num_type, "-i", &args.iter_limit.to_string(), "-m", &args.max_restarts.to_string(), "--passes", &args.passes])
        .args(["-t", &args.timeout.to_string(), "--time-limit", &args.time_limit.to_string()])
        .env("EGGY_CASE", format!("{}\t{}\t{}\t{}", args.num_type, case.file, case.section, case.index));
    if let Some(path) = &args.stats {
        command.env("EGGY_STATS", path);
    }
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn child");
    let mut stdin = child.stdin.take().unwrap();
    writeln!(stdin, "{}\n{}", case.input, case.truth).unwrap();
    drop(stdin);
    let pipe = |mut r: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut s = String::new();
            let _ = r.read_to_string(&mut s);
            s
        })
    };
    let out = pipe(Box::new(child.stdout.take().unwrap()));
    let err = pipe(Box::new(child.stderr.take().unwrap()));
    let limit = Duration::from_secs_f64(args.timeout);
    let status = loop {
        if let Some(s) = child.try_wait().unwrap() {
            break Some(s);
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let secs = start.elapsed().as_secs_f64();
    let (out, err) = (out.join().unwrap(), err.join().unwrap());
    match status {
        None => Outcome { status: "timeout".into(), secs, detail: String::new() },
        Some(s) if !s.success() => {
            let msg = err.lines().find(|l| l.contains("panicked") || l.contains("error")).unwrap_or("").to_string();
            Outcome { status: "error".into(), secs, detail: msg }
        }
        Some(_) => {
            let (status, detail) = out.trim().split_once('\t').unwrap_or(("error", "no output"));
            Outcome { status: status.into(), secs, detail: detail.into() }
        }
    }
}

/// Child mode. Prints `status<TAB>detail`.
fn run_one(args: &Args) {
    let mut lines = std::io::stdin().lock().lines();
    let input = lines.next().unwrap().unwrap();
    let truth = lines.next().unwrap().unwrap();
    let ty = NumType::from_name(&args.num_type).expect("bad numeric type");
    let in_egg = infix_to_egglog(&input, true);
    let gt_egg = infix_to_egglog(&truth, true);
    if in_egg.is_empty() || gt_egg.is_empty() {
        println!("error\tparse failed");
        return;
    }
    let cli = Cli {
        num_type: args.num_type.clone(),
        iter_limit: args.iter_limit,
        max_restarts: args.max_restarts,
        trace: args.trace,
        passes: eggy1::sched::Passes::parse(&format!("time_limit={} {}", (args.time_limit.max(0.0) * args.timeout * 1000.0) as u64, args.passes)).expect("bad --passes"),
        expr: input.clone(),
        ..Default::default()
    };
    let stats_path = std::env::var("EGGY_STATS").ok();
    if stats_path.is_some() {
        eggy1::stats::enable();
    }
    let out = match simplify(&in_egg, &cli) {
        Ok(o) => o,
        Err(e) => {
            println!("error\t{}", e.to_string().replace(['\n', '\t'], " "));
            return;
        }
    };
    let (t_in, t_gt, t_out) = (eval::parse(&in_egg), eval::parse(&gt_egg), eval::parse(&infix_to_egglog(&out, true)));
    let (s_in, s_gt, s_out) = (eval::size(&t_in), eval::size(&t_gt), eval::size(&t_out));
    let mut table = NodeTable::new();
    let (n_in, n_gt, n_out) = (table.intern(&t_in), table.intern(&t_gt), table.intern(&t_out));
    let status = if !same_value(&table, (&t_in, n_in), (&t_out, n_out), ty) {
        "wrong"
    } else if !same_value(&table, (&t_in, n_in), (&t_gt, n_gt), ty) {
        "badgt"
    } else if s_out <= s_gt {
        "solved"
    } else if eggy1::last_run_cut() {
        "cut"
    } else if s_out < s_in {
        "partial"
    } else {
        "unchanged"
    };
    println!("{status}\tsize in/gt/out {s_in}/{s_gt}/{s_out}: {out}");
    if let Some(path) = stats_path {
        write_stats(&path, status, (s_in, s_gt, s_out), &eggy1::stats::features(&t_in));
    }
}

/// Appends the case's per-pass counts to `path` as
/// `type file section index status in gt out features key=count:secs;...`.
fn write_stats(path: &str, status: &str, (s_in, s_gt, s_out): (usize, usize, usize), features: &str) {
    let counts = eggy1::stats::take();
    let Ok(case) = std::env::var("EGGY_CASE") else { return };
    let cells: Vec<String> = counts.iter().map(|(k, (n, secs))| format!("{k}={n}:{secs:.4}")).collect();
    let line = format!("{case}\t{status}\t{s_in}\t{s_gt}\t{s_out}\t{features}\t{}\n", cells.join(";"));
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = f.write_all(line.as_bytes());
    }
}

/// Compare on random and boundary inputs; inputs that divide by zero are skipped.
fn same_value(table: &NodeTable, (a, na): (&Term, NodeId), (b, nb): (&Term, NodeId), ty: NumType) -> bool {
    let mut names = eval::vars(a);
    for v in eval::vars(b) {
        if !names.contains(&v) {
            names.push(v);
        }
    }
    let mut seed = 0x9e3779b97f4a7c15u64;
    let mut rng = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let special = [0u64, 1, 2, u64::MAX, 1 << (ty.bits - 1), (1 << (ty.bits - 1)) - 1];
    (0..256).all(|k| {
        let vals: Vec<u64> = names
            .iter()
            .map(|_| if k < 64 { special[(rng() % special.len() as u64) as usize] } else { rng() })
            .map(|v| v & ty.mask())
            .collect();
        // The table also holds the third term, whose other variables do not matter here.
        let env = |v: &str| names.iter().position(|n| n == v).map_or(0, |i| vals[i]);
        let vals = table.eval_all(ty, &env);
        match (vals[na as usize], vals[nb as usize]) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        }
    })
}
