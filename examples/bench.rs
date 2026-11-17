//! Benchmark on MBA datasets: simplify each case and compare it with the ground truth.
//!
//! Dataset lines are `obfuscated, groundtruth[, ...]`. Lines starting with `#` are
//! comments; the last comment before a run of data lines names that section.
//! Each case runs in a child process (this binary with `--one`) so it can be killed
//! on timeout and a panic only fails that case.

use clap::Parser;
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
    /// Parallel cases (default: number of CPUs).
    #[arg(short, long)]
    jobs: Option<usize>,
    /// At most this many cases per section, evenly spaced.
    #[arg(short, long)]
    limit: Option<usize>,
    /// Write every case that is not `solved` to this file.
    #[arg(short, long)]
    fails: Option<String>,
    /// Child mode: read input and ground truth from stdin, print one result line.
    #[arg(long, hide = true)]
    one: bool,
}

const STATUSES: [&str; 8] = ["solved", "partial", "unchanged", "timeout", "error", "wrong", "badgt", "total"];

struct Case {
    file: String,
    section: String,
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
            sections.last_mut().unwrap().1.push(Case {
                file: name.clone(),
                section,
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
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--one", "-n", &args.num_type, "-i", &args.iter_limit.to_string(), "-m", &args.max_restarts.to_string()])
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
        rule_compile: false,
        expr_compile: false,
        num_type: args.num_type.clone(),
        iter_limit: args.iter_limit,
        max_restarts: args.max_restarts,
        expr: input.clone(),
    };
    let out = match simplify(&in_egg, &cli) {
        Ok(o) => o,
        Err(e) => {
            println!("error\t{}", e.to_string().replace(['\n', '\t'], " "));
            return;
        }
    };
    let (t_in, t_gt, t_out) = (eval::parse(&in_egg), eval::parse(&gt_egg), eval::parse(&infix_to_egglog(&out, true)));
    let (s_in, s_gt, s_out) = (eval::size(&t_in), eval::size(&t_gt), eval::size(&t_out));
    let status = if !same_value(&t_in, &t_out, ty) {
        "wrong"
    } else if !same_value(&t_in, &t_gt, ty) {
        "badgt"
    } else if s_out <= s_gt {
        "solved"
    } else if s_out < s_in {
        "partial"
    } else {
        "unchanged"
    };
    println!("{status}\tsize in/gt/out {s_in}/{s_gt}/{s_out}: {out}");
}

/// Compare on random and boundary inputs; inputs that divide by zero are skipped.
fn same_value(a: &Term, b: &Term, ty: NumType) -> bool {
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
        let env = |v: &str| vals[names.iter().position(|n| n == v).unwrap()];
        match (eval::eval(a, ty, &env), eval::eval(b, ty, &env)) {
            (Some(x), Some(y)) => x == y,
            _ => true,
        }
    })
}
