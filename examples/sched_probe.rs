//! Runs the pre-pass with the prototype scheduler on dataset cases and reports, per case,
//! the legacy rebuild size and the scheduled one. Each case runs in a child process.
//!
//! cargo run --release --example sched_probe -- -n u32 -l 20 bench-data/a.txt > probe.tsv

use clap::Parser;
use eggy1::expr_convert::infix_to_egglog;
use std::io::{BufRead, Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Parser, Clone)]
struct Args {
    #[arg(short, long, default_value = "i64")]
    num_type: String,
    /// Cases per section.
    #[arg(short, long)]
    limit: Option<usize>,
    #[arg(short, long, default_value_t = 20.0)]
    timeout: f64,
    #[arg(short, long)]
    jobs: Option<usize>,
    #[arg(long, hide = true)]
    one: bool,
    files: Vec<String>,
}

struct Case {
    name: String,
    input: String,
}

fn bits(ty: &str) -> u32 {
    ty[1..].parse().expect("numeric type")
}

fn load(args: &Args) -> Vec<Case> {
    let mut out = Vec::new();
    for file in &args.files {
        let text = std::fs::read_to_string(file).unwrap_or_else(|e| panic!("{file}: {e}"));
        let stem = std::path::Path::new(file).file_stem().unwrap().to_string_lossy().to_string();
        let mut sections: Vec<Vec<Case>> = Vec::new();
        let mut header = String::new();
        let mut in_data = false;
        for line in text.lines().map(str::trim).filter(|l| !l.is_empty()) {
            if let Some(c) = line.strip_prefix('#') {
                header = c.split(',').next().unwrap_or("").trim().to_string();
                in_data = false;
                continue;
            }
            if !in_data {
                sections.push(Vec::new());
                in_data = true;
            }
            let mut depth = 0i32;
            let input = line
                .split(|ch| {
                    depth += (ch == '(') as i32 - (ch == ')') as i32;
                    ch == ',' && depth == 0
                })
                .next()
                .unwrap();
            let sec = sections.last_mut().unwrap();
            let name = format!("{stem}:{header}:{}", sec.len());
            sec.push(Case { name, input: input.trim().to_string() });
        }
        for sec in sections {
            let n = sec.len();
            let keep = args.limit.unwrap_or(n).min(n);
            let picks: Vec<usize> = (0..keep).map(|k| k * n / keep).collect();
            out.extend(sec.into_iter().enumerate().filter(|(i, _)| picks.contains(i)).map(|(_, c)| c));
        }
    }
    out
}

fn main() {
    let args = Args::parse();
    if args.one {
        let input = std::io::stdin().lock().lines().next().unwrap().unwrap();
        let egg = infix_to_egglog(&input, true);
        let opts = eggy1::sched::Options { on: true, ..Default::default() };
        let start = Instant::now();
        let _ = eggy1::linear_mba::simplify_linear_with(&egg, bits(&args.num_type), &opts);
        let total = start.elapsed().as_secs_f64();
        match eggy1::sched::take_stats() {
            Some(s) => {
                let passes: Vec<String> = s.passes.iter().map(|(n, r, c, t)| format!("{n}:{r}:{c}:{t:.3}")).collect();
                println!(
                    "{}\t{}\t{}\t{:.3}\t{:.3}\t{}\t{}\t{}",
                    s.legacy,
                    s.best,
                    s.from,
                    s.secs,
                    total,
                    s.nodes,
                    s.instances,
                    passes.join(",")
                )
            }
            None => println!("-\t-\tskipped\t0\t{total:.3}\t0\t0\t"),
        }
        return;
    }
    let cases = Arc::new(load(&args));
    let jobs = args.jobs.unwrap_or(4);
    let next = Arc::new(AtomicUsize::new(0));
    let results = Arc::new(Mutex::new(vec![String::new(); cases.len()]));
    let workers: Vec<_> = (0..jobs)
        .map(|_| {
            let (cases, next, results, args) = (cases.clone(), next.clone(), results.clone(), args.clone());
            std::thread::spawn(move || {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    let Some(case) = cases.get(i) else { break };
                    let line = run_child(&args, &case.input);
                    results.lock().unwrap()[i] = format!("{}\t{}", case.name, line);
                }
            })
        })
        .collect();
    workers.into_iter().for_each(|w| w.join().unwrap());
    println!("case\tlegacy\tbest\tfrom\tsched_secs\ttotal_secs\tnodes\tinstances\tpasses");
    for l in results.lock().unwrap().iter() {
        println!("{l}");
    }
}

fn run_child(args: &Args, input: &str) -> String {
    let start = Instant::now();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--one", "-n", &args.num_type])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn child");
    writeln!(child.stdin.take().unwrap(), "{input}").unwrap();
    let mut out = child.stdout.take().unwrap();
    let reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = out.read_to_string(&mut s);
        s
    });
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
    let out = reader.join().unwrap();
    match status {
        None => "-\t-\ttimeout\t0\t0\t0\t0".into(),
        Some(s) if !s.success() => "-\t-\terror\t0\t0\t0\t0".into(),
        Some(_) => out.trim().to_string(),
    }
}
