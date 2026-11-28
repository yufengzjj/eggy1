//! Language tests: each `tests/lang/*.pipe` holds programs, separated by `# ---` lines, each run
//! by `eggy1::lang::run` in a child process of this test so that what `print` writes to stderr is
//! captured. What a program gives is compared with the `# expect ...` lines that end it;
//! `UPDATE_GOLDEN=1 cargo test --test lang_files` rewrites them.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::Mutex;

use eggy1::lang::{self, Value};

const EXPECT: &str = "# expect ";
const SEPARATOR: &str = "# ---";

/// The programs of a file, split at its `# ---` lines.
fn sections(text: &str) -> Vec<String> {
    let mut out = vec![String::new()];
    for l in text.lines() {
        match l.trim_end() == SEPARATOR {
            true => out.push(String::new()),
            false => {
                let last = out.last_mut().unwrap();
                last.push_str(l);
                last.push('\n');
            }
        }
    }
    out
}

/// Runs program `section` of the file `path`, without its `# expect` lines, and writes its
/// warnings, value and error to stdout, one per line, tagged `warning: `, `value: ` and `error: `.
fn run_child(path: &Path, section: usize) {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display())).replace("\r\n", "\n");
    let parts = sections(&text);
    let (source, _) = split_block(&parts[section]);
    let tagged = |tag: &str, text: &str| text.lines().for_each(|l| println!("{tag}: {l}"));
    match lang::run(source, &[]) {
        Ok(out) => {
            out.warnings.iter().for_each(|w| tagged("warning", w));
            match out.value {
                None => {}
                Some(Value::Num(u64::MAX)) => tagged("value", "none"),
                Some(Value::Num(n)) => tagged("value", &n.to_string()),
                Some(Value::Text(t)) => tagged("value", &t),
                Some(Value::Group(g)) => tagged("value", &format!("group [{}]", g.iter().map(|c| c.term()).collect::<Vec<_>>().join(", "))),
                Some(Value::Fn(_)) => tagged("value", "function"),
            }
        }
        Err(e) => tagged("error", &e),
    }
}

/// The expectation block of program `section` of the file `path`, from a run of it in a child
/// process.
fn expectations(path: &Path, section: usize) -> String {
    let out = Command::new(std::env::current_exe().unwrap())
        .arg("--run-file")
        .arg(path)
        .arg(section.to_string())
        .current_dir(path.parent().unwrap())
        .output()
        .unwrap_or_else(|e| panic!("cannot run the child: {e}"));
    let (stdout, stderr) = (String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n"), String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n"));
    let mut block = String::new();
    if !out.status.success() {
        block += &format!("{EXPECT}crash: exit {}\n", out.status.code().map_or("killed".into(), |c| c.to_string()));
    }
    for l in stderr.lines() {
        block += &format!("{EXPECT}stderr: {l}\n");
    }
    for l in stdout.lines() {
        block += &format!("{EXPECT}{l}\n");
    }
    block
}

/// The program `text` split into its source and its ending block of `# expect ` lines.
fn split_block(text: &str) -> (&str, String) {
    let lines: Vec<&str> = text.lines().collect();
    let mut start = lines.len();
    while start > 0 && (lines[start - 1].starts_with(EXPECT) || lines[start - 1].trim().is_empty()) {
        start -= 1;
    }
    let body_end: usize = lines[..start].iter().map(|l| l.len() + 1).sum::<usize>().min(text.len());
    let block: String = lines[start..].iter().filter(|l| l.starts_with(EXPECT)).map(|l| format!("{l}\n")).collect();
    (text[..body_end].trim_end(), block)
}

fn threads(args: &[String]) -> usize {
    let from_args = args.iter().enumerate().find_map(|(i, a)| match a.strip_prefix("--test-threads") {
        Some(rest) if rest.starts_with('=') => rest[1..].parse().ok(),
        Some("") => args.get(i + 1).and_then(|n| n.parse().ok()),
        _ => None,
    });
    from_args.or_else(|| std::env::var("RUST_TEST_THREADS").ok().and_then(|n| n.parse().ok())).unwrap_or(8usize).max(1)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Some(i) = args.iter().position(|a| a == "--run-file") {
        run_child(Path::new(&args[i + 1]), args[i + 2].parse().unwrap());
        return ExitCode::SUCCESS;
    }
    let filters: Vec<&String> = args.iter().enumerate().filter(|(i, a)| !a.starts_with('-') && !(*i > 0 && args[i - 1] == "--test-threads")).map(|(_, a)| a).collect();
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/lang");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("tests/lang")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "pipe"))
        .filter(|p| filters.is_empty() || filters.iter().any(|f| p.file_name().unwrap().to_string_lossy().contains(f.as_str())))
        .collect();
    files.sort();
    let texts: Vec<String> = files.iter().map(|p| std::fs::read_to_string(p).unwrap().replace("\r\n", "\n")).collect();
    let jobs: Vec<(usize, usize)> = texts.iter().enumerate().flat_map(|(f, t)| (0..sections(t).len()).map(move |s| (f, s))).collect();
    let update = std::env::var("UPDATE_GOLDEN").is_ok_and(|v| !v.is_empty() && v != "0");
    println!("\nrunning {} programs in {} language files", jobs.len(), files.len());
    let next = Mutex::new(0usize);
    let results: Mutex<Vec<Option<String>>> = Mutex::new(vec![None; jobs.len()]);
    std::thread::scope(|s| {
        for _ in 0..threads(&args).min(jobs.len().max(1)) {
            s.spawn(|| {
                loop {
                    let i = {
                        let mut n = next.lock().unwrap();
                        *n += 1;
                        *n - 1
                    };
                    let Some(&(f, section)) = jobs.get(i) else { break };
                    let got = expectations(&files[f], section);
                    results.lock().unwrap()[i] = Some(got);
                }
            });
        }
    });
    let mut results = results.into_inner().unwrap().into_iter();
    let (mut failed, mut count) = (Vec::new(), 0);
    for (path, text) in files.iter().zip(&texts) {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let parts = sections(text);
        let mut new = Vec::new();
        for (i, part) in parts.iter().enumerate() {
            count += 1;
            let got = results.next().unwrap().unwrap();
            let (body, want) = split_block(part);
            let name = match parts.len() {
                1 => name.clone(),
                _ => format!("{name} [{}]", i + 1),
            };
            if update {
                new.push(if got.is_empty() { body.to_string() } else { format!("{body}\n\n{}", got.trim_end()) });
            } else if want == got {
                println!("test {name} ... ok");
            } else {
                println!("test {name} ... FAILED");
                failed.push(format!("{name}:\n  want:\n{}  got:\n{}", indent(&want), indent(&got)));
            }
        }
        if update {
            let new = format!("{}\n", new.join(&format!("\n\n{SEPARATOR}\n")));
            if &new != text {
                std::fs::write(path, new).unwrap();
            }
            println!("test {name} ... updated");
        }
    }
    if failed.is_empty() {
        println!("\ntest result: ok. {count} passed");
        ExitCode::SUCCESS
    } else {
        println!("\nfailures (UPDATE_GOLDEN=1 cargo test --test lang_files rewrites the # expect lines):\n");
        failed.iter().for_each(|f| println!("{f}"));
        println!("test result: FAILED. {} passed; {} failed", count - failed.len(), failed.len());
        ExitCode::FAILURE
    }
}

fn indent(block: &str) -> String {
    match block.is_empty() {
        true => "    (nothing)\n".into(),
        false => block.lines().map(|l| format!("    {l}\n")).collect(),
    }
}
