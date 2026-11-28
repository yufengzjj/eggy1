//! Command-line snapshot tests: each line of `tests/golden/cases.txt` is a command line of the
//! eggy1 binary whose exit status, stdout and stderr are compared with `tests/golden/out/`.
//! `UPDATE_GOLDEN=1 cargo test --test golden` rewrites the snapshots.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

#[derive(Clone, Copy, PartialEq)]
enum Group {
    Full,
    Status,
}

struct Case {
    line: usize,
    text: String,
    args: Vec<String>,
    group: Group,
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The words of a command line: spaces separate them, `"..."` and `'...'` quote, and `\"` and
/// `\\` are escapes inside double quotes.
fn split_args(line: &str) -> Result<Vec<String>, String> {
    let (mut out, mut word, mut in_word) = (Vec::new(), String::new(), false);
    let mut chars = line.chars();
    while let Some(c) = chars.next() {
        match c {
            ' ' | '\t' => {
                if in_word {
                    out.push(std::mem::take(&mut word));
                    in_word = false;
                }
            }
            '"' => {
                in_word = true;
                loop {
                    match chars.next() {
                        Some('"') => break,
                        Some('\\') => match chars.next() {
                            Some(e @ ('"' | '\\')) => word.push(e),
                            Some(e) => {
                                word.push('\\');
                                word.push(e);
                            }
                            None => return Err("line ends after \\".into()),
                        },
                        Some(e) => word.push(e),
                        None => return Err("unclosed \"".into()),
                    }
                }
            }
            '\'' => {
                in_word = true;
                loop {
                    match chars.next() {
                        Some('\'') => break,
                        Some(e) => word.push(e),
                        None => return Err("unclosed '".into()),
                    }
                }
            }
            c => {
                in_word = true;
                word.push(c);
            }
        }
    }
    if in_word {
        out.push(word);
    }
    Ok(out)
}

/// The cases of `cases.txt`; `[full]` and `[status]` lines start a group, `[full]` first.
fn read_cases(text: &str) -> Vec<Case> {
    let mut group = Group::Full;
    let mut cases = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        match line {
            "" => continue,
            "[full]" => group = Group::Full,
            "[status]" => group = Group::Status,
            l if l.starts_with('#') => continue,
            l => {
                let args = split_args(l).unwrap_or_else(|e| panic!("cases.txt line {}: {e}", i + 1));
                cases.push(Case { line: i + 1, text: l.to_string(), args, group });
            }
        }
    }
    cases
}

fn slug(case: &Case, index: usize) -> String {
    let mut s = String::new();
    for c in case.text.chars() {
        if c.is_ascii_alphanumeric() {
            s.push(c.to_ascii_lowercase());
        } else if !s.ends_with('-') && !s.is_empty() {
            s.push('-');
        }
        if s.len() >= 40 {
            break;
        }
    }
    format!("{:03}-{}", index + 1, s.trim_end_matches('-'))
}

/// `text` with every time in seconds or milliseconds (`0.0170s`, `12ms`, `3.5 ms`) written `<t>`.
fn mask_times(text: &str) -> String {
    let b = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < b.len() {
        let starts = b[i].is_ascii_digit() && (i == 0 || !(b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_' || b[i - 1] == b'.'));
        if starts {
            let mut j = i;
            while j < b.len() && b[j].is_ascii_digit() {
                j += 1;
            }
            if j + 1 < b.len() && b[j] == b'.' && b[j + 1].is_ascii_digit() {
                j += 1;
                while j < b.len() && b[j].is_ascii_digit() {
                    j += 1;
                }
            }
            let mut k = j;
            if k < b.len() && b[k] == b' ' {
                k += 1;
            }
            let unit = if text[k..].starts_with("ms") {
                Some(k + 2)
            } else if text[k..].starts_with('s') && k == j {
                Some(k + 1)
            } else {
                None
            };
            if let Some(end) = unit.filter(|&e| e == b.len() || !(b[e].is_ascii_alphanumeric() || b[e] == b'_')) {
                out.push_str("<t>");
                out.push_str(&text[j..end]);
                i = end;
                continue;
            }
            out.push_str(&text[i..j]);
            i = j;
            continue;
        }
        let len = text[i..].chars().next().map_or(1, char::len_utf8);
        out.push_str(&text[i..i + len]);
        i += len;
    }
    out
}

/// `text` with line ends, the binary's name, times and panic headers (`thread 'main' (ID)
/// panicked at src\x.rs`) the same on every run and platform.
fn normalize(text: &[u8]) -> String {
    let s = String::from_utf8_lossy(text).replace("\r\n", "\n").replace("eggy1.exe", "eggy1");
    let lines: Vec<String> = s
        .split('\n')
        .map(|l| match (l.strip_prefix("thread '"), l.find(" panicked at ")) {
            (Some(rest), Some(at)) => {
                let name = rest.split('\'').next().unwrap_or("");
                format!("thread '{name}' panicked at {}", l[at + 13..].replace('\\', "/"))
            }
            _ => l.to_string(),
        })
        .collect();
    mask_times(&lines.join("\n"))
}

fn quote(arg: &str) -> String {
    if !arg.is_empty() && arg.chars().all(|c| c.is_ascii_alphanumeric() || "-_=./,+:".contains(c)) {
        arg.to_string()
    } else {
        format!("\"{}\"", arg.replace('\\', "\\\\").replace('"', "\\\""))
    }
}

fn snapshot(case: &Case) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_eggy1"))
        .args(&case.args)
        .current_dir(root())
        .output()
        .unwrap_or_else(|e| panic!("cannot run eggy1: {e}"));
    let command: Vec<String> = case.args.iter().map(|a| quote(a)).collect();
    let code = out.status.code().map_or("killed".to_string(), |c| c.to_string());
    let mut s = format!("==== command\neggy1 {}\n==== exit\n{code}\n", command.join(" "));
    let (stdout, stderr) = (normalize(&out.stdout), normalize(&out.stderr));
    match case.group {
        Group::Full => {
            s += &format!("==== stdout\n{stdout}");
            if !stdout.is_empty() && !stdout.ends_with('\n') {
                s.push('\n');
            }
            s += &format!("==== stderr\n{stderr}");
            if !stderr.is_empty() && !stderr.ends_with('\n') {
                s.push('\n');
            }
        }
        Group::Status => {
            let cut = stderr.contains("time limit reached") || stdout.contains("time limit reached");
            s += &format!("==== status\n{}\n", if cut { "cut" } else { "not cut" });
        }
    }
    s
}

/// The first differing lines of `want` and `got`, at most a few.
fn short_diff(want: &str, got: &str) -> String {
    let (w, g): (Vec<&str>, Vec<&str>) = (want.lines().collect(), got.lines().collect());
    let mut out = String::new();
    let mut shown = 0;
    for i in 0..w.len().max(g.len()) {
        let (a, b) = (w.get(i), g.get(i));
        if a != b {
            out += &format!("    line {}:\n      want: {}\n      got:  {}\n", i + 1, a.unwrap_or(&"<none>"), b.unwrap_or(&"<none>"));
            shown += 1;
            if shown == 4 {
                out += "    ...\n";
                break;
            }
        }
    }
    out
}

/// The thread count of `--test-threads=N` or `RUST_TEST_THREADS`, else 8.
fn threads() -> usize {
    let args: Vec<String> = std::env::args().collect();
    let from_args = args.iter().enumerate().find_map(|(i, a)| match a.strip_prefix("--test-threads") {
        Some(rest) if rest.starts_with('=') => rest[1..].parse().ok(),
        Some("") => args.get(i + 1).and_then(|n| n.parse().ok()),
        _ => None,
    });
    let n = from_args.or_else(|| std::env::var("RUST_TEST_THREADS").ok().and_then(|n| n.parse().ok())).unwrap_or(8);
    n.max(1)
}

fn run_all<T: Send>(n: usize, threads: usize, f: impl Fn(usize) -> T + Sync) -> Vec<T> {
    let next = Mutex::new(0usize);
    let results: Mutex<Vec<Option<T>>> = Mutex::new((0..n).map(|_| None).collect());
    std::thread::scope(|s| {
        for _ in 0..threads.min(n.max(1)) {
            s.spawn(|| {
                loop {
                    let i = {
                        let mut g = next.lock().unwrap();
                        let i = *g;
                        *g += 1;
                        i
                    };
                    if i >= n {
                        break;
                    }
                    let r = f(i);
                    results.lock().unwrap()[i] = Some(r);
                }
            });
        }
    });
    results.into_inner().unwrap().into_iter().map(Option::unwrap).collect()
}

#[test]
fn golden() {
    let dir = root().join("tests/golden");
    let cases = read_cases(&std::fs::read_to_string(dir.join("cases.txt")).expect("tests/golden/cases.txt"));
    let out_dir = dir.join("out");
    let update = std::env::var("UPDATE_GOLDEN").is_ok_and(|v| !v.is_empty() && v != "0");
    let names: Vec<String> = cases.iter().enumerate().map(|(i, c)| slug(c, i)).collect();
    let got = run_all(cases.len(), threads(), |i| snapshot(&cases[i]));
    if update {
        std::fs::create_dir_all(&out_dir).unwrap();
        let keep: std::collections::HashSet<String> = names.iter().map(|n| format!("{n}.txt")).collect();
        for e in std::fs::read_dir(&out_dir).unwrap().flatten() {
            let name = e.file_name().to_string_lossy().to_string();
            if name.ends_with(".txt") && !keep.contains(&name) {
                std::fs::remove_file(e.path()).unwrap();
            }
        }
        for (name, s) in names.iter().zip(&got) {
            let path = out_dir.join(format!("{name}.txt"));
            if std::fs::read_to_string(&path).ok().as_deref() != Some(s.as_str()) {
                std::fs::write(&path, s).unwrap();
            }
        }
        return;
    }
    let mut failures = String::new();
    let mut count = 0;
    for ((case, name), s) in cases.iter().zip(&names).zip(&got) {
        let path: &Path = &out_dir.join(format!("{name}.txt"));
        let want = std::fs::read_to_string(path).map(|w| w.replace("\r\n", "\n"));
        match want {
            Ok(w) if w == *s => {}
            Ok(w) => {
                count += 1;
                failures += &format!("  {name} (cases.txt line {}): {}\n{}", case.line, case.text, short_diff(&w, s));
            }
            Err(_) => {
                count += 1;
                failures += &format!("  {name} (cases.txt line {}): no snapshot {}\n", case.line, path.display());
            }
        }
    }
    assert!(count == 0, "{count} of {} golden cases differ (UPDATE_GOLDEN=1 cargo test --test golden rewrites them):\n{failures}", cases.len());
}

#[test]
fn masking() {
    assert_eq!(mask_times("  pass/x   2     0.0170s\n"), "  pass/x   2     <t>s\n");
    assert_eq!(mask_times("took 12ms, 3.5 ms; size 12 u8 x2s 1.5"), "took <t>ms, <t> ms; size 12 u8 x2s 1.5");
    assert_eq!(split_args(r#"-n u8 "a \"b\" c" 'd e'"#).unwrap(), ["-n", "u8", "a \"b\" c", "d e"]);
}
