//! Running a program: its source text read into `Passes` (`source::Program`), checked, and
//! its top-level steps run once, in order, as one sequence that starts from no candidates.

use super::ast::{Holds, Pipe, Slot};
use super::eval::{Env, Lex, Value, clear_failed, failed, go, scoped};
use super::host::{self, NUM_TYPE, Passes, TRACE};
use super::parser::parse_assign;
use super::source::Program;
use super::vars::{NONE, get, parsing};

/// What a top-level step gives: nothing (an assignment), the candidates the next step takes,
/// or a value that leaves them as they are.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Gives {
    Nothing,
    Group,
    Num,
    Text,
    Fn,
}

/// A step of a program's top level.
#[derive(Clone, Debug, PartialEq)]
pub struct Top {
    pub pipe: Pipe,
    pub gives: Gives,
}

impl Top {
    /// A step of a pipeline: a binding gives nothing, any other step candidates.
    pub(crate) fn step(pipe: Pipe) -> Top {
        let gives = match &pipe {
            Pipe::Bind(..) => Gives::Nothing,
            Pipe::Expanded(m) if m.switch_names().is_some() => Gives::Nothing,
            _ => Gives::Group,
        };
        Top { pipe, gives }
    }
}

/// What a program gave: the value of its last top-level statement (none when that is a
/// definition or an assignment), and the warnings of reading it.
pub struct Outcome {
    pub value: Option<Value>,
    pub warnings: Vec<String>,
}

/// Reads, checks and runs the program `source`; `globals` are `NAME = VALUE` assignments
/// made before its first step, so a program that defines them as `none` keeps them.
pub fn run(source: &str, globals: &[(&str, &str)]) -> Result<Outcome, String> {
    let mut prog = Program::new();
    prog.read(source)?;
    let (passes, warnings) = prog.finish()?;
    let value = execute(&passes, globals)?;
    Ok(Outcome { value, warnings })
}

/// Runs the program `p` read before (`run`).
pub fn execute(p: &Passes, globals: &[(&str, &str)]) -> Result<Option<Value>, String> {
    execute_then(p, globals, || ()).map(|(v, ())| v)
}

/// `execute`, then `f` in the program's outermost scope, where its global variables still
/// have the values it gave them.
pub fn execute_then<R>(p: &Passes, globals: &[(&str, &str)], f: impl FnOnce() -> R) -> Result<(Option<Value>, R), String> {
    host::start();
    host::set_current(p);
    clear_failed();
    scoped(|| {
        let lex = Lex::new("", None);
        let mut set = Vec::new();
        for (name, val) in globals {
            let step = parsing(&mut p.globals.clone(), || parse_assign(name, val))?;
            set = go(&step, set, &top_env(p, &lex)).map_err(|e| e.to_string())?;
        }
        let (mut env, mut at) = (top_env(p, &lex), settings());
        let (mut last, mut value) = (Gives::Nothing, None);
        for t in &p.program {
            if settings() != at {
                let moved = env.moved.get();
                env = top_env(p, &lex);
                env.moved.set(moved);
                at = settings();
            }
            match t.gives {
                Gives::Nothing | Gives::Group => set = go(&t.pipe, set, &env).map_err(|e| e.to_string())?,
                Gives::Num => value = Some(Value::Num(env.value(&t.pipe, &set))),
                Gives::Text => value = Some(Value::Text(env.text_of(&t.pipe, &set).map_err(|e| e.to_string())?)),
                Gives::Fn => {
                    let Pipe::Var(Slot::Local(n, Holds::Fn(_))) = &t.pipe else { unreachable!("a function value is a function variable") };
                    value = lex.regs.borrow().get(n).cloned();
                }
            }
            if let Some(e) = failed() {
                return Err(e.to_string());
            }
            last = t.gives;
        }
        let value = match last {
            Gives::Nothing => None,
            Gives::Group => Some(Value::Group(set)),
            _ => value,
        };
        Ok((value, f()))
    })
}

/// `f` after the program `p`, in its outermost scope (`execute_then`).
#[cfg(test)]
pub(crate) fn within<R>(p: &Passes, f: impl FnOnce() -> R) -> R {
    execute_then(p, &[], f).unwrap_or_else(|e| panic!("{e}")).1
}

/// `p.prepass()` on `input` at width `w` (`signed` as in `linear_mba::Ctx`), after the program `p`.
#[cfg(test)]
pub(crate) fn prepass_of(p: &Passes, input: host::Cand, w: u32, signed: Option<bool>) -> Result<Vec<host::Cand>, host::Error> {
    within(p, || super::eval::run(&p.prepass(), vec![input.clone()], &Env::with(p, w, signed, false, input.term())))
}

/// The value the program `source` gives.
#[cfg(test)]
pub(crate) fn value(source: &str) -> Result<Option<Value>, String> {
    run(source, &[]).map(|o| o.value)
}

/// The variables the run of a top-level step is made from.
fn settings() -> (u64, u64) {
    (get(NUM_TYPE), get(TRACE))
}

/// The run of the top-level steps: the numeric type and `trace` as the variables have them,
/// the program's group variables.
fn top_env<'a>(p: &'a Passes, lex: &std::rc::Rc<Lex>) -> Env<'a> {
    let ty = host::num_type();
    let signed = host::NumType::from_name(ty).map(|t| t.signed);
    let trace = !matches!(get(TRACE), 0 | NONE);
    let env = Env::with(p, host::width_of(ty), signed, trace, "");
    env.lex.replace(lex.clone());
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    fn passes(source: &str) -> Passes {
        let mut p = Program::new();
        p.read(source).unwrap();
        p.finish().unwrap().0
    }

    fn text(source: &str) -> String {
        match value(source) {
            Ok(Some(Value::Text(t))) => t,
            r => panic!("{source}: {}", r.err().unwrap_or_else(|| "no text".into())),
        }
    }

    #[test]
    fn a_program_runs_once_top_to_bottom() {
        assert!(matches!(value("1 + 2"), Ok(Some(Value::Num(3)))));
        assert!(matches!(value("x_global = 4\nx_global * 2"), Ok(Some(Value::Num(8)))), "a new name assigned a number is a global");
        assert_eq!(text("\"a b\""), "a b");
        assert!(matches!(value("(print \"hello world\")"), Ok(Some(Value::Group(g))) if g.is_empty()), "the candidates start empty");
        assert!(matches!(value("(def (f) id)"), Ok(None)) && matches!(value("keep = 3"), Ok(None)), "a definition or an assignment gives no value");
        assert!(matches!(value("(import \"default\")\nf:term->num = size\nf"), Ok(Some(Value::Fn(_)))));
        let lib = "(import \"default\")\n";
        assert_eq!(text(&format!("{lib}(parse \"x + 0xff\") | show")), "(x + 0xff)", "i64 when num_type is none");
        assert_eq!(text(&format!("{lib}num_type = i8\n(parse \"x + 0xff\") | show")), "(x - 1)");
        assert_eq!(text(&format!("{lib}num_type = u8\nt = (parse \"(Add (Var \\\"x\\\") (Num -1))\")\n(show (main t))")), "(x + 0xff)", "an egglog term, and a group variable of the top level");
        assert_eq!(text(&format!("{lib}num_type = u32\n(parse \"(x & y) + (x | y)\")\nsimplify\nshow")), "(x + y)", "the steps of the top level are one sequence");
        let r = execute_then(&passes(&format!("{lib}trace = 0\nnum_type = u16")), &[("num_type", "u8"), ("restarts", "5")], || (host::num_type(), get(crate::rust_vars::RESTARTS))).unwrap().1;
        assert_eq!(r, ("u16", 5), "the caller's globals come first, a definition as none keeps them");
        for (bad, msg) in [
            ("lowbits", "lowbits has no candidates to work on at the top level"),
            ("(import \"default\")\nsimplify", "simplify has no candidates"),
            ("(import \"default\")\nt = (parse \"x\")\nsimplify", "simplify has no candidates"),
            ("t = (lowbits | unshift)", "has no candidates"),
            ("show", "show has no candidate"),
            ("(load t)", "the program reads group variable t before it is bound"),
            ("num_type = u7", "num_type takes a numeric type"),
            ("(import \"default\")\n(parse \"x\") | show | rewrite", "show gives a text"),
            ("(import \"default\")\n(parse \"x\") | (fix 2 show)", "show gives a text, not candidates"),
        ] {
            let e = value(bad).err().unwrap_or_else(|| panic!("{bad} runs"));
            assert!(e.contains(msg), "{bad}: {e}");
        }
    }

    #[test]
    fn recursion_and_late_binding() {
        let run = |lines: &[&str]| text(&format!("(import \"default\")\n{}", lines.join("\n")));
        let parity = ["(def (even n:num) (if (n > 0) (odd (n - 1)) (parse \"e\")))", "(def (odd n:num) (if (n > 0) (even (n - 1)) (parse \"o\")))"];
        assert_eq!(run(&[&parity[..], &["(parse \"x\") | (even 3) | show"]].concat()), "o", "a call before the definition, and recursion through another function");
        assert_eq!(run(&[&parity[..], &["(parse \"x\") | (even 400) | show"]].concat()), "e");
        let late = ["(def (g) (h 1) | (filter (big 0)))", "(def (h n) (fix n id))", "(def (big k) size > k)", "(parse \"x + y\") | g | show"];
        assert_eq!(run(&late), "(x + y)", "the signature of a function defined later comes from its definition");
        let again = ["(def (f n:num) (fix n (parse \"a\")))", "(def (g) (f 1))", "(def (f k:num) (fix k (parse \"b\")))", "(parse \"x\") | g | show"];
        assert_eq!(run(&again), "b", "a call runs the last definition, also one read before it");
        let after = ["(def (f) (fix 1 (parse \"a\")))", "(def (g) f)", "(parse \"x\") | g | show", "(def (f) (fix 1 (parse \"b\")))"];
        assert_eq!(run(&after), "b", "the program runs after it is read whole");
        let named = ["(def (f s:name) (off s) | (parse \"a\"))", "(def (g) (f relate))", "(def (f t:name) (on t) | (parse \"b\"))", "(parse \"x\") | g | show"];
        assert_eq!(run(&named), "b", "with its name arguments in place");
        let e = value("(def (f) (f 1))").err().unwrap();
        assert!(e.contains("f takes no arguments"), "{e}");
        let e = value("(def (f n) (fix n (f n)))").err().unwrap();
        assert!(e.contains("f is called before its definition"), "{e}");
        let deep = format!("recursion deeper than {} calls in f", super::super::eval::MAX_DEPTH);
        for bad in [
            ["(def (f) f)", "(parse \"x\") | f"],
            ["(def (app p) p)\n(def (f) (app f))", "(parse \"x\") | f"],
            ["(def (f) (memo loop f))", "(parse \"x + y\") | f"],
            ["(def (f) (regions f f))", "(parse \"x + y\") | f"],
            ["(def (f n:num) (f (n + 1)) | id)", "(parse \"x\") | (f 0)"],
        ] {
            let e = value(&format!("(import \"default\")\n{}", bad.join("\n"))).err().unwrap_or_else(|| panic!("{bad:?} runs"));
            assert!(e.contains(&deep), "{bad:?}: {e}");
        }
    }

    #[test]
    fn imports() {
        let dir = std::env::temp_dir().join(format!("eggy1-imports-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("sub")).unwrap();
        std::fs::write(dir.join("a.pipe"), "(import \"sub/b.pipe\")\nimported_a = imported_b + 1\n").unwrap();
        std::fs::write(dir.join("sub/b.pipe"), "imported_b = 1\n").unwrap();
        std::fs::write(dir.join("sub/c.pipe"), "(import \"d.pipe\")\n").unwrap();
        std::fs::write(dir.join("sub/d.pipe"), "(import \"c.pipe\")\n").unwrap();
        let a = dir.join("a.pipe").display().to_string().replace('\\', "/");
        let p = passes(&format!("(import \"{a}\")\n(import \"{a}\")"));
        assert_eq!(p.program.len(), 2, "a file is imported once per program, its imports relative to it");
        assert!(matches!(value(&format!("(import \"{a}\")\nimported_a")), Ok(Some(Value::Num(2)))));
        let c = dir.join("sub/c.pipe").display().to_string().replace('\\', "/");
        let e = value(&format!("(import \"{c}\")")).err().unwrap();
        assert!(e.contains("import cycle: ") && e.contains("c.pipe -> ") && e.contains("d.pipe -> "), "{e}");
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(value("(import \"nowhere.pipe\")").err().unwrap().contains("no file nowhere.pipe and no source named nowhere.pipe"));
        assert!(value("(import \"default\")\n(def (f) (import \"default\"))").err().unwrap().contains("top-level item"));
        let twice = passes("(import \"default\")\n(import \"default\")");
        assert_eq!(twice, host::DEFAULT.0, "the default library is read once");
    }
}
