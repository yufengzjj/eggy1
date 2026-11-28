//! Running a program: its source text read into `Passes` (`source::Program`), checked, and
//! its top-level steps run once, in order, as one sequence that starts with no input.

use super::ast::{Holds, Pipe, Slot};
use super::eval::{Env, Lex, StepKind, Value, clear_failed, failed, go, scoped, step_kind, step_on};
use super::host::{self, NUM_TYPE, Passes, TRACE};
use super::elab::parse_assign;
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
    Tuple,
}

/// A step of a program's top level.
#[derive(Clone, Debug, PartialEq)]
pub struct Top {
    pub pipe: Pipe,
    pub gives: Gives,
}

impl Top {
    /// A step of a pipeline: an assignment or a switch gives nothing, an expression a number or
    /// a text, any other step candidates.
    pub(crate) fn step(pipe: Pipe) -> Top {
        let gives = match &pipe {
            Pipe::Bind(..) | Pipe::Unpack(..) => Gives::Nothing,
            Pipe::Expanded(m) if m.switch_names().is_some() => Gives::Nothing,
            Pipe::Text(_) => Gives::Text,
            Pipe::App(super::ast::Fun::Builtin(b), _) if b.sig.is_text() => Gives::Text,
            p if super::ast::gives_tuple(p) => Gives::Tuple,
            p @ Pipe::Index(..) => match super::ast::value_ty(p) {
                Some(super::types::Ty::Num) => Gives::Num,
                Some(super::types::Ty::Text) => Gives::Text,
                _ => Gives::Group,
            },
            p if step_kind(p) == StepKind::Value => Gives::Num,
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
        // The value the last step gave or passed on: none until a step gives one.
        let (mut last, mut value) = (Gives::Nothing, None);
        for t in &p.program {
            if settings() != at {
                let moved = env.moved.get();
                env = top_env(p, &lex);
                env.moved.set(moved);
                at = settings();
            }
            match t.gives {
                Gives::Fn => {
                    let Pipe::Var(Slot::Local(n, Holds::Fn(_))) = &t.pipe else { unreachable!("a function value is a function variable") };
                    value = lex.regs.borrow().get(n).cloned();
                }
                _ => {
                    let had = value.is_some();
                    let v = step_on(&t.pipe, value.take().unwrap_or(Value::Group(Vec::new())), &env).map_err(|e| e.to_string())?;
                    value = (had || step_kind(&t.pipe) != StepKind::Nothing).then_some(v);
                }
            }
            if let Some(e) = failed() {
                return Err(e.to_string());
            }
            last = t.gives;
        }
        let value = if last == Gives::Nothing { None } else { value };
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

    #[test]
    fn caller_globals_come_first() {
        let r = execute_then(&passes("(import \"default\")\ntrace = 0\nnum_type = u16"), &[("num_type", "u8"), ("restarts", "5")], || (host::num_type(), get(crate::rust_vars::RESTARTS))).unwrap().1;
        assert_eq!(r, ("u16", 5), "the caller's globals come first, a definition as none keeps them");
    }

    #[test]
    fn a_call_before_its_definition_needs_its_arguments() {
        let e = value("(def (f n) (fix n (f n)))").err().unwrap();
        assert!(e.contains("f is called before its definition"), "{e}");
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
        let c = dir.join("sub/c.pipe").display().to_string().replace('\\', "/");
        let e = value(&format!("(import \"{c}\")")).err().unwrap();
        assert!(e.contains("import cycle: ") && e.contains("c.pipe -> ") && e.contains("d.pipe -> "), "{e}");
        std::fs::remove_dir_all(&dir).unwrap();
        let twice = passes("(import \"default\")\n(import \"default\")");
        assert_eq!(twice, host::DEFAULT.0, "the default library is read once");
    }
}
