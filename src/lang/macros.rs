//! The macros of the pipeline language, expanded when parsed: `(smallest p)`, `(on NAME ...)`
//! and `(off NAME ...)`.

use super::ast::{Expanded, Fun, Holds, Pipe, Slot};
use super::defs::Call;
use super::host::{self, INNER, switch_index};
use super::parser::Parser;
use super::types::Ty;
use std::sync::Arc;

impl Expanded {
    /// `(off NAME ...)` (`on` false) or `(on NAME ...)`: `NAME = 0 | ...` or `NAME = 1 | ...`
    /// for the `INNER` passes and `FLAGS` switches named, in the enclosing sequence. A name
    /// that is no switch (a parameter until a call puts its argument in place) expands to
    /// nothing.
    pub fn switches(on: bool, names: &[&str]) -> Pipe {
        let steps = names.iter().filter_map(|n| switch_index(n)).map(|i| Pipe::Bind(Slot::Global(i), std::sync::Arc::new(Pipe::Num(on as u64)))).collect();
        let args = names.iter().map(|n| Pipe::Name(n.to_string())).collect();
        Pipe::Expanded(Box::new(Expanded { head: if on { "on" } else { "off" }, args, steps, scoped: false, timed: false }))
    }

    /// For `on` and `off`: whether it is `on`, and the names.
    pub fn switch_names(&self) -> Option<(bool, Vec<&str>)> {
        let on = match self.head {
            "on" => true,
            "off" => false,
            _ => return None,
        };
        let names = self.args.iter().map(|a| if let Pipe::Name(n) = a { n.as_str() } else { unreachable!("a switch name") });
        Some((on, names.collect()))
    }
}

impl<'a> Parser<'a> {
    /// The macro `(off NAME ...)` or `(on NAME ...)` after its name: one pass for all the
    /// names, since a sequence of them would end their effect.
    pub(crate) fn switches(&mut self, f: &str) -> Result<Pipe, String> {
        let mut ns = Vec::new();
        while !self.at_close() {
            let n = self.name(&format!("a pass name after {f}"))?;
            if self.param(&n).is_some() {
                self.use_param(&n, Ty::Name)?;
                ns.push(n);
                continue;
            }
            host::switch(&n).ok_or_else(|| super::warn::unknown(format!("unknown {f} name {n}"), &n, INNER.iter().chain(&host::FLAGS).copied()))?;
            ns.push(n);
        }
        if ns.is_empty() {
            return Err(format!("{f} needs a pass name"));
        }
        Ok(Expanded::switches(f == "on", &ns.iter().map(String::as_str).collect::<Vec<_>>()))
    }
}

/// The macro `(smallest p)`: `(clear s) | p' | (take_min s)`, `s` a note register no other
/// `smallest` and no name a user writes has, `p'` being `p` with `(note s)` after each step
/// in its text that computes candidates (`crate::lang::eval::computes`, and a pipeline parameter),
/// also in the pipeline arguments of calls and in the bodies of `@inline` calls, but not in
/// the bodies of other calls.
pub fn smallest(p: Pipe) -> Pipe {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let s = format!("smallest#{}", NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
    let (body, scoped) = match &p {
        Pipe::Seq(ps) => (noted_stages(ps, &s, false), true),
        q => (noted_stage(q, &s, false), false),
    };
    let mut steps = vec![Pipe::app("clear", vec![Pipe::Name(s.clone())])];
    steps.extend(body);
    steps.push(Pipe::app("take_min", vec![Pipe::Name(s)]));
    Pipe::Expanded(Box::new(Expanded { head: "smallest", args: vec![p], steps, scoped, timed: super::builtins::get("smallest").is_some_and(|s| s.timed) }))
}

/// `p` with `(note s)` inside and after it (`smallest`); `inline` inside the body of an
/// `@inline` call, where a parameter's argument has the notes of the text it is written in.
fn noted_stage(p: &Pipe, s: &str, inline: bool) -> Vec<Pipe> {
    let q = noted(p, s, inline);
    if super::eval::computes(p) || matches!(p, Pipe::Var(Slot::Param(..) | Slot::Local(_, Holds::Fn(_)))) && !inline { vec![q, Pipe::app("note", vec![Pipe::Name(s.into())])] } else { vec![q] }
}

fn noted_stages(ps: &[Pipe], s: &str, inline: bool) -> Vec<Pipe> {
    ps.iter().flat_map(|p| noted_stage(p, s, inline)).collect()
}

/// `noted_stage` as one stage.
fn noted_one(p: &Pipe, s: &str, inline: bool) -> Pipe {
    let mut ps = noted_stage(p, s, inline);
    if ps.len() == 1 { ps.pop().unwrap() } else { Pipe::Seq(ps) }
}

/// `p` with `(note s)` after the steps inside it, also those of the pipelines inside its
/// expressions; not inside the functions given to a pass, which runs them on its own.
fn noted(p: &Pipe, s: &str, inline: bool) -> Pipe {
    match p {
        Pipe::App(f, args) => {
            let given = |i: usize| match f {
                Fun::Builtin(b) => b.sig.kind() != super::types::Kind::Group || b.sig.param(i).name.starts_with("sub"),
                _ => false,
            };
            let arg = |(i, a): (usize, &Pipe)| match f.param_ty(args, i) {
                Some(t) if !t.is_step() => noted_expr(a, s, inline),
                Some(_) if given(i) => a.clone(),
                _ => noted_one(a, s, inline),
            };
            let args = args.iter().enumerate().map(arg).collect();
            match f {
                Fun::Def(c) if c.def.inline => Pipe::App(Fun::Def(Arc::new(Call { def: c.def.clone(), body: Arc::new(noted_one(&c.body, s, true)) })), args),
                f => Pipe::App(f.clone(), args),
            }
        }
        Pipe::Seq(ps) => Pipe::Seq(noted_stages(ps, s, inline)),
        Pipe::Bind(x, q) => {
            let q = match x {
                Slot::Local(_, Holds::Group) => noted_one(q, s, inline),
                Slot::Local(_, Holds::Fn(t)) if t.is_step() => noted_one(q, s, inline),
                _ => noted_expr(q, s, inline),
            };
            Pipe::Bind(x.clone(), Arc::new(q))
        }
        Pipe::Expanded(m) => Pipe::Expanded(Box::new(Expanded { steps: noted_stages(&m.steps, s, inline), ..(**m).clone() })),
        Pipe::Drop(q, e) => Pipe::Drop(Arc::new(if *e { noted_expr(q, s, inline) } else { noted_one(q, s, inline) }), *e),
        Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::Var(_) | Pipe::FnValue(_) => p.clone(),
    }
}

/// `noted` for the expression `e`, where a sequence gives a number: its steps before the last
/// noted as stages.
fn noted_expr(e: &Pipe, s: &str, inline: bool) -> Pipe {
    match e {
        Pipe::Seq(ps) => {
            let (last, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
            let mut out = match steps {
                [g @ Pipe::Var(Slot::Local(_, Holds::Group))] => vec![g.clone()],
                steps => noted_stages(steps, s, inline),
            };
            out.push(noted_expr(last, s, inline));
            Pipe::Seq(out)
        }
        e => noted(e, s, inline),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::ast::show;
    use crate::lang::parser::parse;
    use crate::passes::Passes;

    /// The steps `(smallest ...)` in `p` expands to, its note registers named `s`, `t`, ... in
    /// the order they first appear.
    fn expansion(p: &Pipe) -> String {
        let Pipe::Expanded(m) = p else { panic!("{}", show(p)) };
        let mut out = show(&Pipe::Seq(m.steps.clone()));
        let mut names: Vec<String> = Vec::new();
        while let Some(i) = out.find("smallest#") {
            let end = out[i + 9..].find(|c: char| !c.is_ascii_digit()).map_or(out.len(), |k| i + 9 + k);
            let n = out[i..end].to_string();
            names.push(n.clone());
            out = out.replace(&n, ["s", "t", "u"][names.len() - 1]);
        }
        out
    }

    #[test]
    fn smallest_notes_each_step_that_computes() {
        let p = parse("(smallest lowbits | id | (save r) | (fix 2 tfunc) | (best 1 unshift id (seq r)) | (if (mixed main) (polish id)))").unwrap();
        assert_eq!(
            expansion(&p),
            "(clear s) | lowbits | (note s) | id | (save r) | (fix 2 tfunc | (note s)) | (best 1 (unshift | (note s)) id (seq r)) | (if (mixed main) ((polish id) | (note s))) | (take_min s)"
        );
        assert_eq!(show(&p), "(smallest lowbits | id | (save r) | (fix 2 tfunc) | (best 1 unshift id (seq r)) | (if (mixed main) (polish id)))", "shown as written");
        assert_eq!(p, parse(&show(&p)).unwrap(), "compared as written");
        let one = parse("(smallest (union (prepass id) take_minimal))").unwrap();
        assert_eq!(expansion(&one), "(clear s) | (union ((prepass id) | (note s)) (take_minimal | (note s))) | (take_min s)");
        let Pipe::Expanded(m) = &one else { unreachable!() };
        assert!(!m.scoped, "a single step runs in the enclosing sequence, as it would without smallest");
        let given = parse("(smallest (relate (lowbits | tfunc)) | (regions lowbits (best 1 tfunc unshift)))").unwrap();
        assert_eq!(expansion(&given), "(clear s) | (relate lowbits | tfunc) | (note s) | (regions lowbits (best 1 (tfunc | (note s)) (unshift | (note s)))) | (take_min s)", "not in the functions given to a pass");
        let nested = parse("(smallest lowbits | (smallest tfunc | none) | unshift)").unwrap();
        assert_eq!(
            expansion(&nested),
            "(clear s) | lowbits | (note s) | (smallest tfunc | none) | unshift | (note s) | (take_min s)",
            "shown as written inside"
        );
        let Pipe::Expanded(m) = &nested else { unreachable!() };
        let inner = expansion(&m.steps[3]);
        assert_eq!(inner, "(clear s) | tfunc | (note t) | (note s) | none | (take_min s)", "the outer note (t) in the inner expansion");
        let names: Vec<String> = [&nested, &m.steps[3]].iter().map(|p| if let Pipe::Expanded(m) = p { show(&m.steps[0]) } else { unreachable!() }).collect();
        assert_ne!(names[0], names[1], "each smallest has a register of its own");
    }

    #[test]
    fn smallest_notes_arguments_but_not_bodies_of_calls() {
        let passes = |spec: &str| Passes::parse(spec).unwrap_or_else(|e| panic!("{spec}: {e}"));
        let p = passes("(def (f p:pipe) rewrite | p) prepass=(smallest (f tfunc) | (relate rewrite))");
        assert_eq!(expansion(&p.prepass()), "(clear s) | (f tfunc | (note s)) | (note s) | (relate rewrite) | (note s) | (take_min s)");
        let Pipe::Expanded(m) = &p.prepass() else { unreachable!() };
        let Some((c, _)) = m.steps[1].call() else { unreachable!() };
        assert_eq!(show(&c.body), "rewrite | p", "the body of a def is a run of its own");
        let p = passes("(def @inline (g n p:pipe) (if ((size main) > n) rewrite) | p) prepass=(smallest (g 1 tfunc))");
        assert_eq!(expansion(&p.prepass()), "(clear s) | (g 1 tfunc | (note s)) | (take_min s)");
        let Pipe::Expanded(m) = &p.prepass() else { unreachable!() };
        let Some((c, _)) = m.steps[1].call() else { unreachable!() };
        let body = show(&c.body).replace(|c: char| c.is_ascii_digit(), "");
        assert_eq!(body, "(if ((size main) > n) (rewrite | (note smallest#))) | p", "an @inline body is noted; its argument has its notes");
        let p = passes("(def (w p) (smallest p | rewrite)) prepass=(w tfunc)");
        let pre = p.prepass();
        let Some((c, _)) = pre.call() else { unreachable!() };
        assert_eq!(expansion(&c.body), "(clear s) | p | (note s) | rewrite | (note s) | (take_min s)", "in a def body a parameter gives what its argument returns");
        let p = passes("(let k rewrite | tfunc) prepass=(smallest id | k)");
        assert_eq!(expansion(&p.prepass()), "(clear s) | id | rewrite | (note s) | tfunc | (note s) | (take_min s)", "a let is in the text");
        let p = passes("(def @inline (h p) (smallest p | none)) prepass=(h rewrite)");
        assert_eq!(expansion(&p.prepass()), "(clear s) | rewrite | (note s) | none | (take_min s)", "an @inline argument put in place");
        assert_eq!(p.to_string(), passes(&p.to_string()).to_string());
    }

    #[test]
    fn macros_print_as_written_and_run_their_expansion() {
        let off = parse("(off relate lowbits)").unwrap();
        let Pipe::Expanded(m) = &off else { panic!("{off:?}") };
        assert_eq!((show(&off).as_str(), show(&Pipe::Seq(m.steps.clone())).as_str()), ("(off relate lowbits)", "relate = 0 | lowbits = 0"));
        assert!(!m.scoped, "the switches stay set until the enclosing sequence ends");
        let on = parse("(on cut)").unwrap();
        let Pipe::Expanded(m) = &on else { panic!("{on:?}") };
        assert_eq!(show(&Pipe::Seq(m.steps.clone())), "(seq cut = 1)");
        let p = Passes::parse("(def (try_without name p) (best 1 p ((off name) | p))) prepass=(try_without relate rewrite)").unwrap();
        let pre = p.prepass();
        let Some((c, _)) = pre.call() else { panic!() };
        let Pipe::App(_, best) = &*c.body else { panic!() };
        let Pipe::Seq(without) = &best[2] else { panic!() };
        let Pipe::Expanded(m) = &without[0] else { panic!() };
        assert_eq!((show(&without[0]).as_str(), show(&Pipe::Seq(m.steps.clone())).as_str()), ("(off relate)", "(seq relate = 0)"), "a name argument put in place expands");
        let s = parse("(smallest lowbits | tfunc)").unwrap();
        let Pipe::Expanded(m) = &s else { panic!() };
        assert_eq!(m.head, "smallest");
        assert_eq!(show(&s), "(smallest lowbits | tfunc)");
        assert_eq!(s, parse(&show(&s)).unwrap(), "compared as written");
    }
}
