//! The checks of the pipelines a run may use (`Passes::check`): functions that need a
//! `simplify` run, functions that reach themselves, group variables read before they are bound;
//! and what a pipeline uses, which the warnings read too.

use super::ast::{Fun, Holds, Pipe, Slot, show, show_stage, starts_with_value};
use super::defs::{Call, expand};
use super::host::{self, Passes, SUBS};
use super::run::Gives;
use super::vars::{var, var_index};

impl Passes {
    /// Rejects pipelines that cannot run: an egglog round or `reprint` outside `pipeline`
    /// (only a `simplify` run has them), also in a function they call, and a function that
    /// reaches itself through other functions. The rebuilds of one term (`rewrite`, `simba`,
    /// `sub_NAME`: one node `rewrite`, which any pass over one term may run) recurse on
    /// subterms, and so may the functions they call that call them again.
    pub(crate) fn check(&self) -> Result<(), String> {
        self.check_top()?;
        let mut reach: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
        let mut needs = std::collections::HashMap::new();
        for (name, node, uses) in self.uses() {
            if let Some(r) = &uses.unsaved {
                let how = match uses.kind(r) {
                    GROUP => format!("{r} = ... or (save {r})"),
                    FUNCTION => format!("{r}:TYPE = ..."),
                    _ => format!("{r} = ..."),
                };
                return Err(format!("{name} reads {} {r} before it is bound ({how})", uses.kind(r)));
            }
            if let Some((what, sig)) = uses.needs_run.first() {
                match node.as_str() {
                    "pipeline" => {}
                    "prepass" | "polish" | "rewrite" => return Err(format!("{what} needs a simplify run and cannot be in {name}: {}", sig.decl())),
                    _ => {
                        needs.insert(node.clone(), (what.clone(), *sig));
                    }
                }
            }
            reach.entry(node).or_default().extend(uses.calls);
        }
        let reached = |start: &str| {
            let (mut seen, mut todo) = (Vec::<String>::new(), reach.get(start).cloned().unwrap_or_default());
            while let Some(n) = todo.pop() {
                if !seen.contains(&n) {
                    todo.extend(reach.get(&n).cloned().unwrap_or_default());
                    seen.push(n);
                }
            }
            seen
        };
        let inner = reached("rewrite");
        let starts = ["pipeline", "prepass", "polish"].into_iter().chain(self.defs.iter().map(|d| d.name.as_str()));
        for start in starts {
            if reached(start).iter().any(|n| n == start) && !(self.defs.iter().any(|d| d.name == start) && inner.iter().any(|n| n == start)) {
                return Err(format!("{start} reaches itself"));
            }
        }
        for start in ["prepass", "polish", "rewrite"] {
            if let Some((n, (what, sig))) = reached(start).iter().find_map(|n| needs.get(n).map(|w| (n, w))) {
                return Err(format!("{what} needs a simplify run and cannot be in {n}, which {start} calls: {}", sig.decl()));
            }
        }
        Ok(())
    }

    /// The top-level steps of the program: a group variable read before a step binds it, a
    /// step that computes candidates before any gives a value (the candidates start empty).
    fn check_top(&self) -> Result<(), String> {
        let mut uses = Uses::default();
        let mut value = false;
        for t in &self.program {
            match t.gives {
                Gives::Num => uses.expr(&t.pipe),
                _ => uses.walk(&t.pipe),
            }
            if let Some(r) = &uses.unsaved {
                return Err(format!("the program reads {} {r} before it is bound", uses.kind(r)));
            }
            let p = &t.pipe;
            match t.gives {
                Gives::Group | Gives::Nothing if !value && needs_input(p) => {
                    let p = match p {
                        Pipe::Bind(_, rhs) => rhs,
                        p => p,
                    };
                    return Err(format!("{} has no candidates to work on at the top level of the program, which starts with none: start from a value, as in (parse \"x + y\") | ... or t = (parse \"x + y\")", show_stage(p)));
                }
                Gives::Group => value |= gives_value(p),
                Gives::Text if !value && matches!(p, Pipe::App(_, args) if args.is_empty()) => {
                    return Err(format!("{} has no candidate to work on at the top level of the program, which starts with none: write its input, as in ({} (main t))", show(p), show(p)));
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Each pipeline by name, with its node in `check` (`rewrite` for `simba` and
    /// `sub_NAME`) and what it uses.
    pub(crate) fn uses(&self) -> Vec<(String, String, Uses)> {
        let main = [("pipeline", &self.pipeline), ("prepass", &self.prepass), ("polish", &self.polish), ("rewrite", &self.rewrite), ("simba", &self.simba)];
        let builtin = main.into_iter().chain(SUBS.iter().map(|(n, _)| *n).zip(&self.subs)).map(|(name, p)| {
            let node = if ["pipeline", "prepass", "polish"].contains(&name) { name } else { "rewrite" };
            (name.to_string(), node.to_string(), p)
        });
        let plain = self.defs.iter().filter(|d| !d.has_names() && !d.inline).map(|d| (d.name.clone(), d.name.clone(), &*d.body));
        let roots: Vec<(String, String, &Pipe)> = builtin.chain(plain).collect();
        let mut called = Vec::new();
        roots.iter().for_each(|(_, _, p)| instances(p, &mut called));
        let bound = |name: &str| self.defs.iter().find(|d| d.name == name).map_or_else(Vec::new, |d| d.bound());
        let of = |p: &Pipe, name: &str| {
            let mut uses = Uses::default();
            let bound = bound(name);
            uses.saved.extend(bound.iter().cloned());
            uses.reads.extend(bound);
            uses.walk(p);
            if binds(p) {
                uses.idle_assign.push(show(p));
            }
            uses
        };
        let mut out: Vec<(String, String, Uses)> = roots.iter().map(|(name, node, p)| (name.clone(), node.clone(), of(p, name))).collect();
        out.extend(called.iter().map(|(name, _, body)| (name.clone(), name.clone(), of(body, name))));
        out
    }
}

/// The calls in `p` of functions with name parameters, and those in the bodies they run, each
/// once per function and name arguments: the function's name, the name arguments, the body.
fn instances(p: &Pipe, out: &mut Vec<(String, Vec<String>, std::sync::Arc<Pipe>)>) {
    p.each(&mut |q| instances(q, out));
    if let Some((c, _)) = p.call()
        && c.def.inline
    {
        instances(&c.body, out);
    } else if let Some((c, args)) = p.call()
        && c.def.has_names()
    {
        let names: Vec<String> = args.iter().filter_map(|a| if let Pipe::Name(n) = a { Some(n.clone()) } else { None }).collect();
        if !out.iter().any(|(n, ns, _)| *n == c.def.name && *ns == names) {
            out.push((c.def.name.clone(), names, c.body.clone()));
            instances(&c.body, out);
        }
    }
}

/// Whether `p` only binds globals: an assignment, `(on NAME)` or `(off NAME)`.
fn binds(p: &Pipe) -> bool {
    match p {
        Pipe::Bind(x, _) => matches!(x, Slot::Global(_)),
        Pipe::Expanded(m) => m.switch_names().is_some(),
        _ => false,
    }
}

/// What a pipeline uses, for `Passes::check` and `Passes::warnings`.
#[derive(Default)]
pub(crate) struct Uses {
    /// The passes in it that need a `simplify` run (`@simplify_only`), by the name they are
    /// counted as.
    pub(crate) needs_run: Vec<(String, &'static super::types::Sig)>,
    /// The functions it runs: `prepass`, `polish`, `rewrite` (also for `simba` and
    /// `sub_NAME`, which any pass over one term may run) and those `def` defines.
    pub(crate) calls: Vec<String>,
    /// The group variables a `(save R)` or `R = p` may have bound by now, in run order; each
    /// pipeline has its own.
    pub(crate) saved: Vec<String>,
    /// The first group variable read where nothing can have bound it before.
    pub(crate) unsaved: Option<String>,
    /// Every group variable read, also by `pre_done` (`t0`, which it may find unbound).
    pub(crate) reads: Vec<String>,
    /// The assignments that end their sequence, so change nothing.
    pub(crate) idle_assign: Vec<String>,
    /// The variables assigned twice in a sequence with no read or other step between.
    pub(crate) reassigned: Vec<String>,
    /// The group variables bound and not read since on every path that reaches this point,
    /// from bindings at the same level of `if`s and other parts that may not run.
    pub(crate) pending: Vec<String>,
    /// The group variables bound again where they are `pending`: the earlier value is never
    /// read.
    pub(crate) dead: Vec<String>,
    /// The stages after a `|` that start with a group value, so drop the candidates before.
    pub(crate) dropping: Vec<String>,
    /// The local variables bound or read as numbers or function values; the others are
    /// group variables.
    pub(crate) kinds: Vec<(String, &'static str)>,
}

const GROUP: &str = "group variable";
const NUMBER: &str = "number variable";
const FUNCTION: &str = "function variable";

impl Uses {
    fn walk(&mut self, p: &Pipe) {
        match p {
            Pipe::App(Fun::Builtin(b), args) => self.app(b, args),
            Pipe::Bind(Slot::Local(r, Holds::Group), p) => {
                self.walk(p);
                self.bound(r);
                if binds(p) {
                    self.idle_assign.push(show(p));
                }
            }
            Pipe::Var(Slot::Local(r, Holds::Group)) => self.read(r),
            Pipe::Var(Slot::Local(r, Holds::Fn(_))) => self.read_as(r, FUNCTION),
            Pipe::Bind(Slot::Local(r, Holds::Fn(t)), p) => {
                match &**p {
                    Pipe::Seq(_) if !t.is_step() => self.expr(p),
                    p => self.walk(p),
                }
                self.bound_as(r, FUNCTION);
            }
            Pipe::Bind(Slot::Local(r, Holds::Num), e) => {
                self.expr(e);
                self.bound_as(r, NUMBER);
            }
            Pipe::Bind(_, v) => self.expr(v),
            Pipe::Seq(ps) => self.seq(ps),
            Pipe::Expanded(m) if m.switch_names().is_some() => {}
            Pipe::Expanded(m) => m.args.iter().for_each(|a| self.walk(a)),
            // An `@inline` body is checked as written out where it is called.
            Pipe::App(Fun::Def(c), args) if c.def.inline => {
                args.iter().zip(&c.def.params).for_each(|(a, p)| if p.ty.is_expr() { self.expr(a) });
                self.walk(&expand(c, args));
            }
            // A pipeline argument runs with the caller's group variables, at any point of the call
            // and any number of times.
            Pipe::App(Fun::Def(c), args) => {
                self.calls.push(c.def.name.clone());
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Param(..)) => {}
            e => self.expr(e),
        }
    }

    /// The steps `ps` of a sequence.
    fn seq(&mut self, ps: &[Pipe]) {
        let flat: Vec<Pipe>;
        let ps = match ps.iter().any(|p| p.call().is_some_and(|(c, _)| c.def.inline)) {
            true => {
                flat = ps.iter().flat_map(flat_stages).collect();
                &flat
            }
            false => ps,
        };
        let mut pending: Vec<usize> = Vec::new();
        for p in ps {
            match p {
                Pipe::Bind(Slot::Global(i), v) => {
                    if reads_var(v, *i) {
                        pending.retain(|j| j != i);
                    }
                    self.assigned(&mut pending, *i);
                }
                Pipe::Expanded(m) if m.switch_names().is_some() => m.switch_names().unwrap().1.into_iter().filter_map(var_index).for_each(|i| self.assigned(&mut pending, i)),
                _ => pending.clear(),
            }
        }
        ps.iter().for_each(|p| self.walk(p));
        for p in ps.iter().skip(1).filter(|p| starts_with_value(p)) {
            let s = show_stage(p);
            if !s.contains('#') {
                self.dropping.push(s);
            }
        }
        if let Some(a) = ps.last().filter(|p| binds(p)) {
            self.idle_assign.push(show(a));
        }
    }

    fn app(&mut self, b: &super::builtins::Builtin, args: &[Pipe]) {
        if b.sig.simplify_only {
            self.needs_run.push((host::step_name(b.name, args), b.sig));
        }
        let name = |i: usize| match &args[i] {
            Pipe::Name(n) => n.as_str(),
            a => unreachable!("{a:?} is not a name"),
        };
        match b.name {
            "prepass" | "polish" | "pipeline" => self.calls.push(b.name.into()),
            "show" | "parse" => args.iter().for_each(|a| self.walk(a)),
            "pre_done" => self.seen("t0"),
            "save" => self.bound(name(0)),
            "load" | "label" => self.read(name(0)),
            "union" => args.iter().for_each(|p| self.walk(p)),
            "first" => {
                self.walk(&args[0]);
                args[1..].iter().for_each(|p| self.maybe(p));
            }
            "best" => {
                args[1..].iter().for_each(|p| self.walk(p));
                self.expr(&args[0]);
            }
            "fix" | "wins" => {
                self.expr(&args[0]);
                self.repeated(&args[1]);
            }
            "if" => {
                self.expr(&args[0]);
                let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
                self.walk(&args[1]);
                let after_a = std::mem::take(&mut self.pending);
                self.walk(&args[2]);
                let both: Vec<String> = self.pending.drain(..).filter(|r| after_a.contains(r)).collect();
                self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
                for r in both {
                    if !self.pending.contains(&r) {
                        self.pending.push(r);
                    }
                }
            }
            "retry" => {
                self.walk(&args[1]);
                self.expr(&args[0]);
                self.maybe(&args[2]);
            }
            "filter" | "assert" => self.expr(&args[0]),
            "print" => args.iter().for_each(|a| match a {
                Pipe::Var(Slot::Local(r, Holds::Group)) => self.read(r),
                Pipe::Name(_) | Pipe::Text(_) => {}
                f if f.is_function_value() => {}
                e => self.expr(e),
            }),
            "scope" => self.walk(&args[0]),
            "tag" | "smaller" | "origin" => self.walk(&args[1]),
            // Both rebuild with `Passes::rewrite`.
            "regions" => {
                self.calls.push("rewrite".into());
                self.repeated(&args[0]);
            }
            "again" => {
                self.calls.push("rewrite".into());
                self.walk(&args[0]);
            }
            _ if b.over_term() => self.calls.push("rewrite".into()),
            _ => {}
        }
    }

    fn call_args(&mut self, c: &Call, args: &[Pipe]) {
        use super::types::Ty;
        for (a, p) in args.iter().zip(&c.def.params) {
            match (&p.ty, a) {
                (t, e) if t.is_expr() => self.expr(e),
                (Ty::Group, Pipe::Var(Slot::Local(r, _))) => self.read(r),
                (Ty::Name | Ty::Group, _) => {}
                (_, p) => self.repeated(p),
            }
        }
    }

    fn assigned(&mut self, pending: &mut Vec<usize>, i: usize) {
        if pending.contains(&i) {
            self.reassigned.push(var(i).name.to_string());
        } else {
            pending.push(i);
        }
    }

    /// `p` run more than once: a read can see a save of an earlier run.
    fn repeated(&mut self, p: &Pipe) {
        let mut body = Uses::default();
        body.walk(p);
        self.saved.extend(body.saved);
        self.maybe(p);
    }

    /// `p` run or not. A save in `p` does not make an earlier one dead (`(save t) | (if c
    /// (save t))` keeps a default), and only what is pending either way stays pending.
    fn maybe(&mut self, p: &Pipe) {
        let (before, n) = (std::mem::take(&mut self.pending), self.reads.len());
        self.walk(p);
        self.pending = before.into_iter().filter(|r| !self.reads[n..].contains(r)).collect();
    }

    fn bound(&mut self, r: &str) {
        self.saved.push(r.to_string());
        if self.pending.iter().any(|s| s == r) {
            self.dead.push(r.to_string());
        } else {
            self.pending.push(r.to_string());
        }
    }

    fn seen(&mut self, r: &str) {
        self.reads.push(r.to_string());
        self.pending.retain(|s| s != r);
    }

    fn bound_as(&mut self, r: &str, kind: &'static str) {
        self.kinds.push((r.to_string(), kind));
        self.bound(r);
    }

    fn read_as(&mut self, r: &str, kind: &'static str) {
        self.kinds.push((r.to_string(), kind));
        self.read(r);
    }

    /// What `r` is, for messages: a group variable unless bound or read as another kind.
    pub(crate) fn kind(&self, r: &str) -> &'static str {
        self.kinds.iter().find(|(n, _)| n == r).map_or(GROUP, |(_, k)| k)
    }

    fn read(&mut self, r: &str) {
        self.seen(r);
        if self.unsaved.is_none() && !self.saved.iter().any(|s| s == r) {
            self.unsaved = Some(r.to_string());
        }
    }

    fn expr(&mut self, e: &Pipe) {
        match e {
            Pipe::App(Fun::Builtin(b), args) => {
                let args = match b.input_at(args) {
                    Some(k) => {
                        self.walk(&args[k]);
                        &args[..k]
                    }
                    None => &args[..],
                };
                if ["opaque", "rebuilds"].contains(&b.name) {
                    self.calls.push("prepass".into());
                }
                for a in args.iter() {
                    match a {
                        Pipe::Name(r) => self.read(r),
                        a => self.expr(a),
                    }
                }
            }
            Pipe::App(Fun::Op(..), args) => args.iter().for_each(|a| self.expr(a)),
            Pipe::Seq(ps) => {
                let (e, steps) = ps.split_last().expect("a sequence that gives a number has a last step");
                match steps {
                    [p] => self.walk(p),
                    ps => self.seq(ps),
                }
                self.expr(e);
            }
            Pipe::App(Fun::Def(c), args) => {
                self.calls.push(c.def.name.clone());
                args.get(c.def.params.len()).iter().for_each(|p| self.walk(p));
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Local(r, Holds::Fn(_))) => self.read_as(r, FUNCTION),
            Pipe::Var(Slot::Local(r, Holds::Num)) => self.read_as(r, NUMBER),
            _ => {}
        }
    }
}

/// The stages `p` stands for in a sequence, for `Uses`: those of an `@inline` body written
/// out, after a `filter` of each numeric argument (read at the call, a step there).
fn flat_stages(p: &Pipe) -> Vec<Pipe> {
    match p {
        Pipe::App(Fun::Def(c), args) if c.def.inline => {
            let num = args.iter().zip(&c.def.params).filter(|(_, p)| p.ty.is_expr());
            let filters = num.map(|(e, _)| Pipe::app("filter", vec![e.clone()]));
            let body = match expand(c, args) {
                Pipe::Seq(ps) if c.def.flat => ps.iter().flat_map(flat_stages).collect(),
                q => flat_stages(&q),
            };
            filters.chain(body).collect()
        }
        _ => vec![p.clone()],
    }
}

/// Whether the step `p` gives candidates that do not depend on its input: a group value, `load`.
fn gives_value(p: &Pipe) -> bool {
    starts_with_value(p) || matches!(p, Pipe::App(Fun::Builtin(b), _) if b.name == "load")
}

/// Whether the step `p` computes on candidates it is given before any of its steps gives a
/// value; a binding of a group variable by its right side.
fn needs_input(p: &Pipe) -> bool {
    let steps = |ps: &[Pipe]| {
        for q in ps {
            if gives_value(q) {
                return false;
            }
            if needs_input(q) {
                return true;
            }
        }
        false
    };
    match p {
        Pipe::Seq(ps) => steps(ps),
        Pipe::Expanded(m) => steps(&m.steps),
        Pipe::Bind(Slot::Local(_, Holds::Group), rhs) => needs_input(rhs),
        Pipe::Bind(..) => false,
        Pipe::App(Fun::Def(c), _) if !c.def.inline => !gives_value(p),
        Pipe::App(Fun::Builtin(b), _) if b.name == "pipeline" => true,
        Pipe::App(Fun::Builtin(b), _) => b.timed && !gives_value(p),
        _ => false,
    }
}

/// Whether `e` reads the variable at `i`.
fn reads_var(e: &Pipe, i: usize) -> bool {
    let group = |p: &Pipe| matches!(p, Pipe::Var(Slot::Local(_, Holds::Group)));
    match e {
        Pipe::Var(Slot::Global(j)) => *j == i,
        Pipe::App(Fun::Builtin(b), cs) => match b.input_at(cs) {
            Some(k) => !group(&cs[k]) && (!cs[k].picks() || reads_var(&cs[k], i)) || cs[..k].iter().any(|c| reads_var(c, i)),
            None => cs.iter().any(|c| reads_var(c, i)),
        },
        Pipe::App(Fun::Op(..), cs) => cs.iter().any(|c| reads_var(c, i)),
        Pipe::Seq(ps) => !matches!(&ps[..ps.len() - 1], [p] if group(p)) || reads_var(&ps[ps.len() - 1], i),
        Pipe::App(Fun::Def(c), args) => {
            let num = args.iter().zip(&c.def.params).filter(|(_, p)| p.ty.is_expr());
            c.def.steps || args.get(c.def.params.len()).is_some_and(|p| !group(p)) || num.into_iter().any(|(e, _)| reads_var(e, i))
        }
        _ => false,
    }
}
