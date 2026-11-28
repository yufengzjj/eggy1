//! The checks of the pipelines a run may use (`Passes::check`): group variables read before
//! they are bound; and what a pipeline uses, which the warnings read too.

use super::ast::{Fun, Holds, Pipe, Slot, show};
use super::defs::{Call, expand};
use super::host::Passes;
use super::run::Gives;
use super::vars::{var, var_index};

impl Passes {
    /// Rejects pipelines that cannot run: a read of a group variable that nothing may have
    /// bound.
    pub(crate) fn check(&self) -> Result<(), String> {
        self.check_top()?;
        self.check_flow()?;
        for (name, uses) in self.uses() {
            if let Some(r) = &uses.unsaved {
                let how = match uses.kind(r) {
                    GROUP => format!("{r} = ... or (save {r})"),
                    FUNCTION => format!("{r}:TYPE = ..."),
                    _ => format!("{r} = ..."),
                };
                return Err(format!("{name} reads {} {r} before it is bound ({how})", uses.kind(r)));
            }
        }
        Ok(())
    }

    /// The top-level steps of the program: a group variable read before a step binds it.
    fn check_top(&self) -> Result<(), String> {
        let mut uses = Uses::default();
        for t in &self.program {
            match t.gives {
                Gives::Num => uses.expr(&t.pipe),
                _ => uses.walk(&t.pipe),
            }
            if let Some(r) = &uses.unsaved {
                return Err(format!("the program reads {} {r} before it is bound", uses.kind(r)));
            }
        }
        Ok(())
    }

    /// What each step gives against what the next takes (`flow`), in the bodies of the
    /// functions and the top-level steps.
    fn check_flow(&self) -> Result<(), String> {
        use super::flow::{Flow, expr, step};
        let cx = &mut super::infer::Infer::none();
        for d in &self.defs {
            super::flow::body(d).map_err(|e| format!("{}: {e}", d.name))?;
        }
        let mut f = Flow::None;
        for t in &self.program {
            match t.gives {
                Gives::Num | Gives::Text => {
                    expr(cx, &t.pipe, f)?;
                    f = if t.gives == Gives::Num { Flow::Num } else { Flow::Text };
                }
                Gives::Fn => {}
                _ => f = step(cx, &t.pipe, f)?,
            }
        }
        Ok(())
    }

    /// Each function's body by name, with what it uses.
    pub(crate) fn uses(&self) -> Vec<(String, Uses)> {
        let roots: Vec<(String, &Pipe)> = self.defs.iter().filter(|d| !d.has_names() && !d.inline).map(|d| (d.name.clone(), &*d.body)).collect();
        let mut called = Vec::new();
        roots.iter().for_each(|(_, p)| instances(p, &self.defs, &mut called));
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
        let mut out: Vec<(String, Uses)> = roots.iter().map(|(name, p)| (name.clone(), of(p, name))).collect();
        out.extend(called.iter().map(|(name, _, body)| (name.clone(), of(body, name))));
        out
    }
}

/// The calls in `p` of functions with name parameters, and those in the bodies they run, each
/// once per function and name arguments: the function's name, the name arguments, the body.
fn instances(p: &Pipe, defs: &[std::sync::Arc<super::defs::Def>], out: &mut Vec<(String, Vec<String>, std::sync::Arc<Pipe>)>) {
    p.each(&mut |q| instances(q, defs, out));
    if let Some((c, _)) = p.call()
        && c.def.inline
    {
        instances(&c.body, defs, out);
    } else if let Pipe::App(super::ast::Fun::Def(c), args) = p
        && c.def.has_names()
    {
        let c = c.latest(args, defs);
        let names: Vec<String> = args.iter().filter_map(|a| if let Pipe::Name(n) = a { Some(n.clone()) } else { None }).collect();
        if !out.iter().any(|(n, ns, _)| *n == c.def.name && *ns == names) {
            out.push((c.def.name.clone(), names, c.body.clone()));
            instances(&c.body, defs, out);
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
    /// The steps that do not use their input after a step that gives a value, which is dropped.
    pub(crate) dropping: Vec<String>,
    /// The local variables bound or read as numbers or function values; the others are
    /// group variables.
    pub(crate) kinds: Vec<(String, &'static str)>,
}

const GROUP: &str = "group variable";
const NUMBER: &str = "number variable";
const FUNCTION: &str = "function variable";
const TUPLE: &str = "tuple variable";

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
                if t.is_step() { self.walk(p) } else { self.expr(p) }
                self.bound_as(r, FUNCTION);
            }
            Pipe::Bind(Slot::Local(r, Holds::Num), e) => {
                self.expr(e);
                self.bound_as(r, NUMBER);
            }
            Pipe::Bind(Slot::Local(r, Holds::Tuple(_)), e) => {
                self.walk(e);
                self.bound_as(r, TUPLE);
            }
            Pipe::Bind(_, v) => self.expr(v),
            Pipe::Var(Slot::Local(r, Holds::Tuple(_))) if r != super::ast::INPUT => self.read_as(r, TUPLE),
            Pipe::Tuple(ps) => self.positions(ps),
            Pipe::Index(t, _) => self.walk(t),
            Pipe::Unpack(slots, e) => {
                self.walk(e);
                for x in slots.iter() {
                    match x {
                        Slot::Local(r, Holds::Group) => self.bound(r),
                        Slot::Local(r, Holds::Num) => self.bound_as(r, NUMBER),
                        Slot::Local(r, Holds::Fn(_)) => self.bound_as(r, FUNCTION),
                        Slot::Local(r, Holds::Tuple(_)) => self.bound_as(r, TUPLE),
                        x => unreachable!("{x:?} is not a local variable"),
                    }
                }
            }
            Pipe::Seq(ps) => self.seq(ps),
            Pipe::Expanded(m) if m.switch_names().is_some() => {}
            Pipe::Expanded(m) if m.is_call() => m.steps.iter().for_each(|q| self.walk(q)),
            Pipe::Expanded(m) => m.args.iter().for_each(|a| self.walk(a)),
            // An `@inline` body is checked as written out where it is called.
            Pipe::App(Fun::Def(c), args) if c.def.inline => {
                args.iter().zip(&c.def.params).for_each(|(a, p)| if p.ty.is_expr() { self.expr(a) });
                self.walk(&expand(c, args));
            }
            // A pipeline argument runs with the caller's group variables, at any point of the call
            // and any number of times.
            Pipe::App(Fun::Def(c), args) => {
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Param(..)) => {}
            e => self.expr(e),
        }
    }

    /// The positions of a tuple: expressions, and the others as steps.
    fn positions(&mut self, ps: &[(Pipe, super::types::Ty)]) {
        for (q, t) in ps {
            match t.is_expr() {
                true => self.expr(q),
                false => self.walk(q),
            }
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
        // A value is dropped where a step that does not use its input follows a step that
        // gives one and nothing read it since; `(save R)` keeps the value it is given.
        let mut unread = false;
        for p in ps {
            match super::eval::step_kind(p) {
                _ if matches!(p, Pipe::App(Fun::Builtin(b), _) if b.name == "save") => unread = false,
                super::eval::StepKind::Nothing => unread &= !uses_input(p),
                _ => {
                    if unread && !uses_input(p) {
                        let s = show(p);
                        if !s.contains('#') {
                            self.dropping.push(s);
                        }
                    }
                    unread = true;
                }
            }
        }
        ps.iter().for_each(|p| self.walk(p));
        if let Some(a) = ps.last().filter(|p| binds(p)) {
            self.idle_assign.push(show(a));
        }
    }

    fn app(&mut self, b: &super::builtins::Builtin, args: &[Pipe]) {
        let name = |i: usize| match &args[i] {
            Pipe::Name(n) => n.as_str(),
            a => unreachable!("{a:?} is not a name"),
        };
        match b.name {
            "show" | "parse" => args.iter().for_each(|a| self.walk(a)),
            "pre_done" => self.seen("t0"),
            "save" => self.bound(name(0)),
            "label" => self.read(name(0)),
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
                s if super::flow::is_group_step(s) => self.walk(s),
                e => self.expr(e),
            }),
            "scope" => self.walk(&args[0]),
            "tag" | "smaller" | "origin" => self.walk(&args[1]),
            "regions" => {
                self.repeated(&args[0]);
                self.repeated(&args[1]);
            }
            "again" => {
                self.repeated(&args[0]);
                self.walk(&args[1]);
            }
            _ => self.functions(b, args),
        }
    }

    /// The function arguments of a call of `b`, which may run any number of times.
    fn functions(&mut self, b: &super::builtins::Builtin, args: &[Pipe]) {
        for (i, a) in args.iter().enumerate() {
            match b.sig.param(i) {
                p if p.ty.is_step() => self.repeated(a),
                _ => {}
            }
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
                for (i, a) in args.iter().enumerate() {
                    match a {
                        _ if b.sig.param(i).ty.is_step() => self.repeated(a),
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
                args.get(c.def.params.len()).iter().for_each(|p| self.walk(p));
                self.call_args(c, args);
            }
            Pipe::Var(Slot::Local(r, Holds::Fn(_))) => self.read_as(r, FUNCTION),
            Pipe::Var(Slot::Local(r, Holds::Num)) => self.read_as(r, NUMBER),
            Pipe::Var(Slot::Local(r, Holds::Tuple(_))) if r != super::ast::INPUT => self.read_as(r, TUPLE),
            Pipe::Tuple(ps) => self.positions(ps),
            Pipe::Index(t, _) => self.walk(t),
            Pipe::Expanded(m) if m.is_call() => m.steps.iter().for_each(|q| self.walk(q)),
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

/// Whether the step `p` reads the value it is given.
fn uses_input(p: &Pipe) -> bool {
    match p {
        Pipe::Num(_) | Pipe::Text(_) | Pipe::Name(_) | Pipe::FnValue(_) => false,
        Pipe::Var(Slot::Local(n, Holds::Tuple(_))) => n == super::ast::INPUT,
        Pipe::Var(Slot::Global(_) | Slot::Local(_, Holds::Num | Holds::Group)) => false,
        Pipe::Tuple(ps) => ps.iter().any(|(q, t)| !t.is_function() && uses_input(q)),
        Pipe::Index(t, _) | Pipe::Unpack(_, t) => uses_input(t),
        Pipe::Seq(ps) => {
            for q in ps {
                if uses_input(q) {
                    return true;
                }
                if super::eval::step_kind(q) != super::eval::StepKind::Nothing {
                    return false;
                }
            }
            false
        }
        Pipe::Bind(Slot::Local(_, Holds::Fn(_)), _) => false,
        Pipe::Bind(_, e) => uses_input(e),
        Pipe::Expanded(m) if m.switch_names().is_some() => false,
        Pipe::App(Fun::Builtin(b), args) if b.sig.kind() == super::types::Kind::Effect => args.iter().any(uses_input),
        Pipe::Expanded(m) if m.is_call() => m.steps.first().is_some_and(uses_input),
        Pipe::App(Fun::Op(..), args) => args.iter().any(uses_input),
        Pipe::App(Fun::Builtin(b), args) => match b.input_at(args) {
            Some(k) => uses_input(&args[k]),
            None => b.sig.input.is_some() && b.sig.kind() != super::types::Kind::FromText,
        },
        Pipe::App(Fun::Def(c), args) => match args.get(c.def.params.len()) {
            Some(q) => uses_input(q),
            None if args.len() < c.def.params.len() => true,
            None => c.def.step || c.def.implicit.is_some() || args.iter().zip(&c.def.params).any(|(a, q)| q.ty == super::types::Ty::Num && uses_input(a)),
        },
        _ => true,
    }
}
