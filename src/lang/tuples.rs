//! Tuples in elaboration (`docs/lang/tuples.md`): `(a, b, ...)`; `(index i t)` of a tuple,
//! whose position `i` is a number written out so that its type is known; `(a, b) = t`; and a
//! step that gives a tuple followed by one that takes it.

use super::ast::{Fun, Holds, Pipe, Slot, gives_tuple, input_of, show, show_expr, show_tuple_input, stage, starts_with_value, value_ty};
use super::defs::def_sig;
use super::elab::{Elab, Items, Rhs, group};
use super::syntax::{Node, Pipeline, Syn};
use super::types::Ty;
use super::vars::var_index;
use std::sync::Arc;

impl<'a> Elab<'a> {
    /// The type of the tuple the variable or parameter `n` holds.
    pub(crate) fn tuple_var(&self, n: &str) -> Option<Ty> {
        match self.param(n) {
            Some(i) => self.params[i].ty.clone().filter(|t| t.positions().is_some()),
            None => self.tuples.iter().rev().find(|(m, _)| m == n).map(|(_, t)| t.clone()),
        }
    }

    /// Whether `n` is a function defined that gives a tuple.
    pub(crate) fn tuple_def(&self, n: &str) -> bool {
        self.param(n).is_none() && self.defs.get(n).and_then(|d| d.def.as_ref()).is_some_and(|d| d.tuple.is_some())
    }

    /// Whether the name `n` alone gives a tuple: a variable or parameter that holds one, or a
    /// function without parameters that gives one and is applied here.
    pub(crate) fn tuple_term_name(&self, n: &str) -> bool {
        self.tuple_var(n).is_some() || self.tuple_def(n) && self.defs[n].params.is_empty() && (self.input || self.defs[n].def.as_ref().is_some_and(|d| !d.step))
    }

    /// Whether `x` gives a tuple by what it is written of: a tuple, a name that gives one, a
    /// call of a function that gives one, or `(index i t)` of such a tuple.
    pub(crate) fn tuple_term_known(&self, x: &Syn) -> bool {
        match &x.node {
            Node::Name(n) => self.tuple_term_name(n),
            Node::Tuple(_) => true,
            Node::Paren(_) => x.head_name().is_some_and(|n| self.tuple_def(n)) || self.index_of_known(x),
            _ => false,
        }
    }

    /// Whether `x` is `(index i t)` of a tuple `t` known by what it is written of.
    fn index_of_known(&self, x: &Syn) -> bool {
        self.index_form(x).is_some_and(|t| self.tuple_term_known(t))
    }

    /// The tuple of `(index i t)` where `x` is written so.
    fn index_form<'s>(&self, x: &'s Syn<'s>) -> Option<&'s Syn<'s>> {
        let (st, rest) = x.head_stage()?;
        (st.items[0].name() == Some("index") && self.param("index").is_none() && rest.is_empty() && st.items.len() >= 3).then(|| &st.items[2])
    }

    /// `(index i t)` where `x` is written so and `t` gives a tuple: its position `i` and the
    /// type of that position; where `t` is a pipeline in parentheses that gives a group, the
    /// `index` of the group, as a step. `None` for anything else.
    pub(crate) fn tuple_index(&mut self, x: &Syn) -> Result<Option<(Pipe, Ty)>, String> {
        let Some(t) = self.index_form(x) else { return Ok(None) };
        if self.tuple_term_known(t) {
            return self.index_tuple(x, None).map(Some);
        }
        if t.paren().is_none_or(|p| p.stages.len() < 2) {
            return Ok(None);
        }
        let p = self.stage(t)?;
        if let Some(ty) = value_ty(&p).filter(|ty| ty.positions().is_some()) {
            return self.index_tuple(x, Some((p, ty))).map(Some);
        }
        let mut c = Items::of(x);
        let i = self.earg_of(&mut c)?;
        let (st, _) = x.head_stage().unwrap();
        if let Some(y) = st.items.get(3) {
            return Err(format!("expected ), found {}", self.tok(y.at)));
        }
        let index = Pipe::App(Fun::Builtin(super::builtins::builtin("index").unwrap()), vec![i].into());
        Ok(Some((Pipe::Seq(vec![p, index]), Ty::Group)))
    }

    /// `(index i t)` of a tuple `t`, `t` elaborated when given, and the type of its position
    /// `i`.
    fn index_tuple(&mut self, x: &Syn, given: Option<(Pipe, Ty)>) -> Result<(Pipe, Ty), String> {
        let (st, _) = x.head_stage().unwrap();
        let tx = &st.items[2];
        let i = match &st.items[1].node {
            Node::Num(i) => *i,
            _ => {
                let mut c = Items::of(x);
                let e = self.earg_of(&mut c)?;
                let (t, ty) = match given {
                    Some(g) => g,
                    None => self.tuple_term(tx)?,
                };
                let t = show_tuple_input(&t);
                return Err(format!("(index {} {t}): a position of a tuple is a number written out, as in (index 0 {t}), since each position has its own type ({t} is {ty})", show_expr(&e, 7)));
            }
        };
        let (t, _) = match given {
            Some(g) => g,
            None => self.tuple_term(tx)?,
        };
        if let Some(y) = st.items.get(3) {
            return Err(format!("expected ), found {}", self.tok(y.at)));
        }
        let shown = show_tuple_input(&t);
        self.index_of(t, i, &shown)
    }

    /// Position `i` of the tuple `t`, written `shown`, and its type.
    fn index_of(&self, t: Pipe, i: u64, shown: &str) -> Result<(Pipe, Ty), String> {
        let ty = value_ty(&t).expect("a term that gives a tuple");
        let ts = ty.positions().expect("a tuple type");
        match usize::try_from(i).ok().filter(|i| *i < ts.len()) {
            Some(k) => Ok((Pipe::Index(Arc::new(t), k), ts[k].clone())),
            None => Err(format!("(index {i} {shown}) is out of range: {ty} has positions 0 to {}", ts.len() - 1)),
        }
    }

    /// A term that gives a tuple, and the tuple's type.
    pub(crate) fn tuple_term(&mut self, x: &Syn) -> Result<(Pipe, Ty), String> {
        self.tuple_term_for(x, None)
    }

    /// `tuple_term` where a tuple of type `want` is taken, which a tuple written out reads its
    /// positions by.
    fn tuple_term_for(&mut self, x: &Syn, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        let not_tuple = |e: &Self| format!("expected a tuple, as in (1, t), a variable that holds one or a call of a function that gives one; found {}", e.tok(x.at));
        match &x.node {
            Node::Name(n) if self.tuple_var(n).is_some() => {
                let ty = self.tuple_var(n).unwrap();
                self.use_param(n, ty.clone())?;
                Ok((Pipe::Var(Slot::Local(n.to_string(), Holds::Tuple(Box::new(ty.clone())))), ty))
            }
            Node::Name(n) if self.tuple_term_name(n) => {
                self.used.push(n.to_string());
                let p = self.defs[*n].pipe.clone();
                let ty = value_ty(&p).expect("a call of a function that gives a tuple");
                Ok((p, ty))
            }
            Node::Tuple(_) => self.tuple_literal(x, want),
            Node::Paren(_) if self.index_form(x).is_some() => match self.tuple_index(x)? {
                Some((p, ty)) if ty.positions().is_some() => Ok((p, ty)),
                Some((p, ty)) => Err(format!("{} gives {ty}, not a tuple", show(&p))),
                None => Err(not_tuple(self)),
            },
            Node::Paren(_) if x.head_name().is_some_and(|n| self.tuple_def(n)) => {
                let n = x.head_name().unwrap().to_string();
                let mut c = Items::of(x);
                let p = self.def_call_in(&n, &mut c)?;
                let ty = value_ty(&p).expect("a call of a function that gives a tuple");
                Ok((p, ty))
            }
            Node::Paren(_) => {
                let p = self.stage(x)?;
                match value_ty(&p).filter(|t| t.positions().is_some()) {
                    Some(ty) => Ok((p, ty)),
                    None => Err(not_tuple(self)),
                }
            }
            _ => Err(not_tuple(self)),
        }
    }

    /// `(a, b, ...)`: each position read as `position` reads it, where a tuple of type `want`
    /// is taken by the type of that position.
    pub(crate) fn tuple_literal(&mut self, x: &Syn, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        let positions = x.tuple().expect("a tuple");
        let mut ps = Vec::new();
        for pl in positions {
            let at = want.and_then(Ty::positions).and_then(|ts| ts.get(ps.len()));
            ps.push(self.inside(|e| e.position(pl, at))?);
        }
        let ts: Vec<Ty> = ps.iter().map(|(_, t)| t.clone()).collect();
        let ty = if ts.contains(&Ty::Any) { Ty::Tuple(ts.into()) } else { Ty::tuple(ts)? };
        Ok((Pipe::Tuple(ps.into()), ty))
    }

    /// A position of a tuple and its type, `want` where the tuple is taken by a parameter of a
    /// tuple type: a text, a tuple, `(index i t)` of a tuple, a function written alone, a
    /// function variable or parameter, a group variable, an expression, or else one step (a
    /// pipeline in parentheses), as the right side of an assignment reads it. A function
    /// written alone that lacks at most its input is applied to the step's input where `want`
    /// is no function type and the step has an input, else it is the function value.
    fn position(&mut self, pl: &Pipeline, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        let st = &pl.stages[0];
        let x = &st.items[0];
        let alone = st.items.len() == 1 && pl.stages.len() == 1;
        let out = match &x.node {
            Node::Assign(super::syntax::Lhs::Name(n), _) => return Err(format!("a position of a tuple is a value, not an assignment: {n} = ...")),
            Node::Name(n) if alone && let Some(s) = self.bare_fn(n) => match want.filter(|w| w.is_function()) {
                None if self.input || s.input.is_none() => match s.result {
                    Ty::Num => (self.expr(x)?, Ty::Num),
                    Ty::Text => (self.text_value(x)?, Ty::Text),
                    _ => (self.stage(x)?, Ty::Group),
                },
                w => {
                    let ty = w.cloned().unwrap_or_else(|| {
                        let input = if s.input.as_ref().is_some_and(|i| i.ty == Ty::Group) { Ty::Group } else { Ty::Term };
                        Ty::Fn(Box::new(input), Box::new(s.result.clone()))
                    });
                    let outer = std::mem::replace(&mut self.input, true);
                    let f = self.fn_rhs("a position", &ty, x);
                    self.input = outer;
                    (f?, ty)
                }
            },
            Node::Str(t) => (Pipe::Text(t.to_string()), Ty::Text),
            _ if self.text_fn(x) => (self.text_value(x)?, Ty::Text),
            _ if let Some((p, t)) = self.tuple_index(x)? => (p, t),
            _ if self.tuple_term_known(x) => self.tuple_term_for(x, want.filter(|w| w.positions().is_some()))?,
            Node::Name(n) if alone && self.param(n).is_none() && self.fn_var(n).is_some() => {
                let f = self.fn_read(n.to_string());
                let Pipe::Var(Slot::Local(_, Holds::Fn(t))) = &f else { unreachable!("a function variable read") };
                let t = t.clone();
                (f, t)
            }
            Node::Name(n) if alone && self.param(n).is_some_and(|i| self.params[i].ty.as_ref().is_some_and(Ty::is_function)) => {
                let i = self.param(n).unwrap();
                self.count_param(n);
                (Pipe::Var(Slot::Param(i, n.to_string())), self.params[i].ty.clone().unwrap())
            }
            Node::Name(n) if alone && self.group_value(n) => {
                self.use_param(n, Ty::Group)?;
                (group(n.to_string()), Ty::Group)
            }
            Node::Name(n) if alone && self.param(n).is_none() && self.unknown(n) && self.local_kind(n).is_none() => {
                self.group_name(n)?;
                (group(n.to_string()), Ty::Group)
            }
            Node::Name(n) if alone && self.param(n).is_some_and(|i| self.params[i].ty.is_none()) => {
                self.count_param(n);
                self.holes.push(n.to_string());
                (Pipe::Var(Slot::Param(self.param(n).unwrap(), n.to_string())), Ty::Any)
            }
            _ if self.rhs_number(x, true) => (self.expr(x)?, Ty::Num),
            _ => match self.rhs_step(x)? {
                Rhs::Num(e) => (e, Ty::Num),
                Rhs::Group(p) if gives_tuple(&p) => {
                    let t = value_ty(&p).unwrap();
                    (p, t)
                }
                Rhs::Group(p) => (p, Ty::Group),
            },
        };
        if pl.stages.len() > 1 {
            return Err(format!("a position of a tuple is one value or step: write a pipeline in parentheses, as in (({} | ...), 1)", stage(&out.0)));
        }
        if let Some(y) = st.items.get(1) {
            return Err(format!("expected , or ) in a tuple, found {}", self.tok(y.at)));
        }
        Ok(out)
    }

    /// `n = t`: the tuple `t` of type `ty` bound to the local variable `n`.
    pub(crate) fn bind_tuple(&mut self, n: &str, t: Pipe, ty: Ty) -> Result<Pipe, String> {
        if let Some(k) = self.local_kind(n).filter(|k| *k != "tuple") {
            return Err(format!("{n} is a {k} variable, so it cannot hold a tuple: {} gives {ty}", show_tuple_input(&t)));
        }
        if var_index(n).is_some() {
            return Err(format!("{n} is a variable that holds a number, so it cannot hold a tuple: {} gives {ty}", show_tuple_input(&t)));
        }
        self.local_name(n)?;
        self.tuples.push((n.to_string(), ty.clone()));
        Ok(Pipe::Bind(Slot::Local(n.to_string(), Holds::Tuple(Box::new(ty))), Arc::new(t)))
    }

    /// The right side `x` of an assignment where it gives a tuple by what it is written of,
    /// and the tuple's type.
    pub(crate) fn tuple_rhs(&mut self, x: &Syn) -> Result<Option<(Pipe, Ty)>, String> {
        match self.tuple_term_known(x) {
            true => self.tuple_term(x).map(Some),
            false => Ok(None),
        }
    }

    /// `(a, b, ...) = t`: each name bound to its position of the tuple `t`, as a local
    /// variable of the kind the position's type says.
    pub(crate) fn unpack(&mut self, names: &[&str], rhs: &Syn) -> Result<Pipe, String> {
        for (i, n) in names.iter().enumerate() {
            if names[..i].contains(n) {
                return Err(format!("{n} is written twice in ({}, {n}, ...) = ...", names[..i].join(", ")));
            }
        }
        let lhs = format!("({})", names.join(", "));
        let takes = |e: &Self| format!("{lhs} = ... takes a tuple, as in {lhs} = (1, t), a variable that holds one or a call of a function that gives one; found {}", e.tok(rhs.at));
        let (e, ty) = match () {
            _ if self.tuple_term_known(rhs) => self.tuple_term(rhs)?,
            _ if rhs.paren().is_some_and(|p| p.stages.len() > 1) => {
                let p = self.stage(rhs)?;
                match value_ty(&p).filter(|t| t.positions().is_some()) {
                    Some(ty) => (p, ty),
                    None => return Err(takes(self)),
                }
            }
            _ => return Err(takes(self)),
        };
        let ts = ty.positions().expect("a tuple type").to_vec();
        let shown = show_tuple_input(&e);
        if ts.len() != names.len() {
            return Err(format!("{lhs} = {shown} binds {} names, but {shown} is {ty}, which has {} positions", names.len(), ts.len()));
        }
        let mut slots = Vec::new();
        for (i, (n, t)) in names.iter().zip(&ts).enumerate() {
            let (holds, kind) = match t {
                Ty::Num => (Holds::Num, "number"),
                Ty::Group => (Holds::Group, "group"),
                Ty::Tuple(_) => (Holds::Tuple(Box::new(t.clone())), "tuple"),
                t if t.is_function() => (Holds::Fn(t.clone()), "function"),
                t => return Err(format!("{n} would hold position {i} of {shown}, which is {t}: a variable holds a number, a group, a function or a tuple")),
            };
            if let Some(k) = self.local_kind(n).filter(|k| *k != kind) {
                return Err(format!("{n} is a {k} variable, so it cannot hold position {i} of {shown}, which is {t}"));
            }
            if var_index(n).is_some() {
                return Err(format!("{n} is a global variable; {lhs} = ... binds local variables"));
            }
            self.local_name(n)?;
            match &holds {
                Holds::Num if !self.locals.iter().any(|l| l == n) => self.locals.push(n.to_string()),
                Holds::Group if !self.groups.iter().any(|g| g == n) => self.groups.push(n.to_string()),
                Holds::Fn(t) => self.fns.push((n.to_string(), t.clone())),
                Holds::Tuple(t) => self.tuples.push((n.to_string(), (**t).clone())),
                _ => {}
            }
            slots.push(Slot::Local(n.to_string(), holds));
        }
        Ok(Pipe::Unpack(slots.into(), Arc::new(e)))
    }

    /// The argument for the parameter of type `want` (a tuple) of a call; `whose` names it.
    pub(crate) fn tuple_arg(&mut self, c: &mut Items, want: &Ty, whose: &dyn Fn() -> String) -> Result<Pipe, String> {
        let Some(x) = c.peek() else { return Err(format!("{}; found {}", whose(), self.tok(c.tok()))) };
        if let Node::Name(n) = &x.node
            && self.param(n).is_some_and(|i| self.params[i].ty.is_none())
        {
            c.next();
            self.use_param(n, want.clone())?;
            return Ok(Pipe::Var(Slot::Local(n.to_string(), Holds::Tuple(Box::new(want.clone())))));
        }
        let (e, ty) = match () {
            _ if self.tuple_term_known(x) => {
                c.next();
                self.tuple_term_for(x, Some(want))?
            }
            _ if x.paren().is_some_and(|p| p.stages.len() > 1) => {
                c.next();
                let p = self.stage(x)?;
                match value_ty(&p).filter(|t| t.positions().is_some()) {
                    Some(ty) => (p, ty),
                    None => return Err(format!("{}; found {}", whose(), self.tok(x.at))),
                }
            }
            _ => return Err(format!("{}; found {}", whose(), self.tok(x.at))),
        };
        if ty != *want && !self.fill_holes(&e, &ty, want) {
            return Err(format!("{}; {} is {ty}", whose(), show_tuple_input(&e)));
        }
        Ok(e)
    }

    /// The step `x` after `| ` that takes the tuple of type `ty` the step `origin` gives,
    /// without the tuple, which the run puts in: `(index i)`, which takes its position `i`, or a
    /// call of a function whose last parameter takes that tuple; and the type it gives.
    pub(crate) fn tuple_taker(&mut self, origin: &Pipe, ty: &Ty, x: &Syn) -> Result<(Pipe, Ty), String> {
        let shown = stage(origin);
        if let Some((st, [])) = x.head_stage()
            && st.items[0].name() == Some("index")
            && self.param("index").is_none()
            && st.items.len() == 2
        {
            let Node::Num(i) = st.items[1].node else {
                let mut c = Items::of(x);
                let e = self.earg_of(&mut c)?;
                return Err(format!("{shown} | (index {}): a position of a tuple is a number written out, as in (index 0), since each position has its own type ({shown} is {ty})", show_expr(&e, 7)));
            };
            return self.index_of(input_of(ty.clone()), i, &shown);
        }
        let (open, n) = match &x.node {
            Node::Name(n) => (false, n.to_string()),
            Node::Paren(_) => (true, x.head_name().unwrap_or("").to_string()),
            _ => (false, String::new()),
        };
        let takes = self.param(&n).is_none().then(|| self.defs.get(&n)).flatten().and_then(|d| d.def.clone()).filter(|d| d.params.last().is_some_and(|p| p.ty.positions().is_some()));
        let Some(d) = takes else { return Err(format!("{shown} gives {ty}; {}", self.takes(x))) };
        let last = d.params.last().unwrap();
        if last.ty != *ty && !self.fill_holes(origin, ty, &last.ty) {
            return Err(format!("{n} takes {last}: {}; {shown} gives {ty}", super::defs::sig_of(&d)));
        }
        let rest = def_sig(&n, &d.params[..d.params.len() - 1]);
        let args = match open {
            true => {
                let mut c = Items::of(x);
                let a = match rest.params.is_empty() {
                    true => Vec::new(),
                    false => self.inside(|e| e.args(&rest, true, &mut c))?,
                };
                self.close(&c)?;
                a
            }
            false => Vec::new(),
        };
        self.used.push(n.clone());
        let gives = match (&d.tuple, &d.value) {
            (Some(t), _) => t.clone(),
            (None, Some(_)) => Ty::Num,
            (None, None) => Ty::Group,
        };
        Ok((self.call_of(&n, args, None)?, gives))
    }

    /// Whether the tuple `e` of type `have` fits where `want` is taken once the parameters
    /// written alone in its positions (`any` in `have`) take the types there.
    fn fill_holes(&mut self, e: &Pipe, have: &Ty, want: &Ty) -> bool {
        match (have, want, e) {
            (Ty::Any, w, Pipe::Var(Slot::Param(_, n))) => self.use_param(n, w.clone()).is_ok(),
            (Ty::Tuple(hs), Ty::Tuple(ws), Pipe::Tuple(ps)) if hs.len() == ws.len() => ps.iter().zip(ws.iter()).all(|((q, h), w)| self.fill_holes(q, h, w)),
            _ => have == want,
        }
    }

    /// Whether the tuple `p` gives reads the input of the step: one of its positions does.
    pub(crate) fn tuple_reads(&self, p: &Pipe) -> bool {
        match p {
            Pipe::Tuple(ps) => ps.iter().any(|(q, t)| match t {
                Ty::Num => self.input_ty(q).is_some(),
                Ty::Group => !starts_with_value(q),
                Ty::Text => matches!(q, Pipe::App(_, a) if a.is_empty()),
                Ty::Tuple(_) => self.tuple_reads(q),
                _ => matches!(q, Pipe::Index(..)) && self.tuple_reads(q),
            }),
            Pipe::Index(t, _) => self.tuple_reads(t),
            Pipe::App(Fun::Def(c), args) => c.def.step && args.len() <= c.def.params.len(),
            Pipe::Seq(ps) => !ps.first().is_some_and(starts_with_value),
            _ => false,
        }
    }
}

/// The body `p` of a definition with the parameters written alone in positions of its tuples
/// (`holes`) read by the types `params` now have: each such position read as a parameter of
/// that type, and the types of the tuples and of the variables bound to them made again.
pub(crate) fn fill(p: &Pipe, params: &[super::infer::ParamUse], bound: &mut Vec<(String, Ty)>) -> Pipe {
    let all = |ps: &[Pipe], bound: &mut Vec<(String, Ty)>| ps.iter().map(|q| fill(q, params, bound)).collect::<Vec<_>>();
    match p {
        Pipe::Tuple(ps) => Pipe::Tuple(
            ps.iter()
                .map(|(q, t)| match (t, q) {
                    (Ty::Any, Pipe::Var(Slot::Param(i, n))) => {
                        let ty = params[*i].ty.clone().unwrap_or(Ty::Any);
                        let read = match &ty {
                            Ty::Group | Ty::Term => group(n.clone()),
                            t @ Ty::Tuple(_) => Pipe::Var(Slot::Local(n.clone(), Holds::Tuple(Box::new(t.clone())))),
                            _ => q.clone(),
                        };
                        let ty = if ty == Ty::Term { Ty::Group } else { ty };
                        (read, ty)
                    }
                    (t, q) => {
                        let q = fill(q, params, bound);
                        let t = match t {
                            Ty::Tuple(_) => value_ty(&q).unwrap_or_else(|| t.clone()),
                            t => t.clone(),
                        };
                        (q, t)
                    }
                })
                .collect(),
        ),
        Pipe::Seq(ps) => Pipe::Seq(all(ps, bound)),
        Pipe::App(f, args) => Pipe::App(f.clone(), all(args, bound).into()),
        Pipe::Bind(Slot::Local(n, Holds::Tuple(t)), q) => {
            let q = fill(q, params, bound);
            let t = value_ty(&q).unwrap_or_else(|| (**t).clone());
            bound.push((n.clone(), t.clone()));
            Pipe::Bind(Slot::Local(n.clone(), Holds::Tuple(Box::new(t))), Arc::new(q))
        }
        Pipe::Var(Slot::Local(n, Holds::Tuple(t))) => {
            let t = bound.iter().rev().find(|(m, _)| m == n).map_or_else(|| (**t).clone(), |(_, t)| t.clone());
            Pipe::Var(Slot::Local(n.clone(), Holds::Tuple(Box::new(t))))
        }
        Pipe::Bind(x, q) => Pipe::Bind(x.clone(), Arc::new(fill(q, params, bound))),
        Pipe::Index(q, i) => Pipe::Index(Arc::new(fill(q, params, bound)), *i),
        Pipe::Unpack(x, q) => Pipe::Unpack(x.clone(), Arc::new(fill(q, params, bound))),
        Pipe::Expanded(m) => Pipe::Expanded(Box::new(super::ast::Expanded { args: all(&m.args, bound), steps: all(&m.steps, bound), ..(**m).clone() })),
        Pipe::FnValue(q) => Pipe::FnValue(Arc::new(fill(q, params, bound))),
        Pipe::Num(_) | Pipe::Name(_) | Pipe::Text(_) | Pipe::Var(_) => p.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::lang::defs::{show_def, sig_of};
    use crate::passes::Passes;

    #[test]
    fn tuples_print_back_as_written() {
        let spec = "(def (mk n) (n + 1, (lowbits | unshift), n)) (def (swap t:(num, num)) ((index 1 t), (index 0 t))) (def (f) u = (swap (2, 3)) | (a, b) = u | (if (a > b) ((mk a) | (index 1)))) prepass=f";
        let p = Passes::parse(spec).unwrap();
        let shown: Vec<String> = p.defs[p.defs.len() - 3..].iter().map(|d| format!("{} {}", sig_of(d), show_def(d))).collect();
        assert_eq!(
            shown,
            [
                "(mk n:num g:group) (num, group, num) (def (mk n) (n + 1, (lowbits | unshift), n))",
                "(swap t:(num, num)) (num, num) (def (swap t:(num, num)) ((index 1 t), (index 0 t)))",
                "(f g:group) group (def (f) u = (swap (2, 3)) | (a, b) = u | (if (a > b) ((mk a) | (index 1))))",
            ]
        );
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "tuples are written back as read");
    }

    #[test]
    fn steps_that_pass_a_tuple_on_print_back_as_written() {
        let spec = "(def (mk n) (n + 1, n)) (def (swap t:(num, num)) ((index 1 t), (index 0 t))) (def (f a) (mk a) | (print \"made\" a) | k = a * 2 | swap | (print k)) (def (g) x = ((mk 1) | (print 1) | (index 0)) + 1 | (print (index 1 ((2, 3) | (print x))))) prepass=g";
        let p = Passes::parse(spec).unwrap();
        let shown: Vec<String> = p.defs[p.defs.len() - 2..].iter().map(|d| show_def(d)).collect();
        assert_eq!(shown, ["(def (f a) (mk a) | (print \"made\" a) | k = a * 2 | swap | (print k))", "(def (g) x = ((mk 1) | (print 1) | (index 0)) + 1 | (print (index 1 ((2, 3) | (print x)))))"]);
        assert_eq!(Passes::parse(&p.to_string()).unwrap(), p, "the joints are written back as read");
    }
}
