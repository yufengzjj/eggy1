//! Tuples in the parser (`docs/lang/tuples.md`): `(a, b, ...)`, told from a call by its
//! commas; `(index i t)` of a tuple, whose position `i` is a number written out so that its
//! type is known when read; `(a, b) = t`; and a step that gives a tuple followed by one that
//! takes it.

use super::ast::{Fun, Holds, Pipe, Slot, gives_tuple, input_of, passes_on, show, show_expr, show_tuple_input, stage, starts_with_value, value_ty};
use super::builtins::get;
use super::defs::def_sig;
use super::lexer::{Tok, show_tok};
use super::parser::{Parser, Rhs, group, seq_of};
use super::types::Ty;
use super::vars::var_index;
use std::sync::Arc;

impl<'a> Parser<'a> {
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

    /// The offset of the `)` that closes the `(` `k` tokens ahead.
    fn close_of(&self, k: usize) -> Option<usize> {
        let mut depth = 0;
        for (j, t) in self.toks.get(self.at + k..)?.iter().enumerate() {
            match t {
                Tok::Open => depth += 1,
                Tok::Close if depth == 1 => return Some(k + j),
                Tok::Close => depth -= 1,
                _ => {}
            }
        }
        None
    }

    /// Whether a tuple `(a, b, ...)` starts `k` tokens ahead: a `(` with a `,` inside it, not
    /// inside deeper parentheses.
    pub(crate) fn tuple_literal_at(&self, k: usize) -> bool {
        if self.peek_at(k) != Some(&Tok::Open) {
            return false;
        }
        let mut depth = 0;
        for t in &self.toks[self.at + k..] {
            match t {
                Tok::Open => depth += 1,
                Tok::Close if depth == 1 => return false,
                Tok::Close => depth -= 1,
                Tok::Comma if depth == 1 => return true,
                _ => {}
            }
        }
        false
    }

    /// The offset past the expression argument `k` tokens ahead.
    fn skip_arg(&self, k: usize) -> usize {
        match self.peek_at(k) {
            Some(Tok::Not) => self.skip_arg(k + 1),
            Some(Tok::Open) => self.close_of(k).map_or(k, |c| c + 1),
            Some(_) => k + 1,
            None => k,
        }
    }

    /// Whether a term that gives a tuple starts `k` tokens ahead: a tuple, a variable or
    /// parameter that holds one, a call of a function that gives one, `(index i t)` of a tuple
    /// (which may give any type), or a pipeline in parentheses that gives one.
    pub(crate) fn tuple_term_at(&self, k: usize) -> bool {
        match self.peek_at(k) {
            Some(Tok::Name(n)) => self.tuple_var(n).is_some() || self.tuple_def(n) && self.defs[n].params.is_empty() && (self.input || self.defs[n].def.as_ref().is_some_and(|d| !d.step)),
            Some(Tok::Open) => self.tuple_literal_at(k) || matches!(self.peek_at(k + 1), Some(Tok::Name(n)) if self.tuple_def(n)) || self.tuple_index_at(k) || self.paren_tuple_at(k),
            _ => false,
        }
    }

    /// A parser of the same text and names, at `k` tokens ahead.
    fn trial(&self, k: usize) -> Parser<'a> {
        let mut p = Parser::new(self.toks.clone(), self.defs);
        p.at = self.at + k;
        (p.params, p.groups, p.fns, p.locals, p.tuples) = (self.params.clone(), self.groups.clone(), self.fns.clone(), self.locals.clone(), self.tuples.clone());
        p
    }

    /// Whether a pipeline in parentheses that gives a tuple starts `k` tokens ahead
    /// (`((mk 3) | (print "x"))`): read on trial where it has a `|` and names something that
    /// may give a tuple.
    fn paren_tuple_at(&self, k: usize) -> bool {
        let Some(c) = self.close_of(k) else { return false };
        let inner = &self.toks[self.at + k + 1..self.at + c];
        let mut depth = 0;
        let bar = inner.iter().any(|t| {
            match t {
                Tok::Open => depth += 1,
                Tok::Close => depth -= 1,
                _ => {}
            }
            depth == 0 && *t == Tok::Bar
        });
        let tuple_name = |n: &str| self.tuple_var(n).is_some() || self.tuple_def(n) || get(n).is_some_and(|s| s.result.positions().is_some());
        if !bar || !inner.iter().any(|t| matches!(t, Tok::Comma) || matches!(t, Tok::Name(n) if tuple_name(n))) {
            return false;
        }
        let mut p = self.trial(k + 1);
        matches!(p.stages_of_pipe(), Ok((stages, None)) if p.peek() == Some(&Tok::Close) && stages.iter().rev().find(|q| !passes_on(q)).is_some_and(gives_tuple))
    }

    /// Whether `(index i t)` of a tuple `t` starts `k` tokens ahead.
    pub(crate) fn tuple_index_at(&self, k: usize) -> bool {
        self.peek_at(k) == Some(&Tok::Open) && matches!(self.peek_at(k + 1), Some(Tok::Name(n)) if n == "index" && self.param(n).is_none()) && self.tuple_term_at(self.skip_arg(k + 2))
    }

    /// The type of the position `(index i t)` `k` tokens ahead gives, where `t` is a tuple.
    pub(crate) fn index_ty_at(&self, k: usize) -> Option<Ty> {
        if !self.tuple_index_at(k) {
            return None;
        }
        self.trial(k).index_tuple().ok().map(|(_, t)| t)
    }

    /// Whether an expression of the tuple kind starts after the `(`s `k` counts: `(index i t)`
    /// of a tuple whose position `i` is a number.
    pub(crate) fn number_index_at(&self, k: usize) -> bool {
        k > 0 && self.index_ty_at(k - 1) == Some(Ty::Num)
    }

    /// `(index i t)` of a tuple `t`, and the type of its position `i`.
    pub(crate) fn index_tuple(&mut self) -> Result<(Pipe, Ty), String> {
        self.expect(Tok::Open, "(")?;
        self.at += 1;
        let i = match self.peek() {
            Some(Tok::Num(i)) => {
                let i = *i;
                self.at += 1;
                i
            }
            _ => {
                let e = self.arg()?;
                let (t, ty) = self.tuple_term()?;
                let t = show_tuple_input(&t);
                return Err(format!("(index {} {t}): a position of a tuple is a number written out, as in (index 0 {t}), since each position has its own type ({t} is {ty})", show_expr(&e, 7)));
            }
        };
        let (t, _) = self.tuple_term()?;
        self.expect(Tok::Close, ")")?;
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

    /// A term that gives a tuple, as `tuple_term_at` finds one, and the tuple's type.
    pub(crate) fn tuple_term(&mut self) -> Result<(Pipe, Ty), String> {
        self.tuple_term_for(None)
    }

    /// `tuple_term` where a tuple of type `want` is taken, which a tuple written out reads its
    /// positions by.
    fn tuple_term_for(&mut self, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        match self.peek().cloned() {
            Some(Tok::Name(n)) if self.tuple_var(&n).is_some() => {
                let ty = self.tuple_var(&n).unwrap();
                self.at += 1;
                self.use_param(&n, ty.clone())?;
                Ok((Pipe::Var(Slot::Local(n, Holds::Tuple(Box::new(ty.clone())))), ty))
            }
            Some(Tok::Name(n)) if self.tuple_term_at(0) => {
                self.at += 1;
                self.used.push(n.clone());
                let p = self.defs[&n].pipe.clone();
                let ty = value_ty(&p).expect("a call of a function that gives a tuple");
                Ok((p, ty))
            }
            Some(Tok::Open) if self.tuple_literal_at(0) => self.tuple_literal(want),
            Some(Tok::Open) if self.tuple_index_at(0) => {
                let (p, ty) = self.index_tuple()?;
                match ty.positions() {
                    Some(_) => Ok((p, ty)),
                    None => Err(format!("{} gives {ty}, not a tuple", show(&p))),
                }
            }
            Some(Tok::Open) if self.paren_tuple_at(0) => {
                self.at += 1;
                let (stages, _) = self.stages_of_pipe()?;
                self.expect(Tok::Close, ")")?;
                let p = seq_of(stages);
                let ty = value_ty(&p).expect("a pipeline that gives a tuple");
                Ok((p, ty))
            }
            Some(Tok::Open) if self.tuple_term_at(0) => {
                let Some(Tok::Name(n)) = self.peek_at(1).cloned() else { unreachable!("a call is ahead") };
                self.at += 2;
                let p = self.def_call(&n)?;
                self.expect(Tok::Close, ")")?;
                let ty = value_ty(&p).expect("a call of a function that gives a tuple");
                Ok((p, ty))
            }
            t => Err(format!("expected a tuple, as in (1, t), a variable that holds one or a call of a function that gives one; found {}", show_tok(t.as_ref()))),
        }
    }

    /// `(a, b, ...)`: each position read as `position` reads it, where a tuple of type `want`
    /// is taken by the type of that position.
    pub(crate) fn tuple_literal(&mut self, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        self.expect(Tok::Open, "(")?;
        let mut ps = Vec::new();
        loop {
            let at = want.and_then(Ty::positions).and_then(|ts| ts.get(ps.len()));
            ps.push(self.position(at)?);
            match self.next() {
                Some(Tok::Comma) => {}
                Some(Tok::Close) => break,
                x => return Err(format!("expected , or ) in a tuple, found {}", show_tok(x.as_ref()))),
            }
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
    fn position(&mut self, want: Option<&Ty>) -> Result<(Pipe, Ty), String> {
        let alone = matches!(self.peek_at(1), Some(Tok::Comma | Tok::Close));
        let out = match self.peek().cloned() {
            Some(Tok::Name(n)) if self.peek_at(1) == Some(&Tok::Assign) => return Err(format!("a position of a tuple is a value, not an assignment: {n} = ...")),
            Some(Tok::Name(n)) if alone && let Some(s) = self.bare_fn(&n) => match want.filter(|w| w.is_function()) {
                None if self.input || s.input.is_none() => match s.result {
                    Ty::Num => (self.or()?, Ty::Num),
                    Ty::Text => (self.text_value()?, Ty::Text),
                    _ => (self.stage()?, Ty::Group),
                },
                w => {
                    let ty = w.cloned().unwrap_or_else(|| {
                        let input = if s.input.as_ref().is_some_and(|i| i.ty == Ty::Group) { Ty::Group } else { Ty::Term };
                        Ty::Fn(Box::new(input), Box::new(s.result.clone()))
                    });
                    let outer = std::mem::replace(&mut self.input, true);
                    let f = self.fn_rhs("a position", &ty.to_string(), &ty);
                    self.input = outer;
                    (f?, ty)
                }
            },
            Some(Tok::Str(t)) => {
                self.at += 1;
                (Pipe::Text(t), Ty::Text)
            }
            _ if self.text_ahead() => (self.text_value()?, Ty::Text),
            _ if self.tuple_index_at(0) && self.index_ty_at(0) == Some(Ty::Num) => (self.or()?, Ty::Num),
            _ if self.tuple_index_at(0) => self.index_tuple()?,
            _ if self.tuple_term_at(0) => self.tuple_term_for(want.filter(|w| w.positions().is_some()))?,
            Some(Tok::Name(n)) if alone && self.param(&n).is_none() && self.fn_var(&n).is_some() => {
                self.at += 1;
                let f = self.fn_read(n);
                let Pipe::Var(Slot::Local(_, Holds::Fn(t))) = &f else { unreachable!("a function variable read") };
                let t = t.clone();
                (f, t)
            }
            Some(Tok::Name(n)) if alone && self.param(&n).is_some_and(|i| self.params[i].ty.as_ref().is_some_and(Ty::is_function)) => {
                self.at += 1;
                let i = self.param(&n).unwrap();
                self.count_param(&n);
                (Pipe::Var(Slot::Param(i, n)), self.params[i].ty.clone().unwrap())
            }
            Some(Tok::Name(n)) if alone && self.group_value(&n) => {
                self.at += 1;
                self.use_param(&n, Ty::Group)?;
                (group(n), Ty::Group)
            }
            Some(Tok::Name(n)) if alone && self.param(&n).is_none() && self.unknown(&n) && self.local_kind(&n).is_none() => {
                self.at += 1;
                self.group_name(&n)?;
                (group(n), Ty::Group)
            }
            Some(Tok::Name(n)) if alone && self.param(&n).is_some_and(|i| self.params[i].ty.is_none()) => {
                self.at += 1;
                self.count_param(&n);
                self.holes.push(n.clone());
                (Pipe::Var(Slot::Param(self.param(&n).unwrap(), n)), Ty::Any)
            }
            _ if self.number_ahead(true) => (self.or()?, Ty::Num),
            _ => match self.rhs_group(true, false)? {
                Rhs::Num(e) => (e, Ty::Num),
                Rhs::Group(p) if gives_tuple(&p) => {
                    let t = value_ty(&p).unwrap();
                    (p, t)
                }
                Rhs::Group(p) => (p, Ty::Group),
            },
        };
        if self.peek() == Some(&Tok::Bar) {
            return Err(format!("a position of a tuple is one value or step: write a pipeline in parentheses, as in (({} | ...), 1)", stage(&out.0)));
        }
        Ok(out)
    }

    /// What kind of local variable `n` is bound as so far in the text.
    pub(crate) fn local_kind(&self, n: &str) -> Option<&'static str> {
        if self.groups.iter().any(|g| g == n) {
            Some("group")
        } else if self.locals.iter().any(|l| l == n) {
            Some("number")
        } else if self.fn_var(n).is_some() {
            Some("function")
        } else if self.tuples.iter().any(|(t, _)| t == n) {
            Some("tuple")
        } else {
            None
        }
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

    /// Whether a destructuring `(a, b, ...) = ...` is ahead.
    pub(crate) fn unpack_ahead(&self) -> bool {
        self.tuple_literal_at(0) && self.close_of(0).is_some_and(|c| self.peek_at(c + 1) == Some(&Tok::Assign))
    }

    /// `(a, b, ...) = t`: each name bound to its position of the tuple `t`, as a local
    /// variable of the kind the position's type says.
    pub(crate) fn unpack(&mut self) -> Result<Pipe, String> {
        self.expect(Tok::Open, "(")?;
        let mut names: Vec<String> = Vec::new();
        loop {
            let n = self.name("a name in (a, b, ...) = ...")?;
            if names.contains(&n) {
                return Err(format!("{n} is written twice in ({}, {n}, ...) = ...", names.join(", ")));
            }
            names.push(n);
            match self.next() {
                Some(Tok::Comma) => {}
                Some(Tok::Close) => break,
                x => return Err(format!("expected , or ) in ({}, ...) = ..., found {}", names.join(", "), show_tok(x.as_ref()))),
            }
        }
        let lhs = format!("({})", names.join(", "));
        self.expect(Tok::Assign, &format!("= after {lhs}"))?;
        if !self.tuple_term_at(0) {
            return Err(format!("{lhs} = ... takes a tuple, as in {lhs} = (1, t), a variable that holds one or a call of a function that gives one; found {}", show_tok(self.peek())));
        }
        let (e, ty) = self.tuple_term()?;
        self.no_assign()?;
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
                Holds::Num if !self.locals.contains(n) => self.locals.push(n.clone()),
                Holds::Group if !self.groups.contains(n) => self.groups.push(n.clone()),
                Holds::Fn(t) => self.fns.push((n.clone(), t.clone())),
                Holds::Tuple(t) => self.tuples.push((n.clone(), (**t).clone())),
                _ => {}
            }
            slots.push(Slot::Local(n.clone(), holds));
        }
        Ok(Pipe::Unpack(slots.into(), Arc::new(e)))
    }

    /// The argument for the parameter of type `want` (a tuple) of a call; `whose` names it.
    pub(crate) fn tuple_arg(&mut self, want: &Ty, whose: &dyn Fn() -> String) -> Result<Pipe, String> {
        if let Some(Tok::Name(n)) = self.peek().cloned()
            && self.param(&n).is_some_and(|i| self.params[i].ty.is_none())
        {
            self.at += 1;
            self.use_param(&n, want.clone())?;
            return Ok(Pipe::Var(Slot::Local(n, Holds::Tuple(Box::new(want.clone())))));
        }
        if !self.tuple_term_at(0) {
            return Err(format!("{}; found {}", whose(), show_tok(self.peek())));
        }
        let (e, ty) = self.tuple_term_for(Some(want))?;
        if ty != *want && !self.fill_holes(&e, &ty, want) {
            return Err(format!("{}; {} is {ty}", whose(), show_tuple_input(&e)));
        }
        Ok(e)
    }

    /// The step after `| ` that takes the tuple of type `ty` the step `origin` gives, without
    /// the tuple, which the run puts in: `(index i)`, which takes its position `i`, or a call
    /// of a function whose last parameter takes that tuple; and the type it gives.
    pub(crate) fn tuple_taker(&mut self, origin: &Pipe, ty: &Ty) -> Result<(Pipe, Ty), String> {
        let shown = stage(origin);
        if self.peek() == Some(&Tok::Open) && matches!(self.peek_at(1), Some(Tok::Name(n)) if n == "index" && self.param(n).is_none()) {
            let end = self.skip_arg(2);
            if self.peek_at(end) == Some(&Tok::Close) {
                let Some(Tok::Num(i)) = self.peek_at(2).cloned() else {
                    self.at += 2;
                    let e = self.arg()?;
                    return Err(format!("{shown} | (index {}): a position of a tuple is a number written out, as in (index 0), since each position has its own type ({shown} is {ty})", show_expr(&e, 7)));
                };
                self.at += 4;
                return self.index_of(input_of(ty.clone()), i, &shown);
            }
        }
        let (open, n) = match (self.peek().cloned(), self.peek_at(1).cloned()) {
            (Some(Tok::Name(n)), _) => (false, n),
            (Some(Tok::Open), Some(Tok::Name(n))) => (true, n),
            _ => (false, String::new()),
        };
        let takes = self.param(&n).is_none().then(|| self.defs.get(&n)).flatten().and_then(|d| d.def.clone()).filter(|d| d.params.last().is_some_and(|p| p.ty.positions().is_some()));
        let Some(d) = takes else { return Err(format!("{shown} gives {ty}; {}", self.takes_ahead())) };
        let last = d.params.last().unwrap();
        if last.ty != *ty && !self.fill_holes(origin, ty, &last.ty) {
            return Err(format!("{n} takes {last}: {}; {shown} gives {ty}", super::defs::sig_of(&d)));
        }
        self.at += 1 + usize::from(open);
        let rest = def_sig(&n, &d.params[..d.params.len() - 1]);
        let args = match open && !rest.params.is_empty() {
            true => self.args(&rest, true)?,
            false => Vec::new(),
        };
        if open {
            self.expect(Tok::Close, ")")?;
        }
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

    /// A type written after `:`: a name, a tuple type `(A, B, ...)`, or `A->B`.
    pub(crate) fn type_text(&mut self) -> Result<String, String> {
        let mut t = self.type_atom("a type after :")?;
        while self.peek() == Some(&Tok::Arrow) {
            self.at += 1;
            t = format!("{t}->{}", self.type_atom("a type after ->")?);
        }
        Ok(t)
    }

    fn type_atom(&mut self, what: &str) -> Result<String, String> {
        if self.peek() != Some(&Tok::Open) {
            return self.name(what);
        }
        self.at += 1;
        let mut ts = vec![self.type_text()?];
        while self.peek() == Some(&Tok::Comma) {
            self.at += 1;
            ts.push(self.type_text()?);
        }
        self.expect(Tok::Close, ") after a tuple type")?;
        Ok(format!("({})", ts.join(", ")))
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
