//! The types of the parameters of a `def` that has none written, inferred from its body alone:
//! the parser records each use whose position fixes a type (`ParamUse`), and the flow check
//! (`flow`) walked over the body joins those with what each step gives and the next takes;
//! each parameter gets one type, or the error of uses that disagree or of none that fixes it.

use super::ast::{Pipe, show_stage};
use super::flow::{Flow, expr, step};
use super::parser::Parser;
use super::types::{Param, Ty};

/// A parameter of the function whose body is read, and the type the uses read so far give it.
#[derive(Clone)]
pub(crate) struct ParamUse {
    pub(crate) name: String,
    pub(crate) ty: Option<Ty>,
    pub(crate) annotated: bool,
    pub(crate) uses: usize,
}

impl<'a> Parser<'a> {
    pub(crate) fn param(&self, n: &str) -> Option<usize> {
        self.params.iter().position(|p| p.name == n)
    }

    /// Records a use of `n` as `ty` where `n` is a parameter; an error where an earlier use
    /// gave it another type.
    pub(crate) fn use_param(&mut self, n: &str, ty: Ty) -> Result<(), String> {
        let Some(i) = self.param(n) else { return Ok(()) };
        let p = &mut self.params[i];
        p.uses += 1;
        match &p.ty {
            Some(t) if *t == ty || matches!(t, Ty::Fn(..)) && t.fits(&ty) => Ok(()),
            // A term is read where a group value is, as the group of it.
            Some(Ty::Term) if ty == Ty::Group => Ok(()),
            Some(t) if p.annotated && matches!(t, Ty::Fn(..)) && !t.is_pipe() => Err(format!("parameter {n}:{t} is used where {ty} is wanted")),
            Some(t) if t.what() == ty.what() || matches!(t, Ty::Fn(..)) && !t.is_pipe() => Err(format!("parameter {n} is used as {t} and as {ty}")),
            Some(t) => Err(format!("parameter {n} is used as {} and as {}", t.what(), ty.what())),
            None => {
                p.ty = Some(ty);
                Ok(())
            }
        }
    }

    /// Records `n` written as a step: one with a type must fit a pipeline; one without gets
    /// its type from the flow of the body (`solve`).
    pub(crate) fn step_param(&mut self, n: &str) -> Result<(), String> {
        match self.param(n).and_then(|i| self.params[i].ty.clone()) {
            Some(_) => self.use_param(n, Ty::pipe()),
            None => {
                self.count_param(n);
                Ok(())
            }
        }
    }

    /// Counts a use of the parameter `n` whose type the flow of the body gives.
    pub(crate) fn count_param(&mut self, n: &str) {
        if let Some(i) = self.param(n) {
            self.params[i].uses += 1;
        }
    }
}

/// A type while it is inferred: a type variable, a type, or a function of two.
#[derive(Clone, Debug)]
enum It {
    Var(usize),
    Ty(Ty),
    Fn(Box<It>, Box<It>),
}

impl It {
    fn of(t: &Ty) -> It {
        match t {
            Ty::Fn(a, b) => It::Fn(Box::new(It::of(a)), Box::new(It::of(b))),
            Ty::MaybeTerm => It::Ty(Ty::Term),
            t => It::Ty(t.clone()),
        }
    }
}

/// The types of the parameters of one body and what is known of them: inferring, or checking
/// a body whose parameters have their types.
pub(crate) struct Infer {
    vars: Vec<Option<It>>,
    /// The parameter each variable belongs to, for errors.
    owner: Vec<usize>,
    params: Vec<It>,
    names: Vec<String>,
    /// The parameters read as values (a group or a term), by name.
    values: Vec<(String, usize)>,
    solving: bool,
    /// While only the positions that take one type exactly (arguments) are read, before the
    /// joints between steps, which also join a group and a term.
    exact: bool,
}

impl Infer {
    /// For a pipeline outside any function.
    pub(crate) fn none() -> Infer {
        Infer { vars: Vec::new(), owner: Vec::new(), params: Vec::new(), names: Vec::new(), values: Vec::new(), solving: false, exact: false }
    }

    /// For checking the body of a function with parameters `params`, the input parameter
    /// `input` and the implicit input `implicit`.
    pub(crate) fn of_params(params: &[Param], input: Option<&str>, implicit: Option<&Ty>) -> Infer {
        let mut cx = Infer::none();
        for p in params {
            cx.add(&p.name, It::of(&p.ty), matches!(p.ty, Ty::Group | Ty::Term));
        }
        if let Some(g) = input {
            cx.add(g, It::Ty(if implicit == Some(&Ty::Term) { Ty::Term } else { Ty::Group }), true);
        }
        cx
    }

    fn add(&mut self, name: &str, t: It, value: bool) {
        if value {
            self.values.push((name.to_string(), self.params.len()));
        }
        self.params.push(t);
        self.names.push(name.to_string());
    }

    fn fresh(&mut self, owner: usize) -> It {
        self.vars.push(None);
        self.owner.push(owner);
        It::Var(self.vars.len() - 1)
    }

    fn resolve(&self, t: &It) -> It {
        match t {
            It::Var(k) => match &self.vars[*k] {
                Some(u) => self.resolve(u),
                None => t.clone(),
            },
            t => t.clone(),
        }
    }

    /// `t` with its variables bound written out, `?` for those that are not.
    fn show(&self, t: &It) -> String {
        match self.resolve(t) {
            It::Var(_) => "?".into(),
            It::Ty(t) => t.to_string(),
            It::Fn(a, b) if matches!(self.resolve(&a), It::Fn(..)) => format!("({})->{}", self.show(&a), self.show(&b)),
            It::Fn(a, b) => match (self.resolve(&a), self.resolve(&b)) {
                (It::Ty(Ty::Group), It::Ty(Ty::Group)) => "pipe".into(),
                _ => format!("{}->{}", self.show(&a), self.show(&b)),
            },
        }
    }

    fn unify(&mut self, a: &It, b: &It) -> bool {
        match (self.resolve(a), self.resolve(b)) {
            (It::Var(x), It::Var(y)) if x == y => true,
            (It::Var(x), t) | (t, It::Var(x)) => {
                self.vars[x] = Some(t);
                true
            }
            (It::Ty(x), It::Ty(y)) => x == y,
            (It::Fn(a, b), It::Fn(c, d)) => self.unify(&a, &c) && self.unify(&b, &d),
            _ => false,
        }
    }

    fn flow_of(&self, t: &It) -> Flow {
        match self.resolve(t) {
            It::Var(k) => Flow::Var(k),
            It::Ty(Ty::Group) => Flow::Group,
            It::Ty(Ty::Term) => Flow::One,
            It::Ty(Ty::Num) => Flow::Num,
            It::Ty(Ty::Text) => Flow::Text,
            _ => Flow::Unknown,
        }
    }

    fn it_of(f: Flow) -> Option<It> {
        Some(match f {
            Flow::Var(k) => It::Var(k),
            Flow::Group => It::Ty(Ty::Group),
            Flow::One => It::Ty(Ty::Term),
            Flow::Num => It::Ty(Ty::Num),
            Flow::Text => It::Ty(Ty::Text),
            Flow::Unknown => return None,
        })
    }

    /// `f` with its variable written out where it is bound.
    pub(crate) fn now(&self, f: Flow) -> Flow {
        match f {
            Flow::Var(k) => self.flow_of(&It::Var(k)),
            f => f,
        }
    }

    /// A value `given` that flows where `takes` is taken: where either is not known yet it
    /// becomes the other; else a group may go where a term is (each element) and a term where
    /// a group is. The error names the parameter whose uses disagree.
    fn link(&mut self, given: Option<It>, takes: &It) -> Result<(), String> {
        let Some(g) = given.filter(|_| !self.exact) else { return Ok(()) };
        let (gr, tr) = (self.resolve(&g), self.resolve(takes));
        let owner = match (&gr, &tr) {
            (It::Var(k), _) | (_, It::Var(k)) => self.owner[*k],
            _ => return Ok(()),
        };
        let was = self.show(&self.params[owner].clone());
        let other = if matches!(gr, It::Var(_)) { self.show(&tr) } else { self.show(&gr) };
        match self.unify(&gr, &tr) {
            true => Ok(()),
            false => Err(format!("parameter {} is used as {was} and as {other}", self.names[owner])),
        }
    }

    /// The input `given` of a step whose input is `takes`, after the joint: a value not known
    /// yet becomes `takes`.
    pub(crate) fn joint(&mut self, given: Flow, takes: &Ty) -> Result<Flow, String> {
        self.link(Infer::it_of(given), &It::of(takes))?;
        Ok(self.now(given))
    }

    /// The value a step gives, `gives`, where `takes` is taken (a pipeline argument's result,
    /// the group a group variable binds).
    pub(crate) fn result(&mut self, gives: Flow, takes: &Ty) -> Result<(), String> {
        self.link(Infer::it_of(gives), &It::of(takes))
    }

    /// What the group variable `n` read as a value gives: the type of a parameter read so.
    pub(crate) fn value(&mut self, n: &str) -> Result<Option<Flow>, String> {
        let Some(&(_, i)) = self.values.iter().find(|(m, _)| m == n) else { return Ok(None) };
        match self.resolve(&self.params[i].clone()) {
            It::Fn(..) => Err(format!("parameter {n} is used as {} and as a group or a term", self.show(&self.params[i].clone()))),
            t => Ok(Some(self.flow_of(&t))),
        }
    }

    /// What the parameter `i` gives as a step on `input`: a function from `input`, a group
    /// going where its input is a term giving each element's results.
    pub(crate) fn param_step(&mut self, i: usize, input: Flow, at: &Pipe) -> Result<Flow, String> {
        let n = self.names[i].clone();
        if self.values.iter().any(|(_, j)| *j == i) {
            return Err(format!("parameter {n} is used as a group or a term and as a step {}", show_stage(at)));
        }
        let t = self.params[i].clone();
        let (a, b) = match self.resolve(&t) {
            It::Var(_) => {
                let (a, b) = (self.fresh(i), self.fresh(i));
                let f = It::Fn(Box::new(a.clone()), Box::new(b.clone()));
                self.unify(&t, &f);
                (a, b)
            }
            It::Fn(a, b) => (*a, *b),
            It::Ty(_) => return Err(format!("parameter {n} is used as {} and as a step", self.show(&t))),
        };
        self.link(Infer::it_of(input), &a)?;
        let each = matches!(self.resolve(&a), It::Ty(Ty::Term)) && self.now(input) == Flow::Group;
        Ok(match self.flow_of(&b) {
            Flow::One if each => Flow::Group,
            f => f,
        })
    }

    /// The parameter `i` given where a function of type `t` is taken: of that type, where its
    /// uses so far leave it open.
    pub(crate) fn param_arg(&mut self, i: usize, t: &Ty) -> Result<(), String> {
        let p = self.params[i].clone();
        if let Some(have) = self.ty_of(&p) {
            return match have.fits(t) {
                true => Ok(()),
                false => Err(format!("parameter {} is used as {have} and as {t}", self.names[i])),
            };
        }
        let was = self.show(&p);
        match self.unify(&p, &It::of(t)) {
            true => Ok(()),
            false => Err(format!("parameter {} is used as {was} and as {t}", self.names[i])),
        }
    }

    fn ty_of(&self, t: &It) -> Option<Ty> {
        match self.resolve(t) {
            It::Var(_) => None,
            It::Ty(t) => Some(t),
            It::Fn(a, b) => Some(Ty::Fn(Box::new(self.ty_of(&a)?), Box::new(self.ty_of(&b)?))),
        }
    }

    /// An error of the flow check: while inferring only the types matter, so it waits for the
    /// check of the whole program.
    pub(crate) fn fail(&self, e: String) -> Result<(), String> {
        if self.solving { Ok(()) } else { Err(e) }
    }
}

/// Gives each parameter of `params` without a type the one its uses in the body give: `body`
/// (on the input, a term where `one`), or `value`, the expression the body is; `lead` the last
/// parameter where the body starts from it. Errors name the definition `what`.
pub(crate) fn solve(params: &mut [ParamUse], what: &str, name: &str, body: Option<&Pipe>, value: Option<&Pipe>, one: bool, lead: Option<&str>) -> Result<(), String> {
    let mut cx = Infer::none();
    cx.solving = true;
    for (i, p) in params.iter().enumerate() {
        let t = match &p.ty {
            Some(t) => It::of(t),
            None => cx.fresh(i),
        };
        let value = lead == Some(p.name.as_str()) || matches!(p.ty, Some(Ty::Group | Ty::Term));
        cx.add(&p.name, t, value);
    }
    let input = if one { Flow::One } else { Flow::Group };
    for exact in [true, false] {
        cx.exact = exact;
        let walked = match (body, value) {
            (_, Some(e)) => expr(&mut cx, e, input),
            (Some(b), None) => step(&mut cx, b, input).map(|_| ()),
            (None, None) => Ok(()),
        };
        walked.map_err(|e| format!("{what}: {e}"))?;
    }
    if let Some(p) = params.iter().find(|p| p.ty.is_none() && p.uses == 0) {
        return Err(format!("{what}: parameter {} is never used in the body", p.name));
    }
    for (i, p) in params.iter_mut().enumerate() {
        let t = cx.params[i].clone();
        if p.ty.is_none() {
            match cx.ty_of(&t) {
                Some(t) => p.ty = Some(t),
                None => return Err(format!("{what}: cannot infer the type of {0} in {name}: write {0}:TYPE", p.name)),
            }
        }
    }
    Ok(())
}
