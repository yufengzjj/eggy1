//! Pass scheduler for the pre-pass (`docs/pass-framework-plan.md`, step 3). Equivalent
//! nodes of a hash-consed table are merged into classes that keep a few forms each.
//! Registered passes run on new nodes: whole-form passes on forms of the root class,
//! node passes on every node. When the best form of a class changes, its parents are
//! rebuilt with the best form of each child class, so passes see the improvement
//! inside larger terms. The legacy pre-pass results are the seeds.

use crate::dag::{Node, NodeId, NodeTable};
use crate::eval::{Term as T, size};
use crate::linear_mba::Ctx;
use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

/// Scheduler settings from the command line.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Options {
    /// Run the scheduler after the legacy pre-pass.
    pub on: bool,
    /// Names of passes not to run.
    pub disable: Vec<String>,
    /// Print per-call statistics to stderr.
    pub trace: bool,
    /// Stop scheduling past this instant and return the best form so far.
    pub deadline: Option<Instant>,
}

/// Forms kept per class.
const ALTS: usize = 4;
/// Ancestor nodes made per call.
const MAX_INSTANCES: usize = 512;
/// Seeds larger than this are not scheduled; a larger input is left out of the table.
const MAX_SEED_SIZE: usize = 4000;

#[derive(Clone, Copy, PartialEq)]
enum Scope {
    /// Forms of the root class not much larger than its best form.
    Root,
    /// Every new node.
    Node,
}

struct Pass {
    name: &'static str,
    scope: Scope,
    /// Most runs per call.
    budget: usize,
    run: fn(&T, &Ctx) -> Option<T>,
}

fn changed(t: &T, r: T) -> Option<T> {
    (r != *t).then_some(r)
}

/// Registered passes, in the order they are tried on a node.
const PASSES: &[Pass] = &[
    Pass { name: "tfunc_node", scope: Scope::Node, budget: 4096, run: |t, w| crate::tfunc::replacement(t, w) },
    Pass {
        name: "rebuild",
        scope: Scope::Root,
        budget: 8,
        run: |t, w| changed(t, crate::linear_mba::cluster_regions(&crate::linear_mba::rewrite(t, w), w, false)),
    },
    Pass { name: "relate", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::linear_mba::relate(t, w)) },
    Pass { name: "tfunc", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::tfunc::simplify(t, w)) },
    Pass {
        name: "recombine",
        scope: Scope::Root,
        budget: 8,
        run: |t, w| {
            let r = crate::linear_mba::selectors(t, w).is_empty().then(|| crate::linear_mba::recombine_regions(t, w, false))?;
            changed(t, r)
        },
    },
    Pass { name: "cut_products", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::lowbits::cut_products(t, w)) },
    Pass { name: "shifted_xor", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::lowbits::shifted_xor(t, w)) },
    Pass { name: "lowbits_rebuilt", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::lowbits::simplify_rebuilt(t, w)) },
    Pass {
        name: "lowbits",
        scope: Scope::Root,
        budget: 8,
        run: |t, w| changed(t, crate::linear_mba::unshift(&crate::lowbits::simplify(t, w), w)),
    },
    Pass { name: "halve", scope: Scope::Root, budget: 8, run: |t, w| changed(t, crate::linear_mba::halve(t, w)) },
];

/// How a node entered the table, for the trace.
#[derive(Clone, Copy)]
enum Origin {
    Seed(usize),
    /// Result of pass `PASSES[i]` on a node.
    Pass(usize, NodeId),
    /// A parent rebuilt with a better child.
    Instance(NodeId),
    /// Subterm of a node of another origin.
    Inner,
}

#[derive(Default, Clone)]
struct PassStats {
    runs: usize,
    changed: usize,
    secs: f64,
}

struct Sched<'a> {
    w: &'a Ctx,
    opts: &'a Options,
    table: NodeTable,
    parents: Vec<Vec<NodeId>>,
    uf: Vec<NodeId>,
    members: HashMap<NodeId, Vec<NodeId>>,
    alts: HashMap<NodeId, Vec<NodeId>>,
    origin: Vec<Origin>,
    root: NodeId,
    memo: HashSet<(usize, NodeId)>,
    root_queue: VecDeque<NodeId>,
    node_queue: VecDeque<NodeId>,
    events: VecDeque<NodeId>,
    stats: Vec<PassStats>,
    instances: usize,
    timed_out: bool,
}

impl Sched<'_> {
    fn find(&mut self, mut c: NodeId) -> NodeId {
        while self.uf[c as usize] != c {
            let up = self.uf[self.uf[c as usize] as usize];
            self.uf[c as usize] = up;
            c = up;
        }
        c
    }

    fn rank(&self, n: NodeId) -> (u64, u64) {
        (self.table.size(n), self.table.hash(n))
    }

    fn best(&mut self, n: NodeId) -> NodeId {
        let c = self.find(n);
        self.alts[&c][0]
    }

    /// Adds `node`; a new node gets its own class and is queued for node passes.
    fn add(&mut self, node: Node, origin: Origin) -> (NodeId, bool) {
        let before = self.table.len();
        let id = self.table.add(node);
        if self.table.len() == before {
            return (id, false);
        }
        if let Node::Op(_, kids) = self.table.node(id).clone() {
            for k in kids {
                self.parents[k as usize].push(id);
            }
        }
        self.parents.push(Vec::new());
        self.uf.push(id);
        self.members.insert(id, vec![id]);
        self.alts.insert(id, vec![id]);
        self.origin.push(origin);
        self.node_queue.push_back(id);
        (id, true)
    }

    fn intern(&mut self, t: &T, origin: Origin) -> NodeId {
        let node = match t {
            T::Num(v) => Node::Num(*v),
            T::Var(v) => Node::Var(v.clone()),
            T::Op(op, a) => Node::Op(*op, a.iter().map(|x| self.intern(x, Origin::Inner)).collect()),
        };
        self.add(node, origin).0
    }

    fn union(&mut self, a: NodeId, b: NodeId) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (old_a, old_b) = (self.alts[&ra][0], self.alts[&rb][0]);
        let (keep, gone) = if self.members[&ra].len() >= self.members[&rb].len() { (ra, rb) } else { (rb, ra) };
        self.uf[gone as usize] = keep;
        let m = self.members.remove(&gone).unwrap();
        self.members.get_mut(&keep).unwrap().extend(m);
        let mut alts = self.alts.remove(&gone).unwrap();
        alts.extend(self.alts[&keep].iter().copied());
        alts.sort_by_key(|&n| self.rank(n));
        alts.dedup();
        alts.truncate(ALTS);
        let new = alts[0];
        self.alts.insert(keep, alts);
        if new != old_a || new != old_b {
            self.events.push_back(keep);
        }
    }

    /// Parents of the class of `c`, rebuilt with the best form of every child class.
    fn instantiate(&mut self, c: NodeId) {
        let c = self.find(c);
        for m in self.members[&c].clone() {
            for p in self.parents[m as usize].clone() {
                if self.instances >= MAX_INSTANCES {
                    return;
                }
                let Node::Op(op, kids) = self.table.node(p).clone() else { continue };
                let best: Vec<NodeId> = kids.iter().map(|&k| self.best(k)).collect();
                if best == kids {
                    continue;
                }
                let (q, new) = self.add(Node::Op(op, best), Origin::Instance(p));
                self.instances += new as usize;
                let root = self.find(self.root);
                let is_root = self.find(p) == root;
                self.union(p, q);
                if new && is_root {
                    self.queue_root(q);
                }
            }
        }
    }

    fn settle(&mut self) {
        while let Some(c) = self.events.pop_front() {
            self.instantiate(c);
        }
    }

    fn queue_root(&mut self, n: NodeId) {
        let b = self.best(self.root);
        if self.table.size(n) <= 2 * self.table.size(b) {
            self.root_queue.push_back(n);
        }
    }

    fn add_result(&mut self, src: NodeId, r: &T, pass: usize) {
        let before = self.table.len();
        let id = self.intern(r, Origin::Pass(pass, src));
        let root = self.find(self.root);
        let is_root = self.find(src) == root;
        // An existing node joining the root class takes this origin for the trace.
        if (id as usize) < before && is_root && self.find(id) != root {
            self.origin[id as usize] = Origin::Pass(pass, src);
        }
        self.union(src, id);
        if is_root && id as usize >= before {
            self.queue_root(id);
        }
        self.settle();
    }

    fn out_of_time(&mut self) -> bool {
        if self.opts.deadline.is_some_and(|d| Instant::now() >= d) {
            self.timed_out = true;
        }
        self.timed_out
    }

    fn try_pass(&mut self, i: usize, n: NodeId) {
        let p = &PASSES[i];
        if self.stats[i].runs >= p.budget || self.opts.disable.iter().any(|d| d == p.name) || !self.memo.insert((i, n)) {
            return;
        }
        let t = self.table.term(n);
        let start = Instant::now();
        let r = (p.run)(&t, self.w);
        self.stats[i].runs += 1;
        self.stats[i].secs += start.elapsed().as_secs_f64();
        if let Some(r) = r {
            check(&t, &r, self.w, p.name);
            self.stats[i].changed += 1;
            self.add_result(n, &r, i);
        }
    }

    fn run(&mut self) {
        while !self.out_of_time() {
            if let Some(n) = self.node_queue.pop_front() {
                for i in (0..PASSES.len()).filter(|&i| PASSES[i].scope == Scope::Node) {
                    self.try_pass(i, n);
                }
                continue;
            }
            let Some(n) = self.root_queue.pop_front() else { break };
            for i in (0..PASSES.len()).filter(|&i| PASSES[i].scope == Scope::Root) {
                self.try_pass(i, n);
            }
        }
    }

    /// The passes that made `n`, oldest first.
    fn chain(&self, mut n: NodeId) -> String {
        let mut steps = Vec::new();
        for _ in 0..64 {
            match self.origin[n as usize] {
                Origin::Seed(usize::MAX) => {
                    steps.push("input".to_string());
                    break;
                }
                Origin::Seed(i) => {
                    steps.push(format!("legacy{i}"));
                    break;
                }
                Origin::Pass(p, src) => {
                    steps.push(PASSES[p].name.to_string());
                    n = src;
                }
                Origin::Instance(p) => {
                    steps.push("instance".to_string());
                    n = p;
                }
                Origin::Inner => {
                    steps.push("inner".to_string());
                    break;
                }
            }
        }
        steps.reverse();
        steps.join(">")
    }
}

/// Random-evaluation check of a pass result in debug builds.
fn check(a: &T, b: &T, w: &Ctx, name: &str) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut vars = crate::eval::vars(a);
    for v in crate::eval::vars(b) {
        if !vars.contains(&v) {
            vars.push(v);
        }
    }
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    let mut s = 0x9e3779b97f4a7c15u64;
    for _ in 0..16 {
        let vals: Vec<u64> = vars
            .iter()
            .map(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                s
            })
            .collect();
        let env = |v: &str| vals[vars.iter().position(|n| n == v).unwrap()];
        let (x, y) = (crate::eval::eval(a, ty, &env), crate::eval::eval(b, ty, &env));
        if x.is_some() && y.is_some() {
            assert_eq!(x, y, "pass {name} changed the value of {}", crate::eval::show(a));
        }
    }
}

/// Statistics of the last `schedule` call on this thread, for `examples/sched_probe.rs`.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub legacy: usize,
    pub best: usize,
    pub from: String,
    pub nodes: usize,
    pub instances: usize,
    pub secs: f64,
}

thread_local! {
    static LAST: std::cell::RefCell<Option<Stats>> = const { std::cell::RefCell::new(None) };
    static USED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Records that a scheduled form replaced the legacy pre-pass result.
pub(crate) fn mark_used() {
    USED.with(|c| c.set(true));
}

/// Whether a scheduled form replaced a legacy result since the last call.
pub(crate) fn take_used() -> bool {
    USED.with(|c| c.replace(false))
}

/// Takes the statistics of the last `schedule` call on this thread.
pub fn take_stats() -> Option<Stats> {
    LAST.with(|c| c.borrow_mut().take())
}

/// Forms of the input equal to it, smallest first, found by the passes starting from the
/// input and the legacy rebuilds `seeds`. Empty when the scheduler is off or skipped.
pub(crate) fn schedule(input: &T, seeds: &[T], w: &Ctx, opts: &Options) -> Vec<T> {
    if !opts.on || seeds.is_empty() || seeds.iter().any(|t| size(t) > MAX_SEED_SIZE) {
        return Vec::new();
    }
    let start = Instant::now();
    let mut s = Sched {
        w,
        opts,
        table: NodeTable::new(),
        parents: Vec::new(),
        uf: Vec::new(),
        members: HashMap::new(),
        alts: HashMap::new(),
        origin: Vec::new(),
        root: 0,
        memo: HashSet::new(),
        root_queue: VecDeque::new(),
        node_queue: VecDeque::new(),
        events: VecDeque::new(),
        stats: vec![PassStats::default(); PASSES.len()],
        instances: 0,
        timed_out: false,
    };
    if size(input) <= MAX_SEED_SIZE {
        s.root = s.intern(input, Origin::Seed(usize::MAX));
        s.origin[s.root as usize] = Origin::Seed(usize::MAX);
    } else {
        s.root = s.intern(&seeds[0], Origin::Seed(0));
    }
    for (i, t) in seeds.iter().enumerate() {
        let id = s.intern(t, Origin::Seed(i));
        s.union(s.root, id);
    }
    s.settle();
    let root = s.find(s.root);
    s.root_queue.extend(s.alts[&root].clone());
    s.run();
    let root = s.find(s.root);
    let alts = s.alts[&root].clone();
    let b = alts[0];
    let stats = Stats {
        legacy: seeds.iter().map(size).min().unwrap_or_else(|| size(input)),
        best: s.table.size(b) as usize,
        from: s.chain(b),
        nodes: s.table.len(),
        instances: s.instances,
        secs: start.elapsed().as_secs_f64(),
    };
    if opts.trace {
        eprintln!(
            "sched: legacy {} best {} from {} nodes {} instances {} {:.3}s{}",
            stats.legacy,
            stats.best,
            stats.from,
            stats.nodes,
            stats.instances,
            stats.secs,
            if s.timed_out { " (time limit)" } else { "" }
        );
        for (p, st) in PASSES.iter().zip(&s.stats).filter(|(_, st)| st.runs > 0) {
            eprintln!("  {:16} runs {:5} changed {:5} {:.3}s", p.name, st.runs, st.changed, st.secs);
        }
    }
    LAST.with(|c| *c.borrow_mut() = Some(stats));
    alts.iter().map(|&n| s.table.term(n)).collect()
}

/// `secs` from now.
pub fn deadline(secs: Option<f64>) -> Option<Instant> {
    secs.map(|s| Instant::now() + Duration::from_secs_f64(s))
}
