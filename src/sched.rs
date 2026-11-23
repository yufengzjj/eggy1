//! Prototype scheduler for the pre-pass (step 0 of `docs/pass-framework-plan.md`): an
//! equivalence table over hash-consed nodes, small passes run on new nodes, and ancestor
//! instantiation when the best form of a class changes. Off unless `EGGY_SCHED` is set;
//! `EGGY_SCHED_TRACE` prints one line per call to stderr.

use crate::eval::{Op, Term as T, size};
use crate::linear_mba::Ctx;
use std::collections::{HashMap, HashSet, VecDeque};

/// Forms kept per class.
const ALTS: usize = 4;
/// Ancestor nodes made per call.
const MAX_INSTANCES: usize = 512;
/// Runs of whole-term passes per call.
const MAX_ROOT_RUNS: usize = 48;
/// Runs of node passes per call.
const MAX_NODE_RUNS: usize = 4096;
/// Seeds larger than this are not scheduled.
const MAX_SEED_SIZE: usize = 4000;

/// Statistics of the last `schedule` call on this thread.
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub legacy: usize,
    pub best: usize,
    pub from: String,
    pub nodes: usize,
    pub root_runs: usize,
    pub node_runs: usize,
    pub instances: usize,
    pub secs: f64,
}

thread_local! {
    static LAST: std::cell::RefCell<Option<Stats>> = const { std::cell::RefCell::new(None) };
}

/// Takes the statistics of the last `schedule` call on this thread.
pub fn take_stats() -> Option<Stats> {
    LAST.with(|c| c.borrow_mut().take())
}

pub(crate) fn enabled() -> bool {
    std::env::var_os("EGGY_SCHED").is_some()
}

fn tracing() -> bool {
    std::env::var_os("EGGY_SCHED_TRACE").is_some()
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum Key {
    Num(i64),
    Var(String),
    Op(Op, Vec<usize>),
}

struct Node {
    key: Key,
    size: usize,
    hash: u64,
}

type PassFn = fn(&T, &Ctx) -> T;

fn rebuild(t: &T, w: &Ctx) -> T {
    crate::linear_mba::cluster_regions(&crate::linear_mba::rewrite(t, w), w, false)
}
fn recombine(t: &T, w: &Ctx) -> T {
    if crate::linear_mba::selectors(t, w).is_empty() { crate::linear_mba::recombine_regions(t, w, false) } else { t.clone() }
}
fn low(t: &T, w: &Ctx) -> T {
    crate::linear_mba::unshift(&crate::lowbits::simplify(t, w), w)
}

/// Passes on a whole candidate of the root class.
const ROOT_PASSES: [(&str, PassFn); 9] = [
    ("rebuild", rebuild),
    ("relate", crate::linear_mba::relate),
    ("tfunc", crate::tfunc::simplify),
    ("recombine", recombine),
    ("cut_products", crate::lowbits::cut_products),
    ("shifted_xor", crate::lowbits::shifted_xor),
    ("lowbits_rebuilt", crate::lowbits::simplify_rebuilt),
    ("lowbits", low),
    ("halve", crate::linear_mba::halve),
];

struct Sched<'a> {
    w: &'a Ctx,
    nodes: Vec<Node>,
    ids: HashMap<Key, usize>,
    parents: Vec<Vec<usize>>,
    uf: Vec<usize>,
    members: HashMap<usize, Vec<usize>>,
    alts: HashMap<usize, Vec<usize>>,
    /// The pass chain that made each node, for the trace.
    from: Vec<String>,
    root: usize,
    memo: HashSet<(usize, usize)>,
    root_queue: VecDeque<usize>,
    node_queue: VecDeque<usize>,
    events: VecDeque<usize>,
    root_runs: usize,
    node_runs: usize,
    instances: usize,
}

impl<'a> Sched<'a> {
    fn find(&mut self, mut c: usize) -> usize {
        while self.uf[c] != c {
            self.uf[c] = self.uf[self.uf[c]];
            c = self.uf[c];
        }
        c
    }

    fn rank(&self, n: usize) -> (usize, u64) {
        (self.nodes[n].size, self.nodes[n].hash)
    }

    fn best(&mut self, n: usize) -> usize {
        let c = self.find(n);
        self.alts[&c][0]
    }

    /// The node for `key`, and whether it is new.
    fn node(&mut self, key: Key, from: &str) -> (usize, bool) {
        if let Some(&id) = self.ids.get(&key) {
            return (id, false);
        }
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        let size = match &key {
            Key::Num(v) => {
                (0u8, v).hash(&mut h);
                1
            }
            Key::Var(v) => {
                (1u8, v).hash(&mut h);
                1
            }
            Key::Op(op, kids) => {
                (2u8, op).hash(&mut h);
                kids.iter().for_each(|&k| self.nodes[k].hash.hash(&mut h));
                1 + kids.iter().map(|&k| self.nodes[k].size).sum::<usize>()
            }
        };
        let id = self.nodes.len();
        if let Key::Op(_, kids) = &key {
            for &k in kids {
                self.parents[k].push(id);
            }
        }
        self.nodes.push(Node { key: key.clone(), size, hash: h.finish() });
        self.ids.insert(key, id);
        self.parents.push(Vec::new());
        self.uf.push(id);
        self.members.insert(id, vec![id]);
        self.alts.insert(id, vec![id]);
        self.from.push(from.to_string());
        self.node_queue.push_back(id);
        (id, true)
    }

    fn intern(&mut self, t: &T, from: &str) -> usize {
        let key = match t {
            T::Num(v) => Key::Num(*v),
            T::Var(v) => Key::Var(v.clone()),
            T::Op(op, a) => Key::Op(*op, a.iter().map(|x| self.intern(x, from)).collect()),
        };
        self.node(key, from).0
    }

    fn term(&self, n: usize) -> T {
        match &self.nodes[n].key {
            Key::Num(v) => T::Num(*v),
            Key::Var(v) => T::Var(v.clone()),
            Key::Op(op, kids) => T::Op(*op, kids.iter().map(|&k| self.term(k)).collect()),
        }
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (old_a, old_b) = (self.alts[&ra][0], self.alts[&rb][0]);
        let (keep, gone) = if self.members[&ra].len() >= self.members[&rb].len() { (ra, rb) } else { (rb, ra) };
        self.uf[gone] = keep;
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
    fn instantiate(&mut self, c: usize) {
        let c = self.find(c);
        let members = self.members[&c].clone();
        for m in members {
            for p in self.parents[m].clone() {
                if self.instances >= MAX_INSTANCES {
                    return;
                }
                let Key::Op(op, kids) = self.nodes[p].key.clone() else { continue };
                let best: Vec<usize> = kids.iter().map(|&k| self.best(k)).collect();
                if best == kids {
                    continue;
                }
                let bc = self.best(c);
                let from = format!("{}<{}", self.from[p], self.from[bc]);
                let (q, new) = self.node(Key::Op(op, best), &from);
                if new {
                    self.instances += 1;
                }
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

    fn add_result(&mut self, src: usize, r: &T, name: &str) {
        let from = if self.from[src].is_empty() { name.to_string() } else { format!("{}>{}", self.from[src], name) };
        let before = self.nodes.len();
        let id = self.intern(r, &from);
        // Subterms of the result keep the chain of the result itself.
        for n in before..self.nodes.len() {
            self.from[n] = from.clone();
        }
        let root = self.find(self.root);
        let is_root = self.find(src) == root;
        if is_root && id < before && self.find(id) != root {
            self.from[id] = from.clone();
        }
        self.union(src, id);
        if is_root && id >= before {
            self.queue_root(id);
        }
        self.settle();
    }

    /// Whole-term passes only for root forms not much larger than the best one.
    fn queue_root(&mut self, n: usize) {
        let b = self.best(self.root);
        let best = self.nodes[b].size;
        if self.nodes[n].size <= 2 * best {
            self.root_queue.push_back(n);
        }
    }

    fn run(&mut self) {
        loop {
            if let Some(n) = self.node_queue.pop_front() {
                if self.node_runs >= MAX_NODE_RUNS || self.nodes[n].size < 2 || self.nodes[n].size > 256 {
                    continue;
                }
                self.node_runs += 1;
                let t = self.term(n);
                if let Some(r) = crate::tfunc::replacement(&t, self.w) {
                    check(&t, &r, self.w, "tfunc_node");
                    self.add_result(n, &r, "tfunc_node");
                }
                continue;
            }
            let Some(n) = self.root_queue.pop_front() else { break };
            for (i, (name, f)) in ROOT_PASSES.iter().enumerate() {
                if self.root_runs >= MAX_ROOT_RUNS || !self.memo.insert((i, n)) {
                    continue;
                }
                self.root_runs += 1;
                let t = self.term(n);
                let r = f(&t, self.w);
                if r != t {
                    check(&t, &r, self.w, name);
                    self.add_result(n, &r, name);
                }
            }
        }
    }
}

/// Random-evaluation check of a pass result in debug builds.
fn check(a: &T, b: &T, w: &Ctx, name: &str) {
    if !cfg!(debug_assertions) {
        return;
    }
    let mut vars = Vec::new();
    collect_vars(a, &mut vars);
    collect_vars(b, &mut vars);
    let ty = crate::eval::NumType { bits: w.w, signed: false };
    let mut s = 0x9e3779b97f4a7c15u64;
    for _ in 0..16 {
        let vals: HashMap<&str, u64> = vars
            .iter()
            .map(|v| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                (v.as_str(), s)
            })
            .collect();
        let (x, y) = (crate::eval::eval(a, ty, &|v| vals[v]), crate::eval::eval(b, ty, &|v| vals[v]));
        if x.is_some() && y.is_some() {
            assert_eq!(x, y, "pass {name} changed the value of {}", crate::eval::show(a));
        }
    }
}

fn collect_vars(t: &T, out: &mut Vec<String>) {
    match t {
        T::Var(v) if !out.contains(v) => out.push(v.clone()),
        T::Op(_, a) => a.iter().for_each(|x| collect_vars(x, out)),
        _ => {}
    }
}

/// The root class forms, smallest first, starting from the input and the legacy rebuilds.
pub(crate) fn schedule(input: &T, seeds: &[T], w: &Ctx) -> Vec<T> {
    let all: Vec<&T> = std::iter::once(input).chain(seeds).collect();
    if all.iter().any(|t| size(t) > MAX_SEED_SIZE) {
        return Vec::new();
    }
    let start = std::time::Instant::now();
    let mut s = Sched {
        w,
        nodes: Vec::new(),
        ids: HashMap::new(),
        parents: Vec::new(),
        uf: Vec::new(),
        members: HashMap::new(),
        alts: HashMap::new(),
        from: Vec::new(),
        root: 0,
        memo: HashSet::new(),
        root_queue: VecDeque::new(),
        node_queue: VecDeque::new(),
        events: VecDeque::new(),
        root_runs: 0,
        node_runs: 0,
        instances: 0,
    };
    s.root = s.intern(input, "input");
    for (i, t) in seeds.iter().enumerate() {
        let id = s.intern(t, &format!("legacy{i}"));
        s.union(s.root, id);
    }
    s.settle();
    let legacy_best = seeds.iter().map(size).min().unwrap_or(size(input));
    // Seeds were already rebuilt; whole-term passes start from the smallest forms.
    let root = s.find(s.root);
    s.root_queue.extend(s.alts[&root].clone());
    s.run();
    let root = s.find(s.root);
    let alts = s.alts[&root].clone();
    let b = alts[0];
    let stats = Stats {
        legacy: legacy_best,
        best: s.nodes[b].size,
        from: s.from[b].clone(),
        nodes: s.nodes.len(),
        root_runs: s.root_runs,
        node_runs: s.node_runs,
        instances: s.instances,
        secs: start.elapsed().as_secs_f64(),
    };
    if tracing() {
        eprintln!("sched: {stats:?}");
    }
    LAST.with(|c| *c.borrow_mut() = Some(stats));
    alts.iter().map(|&n| s.term(n)).collect()
}
