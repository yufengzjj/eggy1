//! Hash-consed terms: equal subterms are stored once and named by a `NodeId`.

use crate::eval::{self, NumType, Op, Term};
use std::collections::HashMap;

pub type NodeId = u32;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
    Num(i64),
    Var(String),
    Op(Op, Vec<NodeId>),
}

#[derive(Default)]
pub struct NodeTable {
    entries: Vec<Node>,
    ids: HashMap<Node, NodeId>,
}

impl NodeTable {
    pub fn new() -> NodeTable {
        NodeTable::default()
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn node(&self, id: NodeId) -> &Node {
        &self.entries[id as usize]
    }

    fn add(&mut self, node: Node) -> NodeId {
        if let Some(&id) = self.ids.get(&node) {
            return id;
        }
        let id = self.entries.len() as NodeId;
        self.entries.push(node.clone());
        self.ids.insert(node, id);
        id
    }

    pub fn intern(&mut self, t: &Term) -> NodeId {
        let node = match t {
            Term::Num(v) => Node::Num(*v),
            Term::Var(v) => Node::Var(v.clone()),
            Term::Op(op, a) => Node::Op(*op, a.iter().map(|x| self.intern(x)).collect()),
        };
        self.add(node)
    }

    /// The value of every node, as `eval::eval` (`None` below a division by zero); children
    /// come before their parents in the table, so one pass in id order does it.
    pub fn eval_all(&self, ty: NumType, env: &impl Fn(&str) -> u64) -> Vec<Option<u64>> {
        let mut vals: Vec<Option<u64>> = Vec::with_capacity(self.len());
        for e in &self.entries {
            let v = match e {
                Node::Num(c) => Some(*c as u64 & ty.mask()),
                Node::Var(v) => Some(env(v) & ty.mask()),
                Node::Op(op, kids) => {
                    let x = vals[kids[0] as usize];
                    let y = kids.get(1).map_or(Some(0), |&k| vals[k as usize]);
                    x.zip(y).and_then(|(x, y)| eval::apply(*op, x, y, ty))
                }
            };
            vals.push(v);
        }
        vals
    }

    /// Egglog commands that bind each subterm of `roots` used more than once (and larger
    /// than one node) to a global `<prefix><id>`, and the roots written with those names.
    pub fn show_shared(&self, roots: &[NodeId], prefix: &str) -> (String, Vec<String>) {
        let mut uses = vec![0u32; self.len()];
        let mut seen = vec![false; self.len()];
        let mut order = Vec::new();
        for &r in roots {
            uses[r as usize] += 1;
            self.post_order(r, &mut seen, &mut uses, &mut order);
        }
        let shared = |id: NodeId| uses[id as usize] > 1 && matches!(self.node(id), Node::Op(..));
        let mut names: HashMap<NodeId, String> = HashMap::new();
        let mut lets = String::new();
        for &id in &order {
            if shared(id) && !roots.contains(&id) {
                let text = self.show_with(id, &names);
                let name = format!("{prefix}{id}");
                lets += &format!("(let {name} {text})\n");
                names.insert(id, name);
            }
        }
        (lets, roots.iter().map(|&r| self.show_with(r, &names)).collect())
    }

    /// Children first; counts each reference to a node once per parent node.
    fn post_order(&self, id: NodeId, seen: &mut [bool], uses: &mut [u32], order: &mut Vec<NodeId>) {
        if seen[id as usize] {
            return;
        }
        seen[id as usize] = true;
        if let Node::Op(_, kids) = self.node(id) {
            for &k in kids {
                uses[k as usize] += 1;
                self.post_order(k, seen, uses, order);
            }
        }
        order.push(id);
    }

    fn show_with(&self, id: NodeId, names: &HashMap<NodeId, String>) -> String {
        let mut out = String::new();
        self.write(id, names, &mut out, true);
        out
    }

    fn write(&self, id: NodeId, names: &HashMap<NodeId, String>, out: &mut String, top: bool) {
        if !top && let Some(n) = names.get(&id) {
            out.push_str(n);
            return;
        }
        match self.node(id) {
            Node::Num(v) => out.push_str(&format!("(Num {v})")),
            Node::Var(v) => out.push_str(&format!("(Var \"{v}\")")),
            Node::Op(op, kids) => {
                out.push_str(&format!("({op}"));
                for &k in kids {
                    out.push(' ');
                    self.write(k, names, out, false);
                }
                out.push(')');
            }
        }
    }
}
