use petgraph::algo::dominators;
use petgraph::visit::NodeRef;
use std::collections::{HashMap, HashSet};

use crate::*;

type Var<'a, Graph> = <<Graph as CFG<'a>>::Node as CFGNode<'a>>::Variable;
type VarSet<'a, Graph> = HashSet<Var<'a, Graph>>;
type VarVec<'a, Graph> = Vec<Var<'a, Graph>>;
type VarMap<'a, Graph, Value> = HashMap<Var<'a, Graph>, Value>;
type VarMapVec<'a, Graph> = VarMap<'a, Graph, VarVec<'a, Graph>>;

type NodeSet = HashSet<NodeIndex>;
type NodeMap<Value> = HashMap<NodeIndex, Value>;

struct SSA<'a, Graph: CFG<'a>> {
    graph: Graph,
    entry: NodeIndex,
    dom_fronts: NodeMap<NodeSet>,
    need_phi: NodeMap<VarSet<'a, Graph>>,
}

impl<'a, Graph: CFG<'a>> SSA<'a, Graph> {
    pub fn new(graph: Graph, entry: NodeIndex) -> SSA<'a, Graph> {
        SSA {
            graph,
            entry,
            dom_fronts: HashMap::new(),
            need_phi: HashMap::new(),
        }
    }

    pub fn analysis(&mut self) {
        self.dom_fronts = self.dominance_frontiers();
        self.need_phi = self.find_needed_phi_vars();
        let new_vars = self.create_new_vars();
    }

    fn node_defined_var(&self, node: NodeIndex) -> VarMap<'a, Graph, usize> {
        let inst_list = self.graph.node_weight(node).unwrap();
        let mut dvars = HashMap::new();
        for var in inst_list
            .instructions()
            .filter_map(|inst| inst.defined_var())
        {
            *dvars.entry(var).or_insert(0) += 1;
        }
        dvars
    }

    fn dominance_frontiers(&self) -> NodeMap<NodeSet> {
        let mut dom_fronts = HashMap::new();
        for node in self.graph.node_references() {
            dom_fronts.insert(node.id(), HashSet::new());
        }
        let doms = dominators::simple_fast(self.graph, self.entry);
        for node in self.graph.node_references() {
            let node = node.id();
            let idom = match doms.immediate_dominator(node) {
                None => continue,
                Some(x) => x,
            };
            let preds: Vec<NodeIndex> = self
                .graph
                .neighbors_directed(node, petgraph::Incoming)
                .collect();
            if preds.len() < 2 {
                continue;
            }
            for pred in preds {
                let mut runner = pred;
                while runner != idom {
                    dom_fronts.get_mut(&runner).unwrap().insert(node);
                    runner = doms.immediate_dominator(runner).unwrap();
                }
            }
        }
        dom_fronts
    }

    fn find_needed_phi_vars(&self) -> NodeMap<VarSet<'a, Graph>> {
        let mut phi_vars: NodeMap<VarSet<'a, Graph>> = self
            .graph
            .node_references()
            .map(|node| (node.id(), HashSet::new()))
            .collect();
        for node in self.graph.node_references() {
            let node = node.id();
            for front in self.dom_fronts.get(&node).unwrap() {
                for var in self.node_defined_var(node).keys() {
                    phi_vars.get_mut(front).unwrap().insert(*var);
                }
            }
        }
        phi_vars
    }

    fn create_new_vars(&self) -> VarMapVec<'a, Graph> {
        let mut var_count = HashMap::new();
        for node in self.graph.node_references() {
            let node = node.id();
            let dvars = self.node_defined_var(node);
            for (var, cnt) in dvars.iter() {
                *var_count.entry(*var).or_insert(0) += cnt;
            }
            let phi_vars = self.need_phi.get(&node).unwrap();
            for var in phi_vars.iter() {
                *var_count.entry(*var).or_insert(0) += 1;
            }
        }
        var_count
            .iter()
            .map(|(var, count)| (*var, var.split(*count)))
            .collect()
    }
}

pub fn ssa_analysis<'a, Graph: CFG<'a>>(graph: Graph, entry: NodeIndex) {
    SSA::new(graph, entry).analysis();
}
