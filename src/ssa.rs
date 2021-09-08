use petgraph::algo::dominators;
use petgraph::visit::NodeRef;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::*;

type Var<'a, Graph> = <<Graph as CFG<'a>>::Node as CFGNode<'a>>::Variable;
type VarSet<'a, Graph> = HashSet<Var<'a, Graph>>;
type VarVec<'a, Graph> = Vec<Var<'a, Graph>>;
type VarMap<'a, Graph, Value> = HashMap<Var<'a, Graph>, Value>;
type VarMapVec<'a, Graph> = VarMap<'a, Graph, VarVec<'a, Graph>>;

type Inst<'a, Graph> = <<Graph as CFG<'a>>::Node as CFGNode<'a>>::Instruction;

struct RepVar<'a, Graph: CFG<'a>> {
    old: Var<'a, Graph>,
    new: Option<usize>,
}

impl<'a, Graph: CFG<'a>> RepVar<'a, Graph> {
    fn from_old(old: Var<'a, Graph>) -> RepVar<'a, Graph> {
        RepVar { old, new: None }
    }
    fn set_new(&mut self, new: usize) {
        self.new = Some(new);
    }
}

struct Instruction<'a, Graph: CFG<'a>> {
    dvar: Option<RepVar<'a, Graph>>,
    uvar: VarVec<'a, Graph>,
}

impl<'a, Graph: CFG<'a>> Instruction<'a, Graph> {
    fn new(inst: &Inst<'a, Graph>) -> Instruction<'a, Graph> {
        Instruction {
            dvar: inst
                .defined_var()
                .and_then(|var| Some(RepVar::from_old(var))),
            uvar: inst.used_vars(),
        }
    }

    fn old_dvar(&self) -> Option<Var<'a, Graph>> {
        self.dvar.as_ref().and_then(|rv| Some(rv.old))
    }
}

#[derive(Clone)]
struct PhiVar<'a, Graph: CFG<'a>> {
    old: Var<'a, Graph>,
    new: usize,
    phi_args: VarVec<'a, Graph>,
}

impl<'a, Graph: CFG<'a>> PhiVar<'a, Graph> {
    fn from_old(old: Var<'a, Graph>) -> PhiVar<'a, Graph> {
        PhiVar {
            old,
            new: usize::MAX,
            phi_args: Default::default(),
        }
    }

    fn set_new(&mut self, new: usize) {
        self.new = new;
    }

    fn add_arg(&mut self, var: Var<'a, Graph>) {
        self.phi_args.push(var);
    }
}

struct SSA<'a, Graph: CFG<'a>> {
    graph: Graph,
    entry: NodeIndex,
    doms: Option<dominators::Dominators<NodeIndex>>,
    node_list: Vec<NodeIndex>,
    node_id: HashMap<NodeIndex, usize>,
    node_insts: Vec<Vec<Instruction<'a, Graph>>>,
    node_dvars: Vec<VarSet<'a, Graph>>,
    dom_fronts: Vec<HashSet<usize>>,
    node_phi: Vec<Vec<PhiVar<'a, Graph>>>,
    new_vars: VarMapVec<'a, Graph>,
    new_var_cache: RefCell<Vec<VarMap<'a, Graph, Var<'a, Graph>>>>,
}

impl<'a, Graph: CFG<'a>> SSA<'a, Graph> {
    pub fn new(graph: Graph, entry: NodeIndex) -> SSA<'a, Graph> {
        let node_list: Vec<NodeIndex> = graph.node_references().map(|node| node.id()).collect();
        let node_id: HashMap<NodeIndex, usize> = node_list
            .iter()
            .enumerate()
            .map(|(id, node)| (*node, id))
            .collect();
        let node_insts = node_list
            .iter()
            .map(|node| {
                graph
                    .node_weight(*node)
                    .unwrap()
                    .instructions()
                    .map(Instruction::new)
                    .collect()
            })
            .collect();
        SSA {
            graph,
            entry,
            node_list,
            node_id,
            node_insts,
            doms: None,
            dom_fronts: Default::default(),
            node_dvars: Default::default(),
            node_phi: Default::default(),
            new_vars: Default::default(),
            new_var_cache: Default::default(),
        }
    }

    pub fn analysis(&mut self) {
        self.init_node_defined_vars();
        self.dominance_frontiers();
        self.find_needed_phi_vars();
        self.create_new_vars();
        self.assign_dvars();
        self.assign_phi_args();
        self.flush();
    }

    fn init_node_defined_vars(&mut self) {
        self.node_dvars = Vec::new();
        for node in 0..self.node_list.len() {
            let mut dvars = HashSet::new();
            for inst in self.node_insts[node].iter() {
                if let Some(var) = inst.old_dvar() {
                    dvars.insert(var);
                }
            }
            self.node_dvars.push(dvars);
        }
    }

    fn dominance_frontiers(&mut self) {
        self.dom_fronts = vec![HashSet::new(); self.node_list.len()];
        let doms = dominators::simple_fast(self.graph, self.entry);
        for node in self.graph.node_references() {
            let node = node.id();
            let cur_node = *self.node_id.get(&node).unwrap();
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
                    let runner_id = *self.node_id.get(&runner).unwrap();
                    self.dom_fronts[runner_id].insert(cur_node);
                    runner = doms.immediate_dominator(runner).unwrap();
                }
            }
        }
        self.doms = Some(doms);
    }

    fn find_needed_phi_vars(&mut self) {
        let mut need_phi: Vec<VarSet<'a, Graph>> = vec![HashSet::new(); self.node_list.len()];
        for node in 0..self.node_list.len() {
            for front in self.dom_fronts[node].iter() {
                for var in self.node_dvars[node].iter() {
                    need_phi[*front].insert(*var);
                }
            }
        }
        self.node_phi = need_phi
            .into_iter()
            .map(|vars| vars.into_iter().map(PhiVar::from_old).collect())
            .collect();
    }

    fn create_new_vars(&mut self) {
        let mut var_count = HashMap::new();
        for insts in self.node_insts.iter() {
            for inst in insts.iter() {
                if let Some(var) = inst.old_dvar() {
                    *var_count.entry(var).or_insert(0) += 1;
                }
            }
        }
        for phi_vars in self.node_phi.iter() {
            for var in phi_vars.iter() {
                *var_count.entry(var.old).or_insert(0) += 1;
            }
        }
        self.new_vars = var_count
            .iter()
            .map(|(var, count)| (*var, var.split(*count)))
            .collect();
        self.new_var_cache = RefCell::new(vec![HashMap::new(); self.node_list.len()]);
    }

    fn assign_dvars(&mut self) {
        let mut var_count: VarMap<'a, Graph, usize> =
            self.new_vars.keys().map(|var| (*var, 0)).collect();
        for insts in self.node_insts.iter_mut() {
            for inst in insts.iter_mut() {
                if let Some(dvar) = inst.dvar.as_mut() {
                    let cnt = var_count.get_mut(&dvar.old).unwrap();
                    dvar.set_new(*cnt);
                    *cnt += 1;
                }
            }
        }
        for phi_vars in self.node_phi.iter_mut() {
            for pvar in phi_vars.iter_mut() {
                let cnt = var_count.get_mut(&pvar.old).unwrap();
                pvar.set_new(*cnt);
                *cnt += 1;
            }
        }
    }

    fn assign_phi_args(&mut self) {
        for (id, node) in self.node_list.iter().enumerate() {
            let node = *node;
            if !self.reachable(node) {
                continue;
            }
            let preds: Vec<NodeIndex> = self
                .graph
                .neighbors_directed(node, petgraph::Incoming)
                .collect();
            for phi_id in 0..self.node_phi[id].len() {
                let pvar = &self.node_phi[id][phi_id];
                let mut args = HashSet::new();
                for pred in preds.iter() {
                    let arg = self.find_def_at_end(pvar.old, *pred);
                    args.insert(arg);
                }
                let pvar = &mut self.node_phi[id][phi_id];
                for arg in args.into_iter() {
                    pvar.add_arg(arg);
                }
            }
        }
    }

    fn reachable(&self, node: NodeIndex) -> bool {
        if node == self.entry {
            return true;
        }
        let doms = self.doms.as_ref().unwrap();
        doms.immediate_dominator(node).is_some()
    }

    fn find_def_at_end(&self, var: Var<'a, Graph>, node: NodeIndex) -> Var<'a, Graph> {
        let id = *self.node_id.get(&node).unwrap();
        let mut cache = self.new_var_cache.borrow_mut();
        let entry = cache[id].entry(var);
        return *entry.or_insert_with(|| self.find_def_nocache(var, id, self.node_insts[id].len()));
    }

    fn find_def_nocache(&self, var: Var<'a, Graph>, id: usize, last_inst_id: usize) -> Var<'a, Graph> {
        let node = self.node_list[id];
        if self.node_dvars[id].contains(&var) && last_inst_id > 0 {
            for inst_id in last_inst_id-1..0 {
                let inst = &self.node_insts[id][inst_id];
                if let Some(dvar) = inst.dvar.as_ref() {
                    if dvar.old == var {
                        return self.get_new_var(var, dvar.new.unwrap());
                    }
                }
            }
        }
        for pvar in self.node_phi[id].iter() {
            if pvar.old == var {
                return self.get_new_var(var, pvar.new);
            }
        }
        if node == self.entry {
            return var;
        }
        let idom = self.doms.as_ref().unwrap().immediate_dominator(node);
        return self.find_def_at_end(var, idom.unwrap());
    }

    fn get_new_var(&self, old: Var<'a, Graph>, new: usize) -> Var<'a, Graph> {
        self.new_vars.get(&old).unwrap()[new]
    }

    fn flush(&mut self) {
        for id in 0..self.node_list.len() {
            let node = self.node_list[id];
            if !self.reachable(node) {
                continue;
            }
            for pvar_id in 0..self.node_phi[id].len() {
                let pvar = self.node_phi[id][pvar_id].clone();
                let new_var = self.get_new_var(pvar.old, pvar.new);
                self.flush_phi(node, pvar.phi_args, new_var);
            }
            let weight = self.graph.node_weight_mut(node).unwrap();
            for (inst_id, inst) in weight.instructions_mut().enumerate() {
                let myinst = &self.node_insts[id][inst_id];
                if let Some(dvar) = myinst.dvar.as_ref() {
                    let new_var = self.get_new_var(dvar.old, dvar.new.unwrap());
                    inst.replace_def_var(new_var);
                }
                for uvar in myinst.uvar.iter() {
                    let uvar = *uvar;
                    let new_var = self.find_def_nocache(uvar, id, inst_id);
                    inst.replace_use_var(uvar, new_var)
                }
            }
        }
    }

    fn flush_phi(&mut self, node: NodeIndex, src: Vec<Var<'a, Graph>>, dst: Var<'a, Graph>) {
        let weight = self.graph.node_weight_mut(node).unwrap();
        weight.prepend_phi(src, dst);
    }
}

pub fn ssa_analysis<'a, Graph: CFG<'a>>(graph: Graph, entry: NodeIndex) {
    SSA::new(graph, entry).analysis();
}
