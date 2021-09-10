use petgraph::algo::dominators;
use petgraph::visit::NodeRef;
use std::cell::{RefCell, RefMut};
use std::collections::{HashMap, HashSet, VecDeque};
use std::marker::PhantomData;

use crate::*;

struct RepVar<Var> {
    old: Var,
    new: Option<usize>,
}

impl<Var> RepVar<Var>
where
    Var: Variable,
{
    fn from_old(old: Var) -> RepVar<Var> {
        RepVar { old, new: None }
    }
    fn set_new(&mut self, new: usize) {
        self.new = Some(new);
    }
}

struct Instruction<Var> {
    dvar: Option<RepVar<Var>>,
    uvars: Vec<Var>,
}

impl<Var> Instruction<Var>
where
    Var: Variable,
{
    fn new<Inst>(inst: &Inst) -> Instruction<Var>
    where
        Inst: DefUseVars<Variable = Var>,
    {
        Instruction {
            dvar: inst
                .defined_var()
                .and_then(|var| Some(RepVar::from_old(var))),
            uvars: inst.used_vars(),
        }
    }

    fn old_dvar(&self) -> Option<Var> {
        self.dvar.as_ref().and_then(|rv| Some(rv.old.clone()))
    }
}

#[derive(Clone)]
struct PhiVar<Var> {
    old: Var,
    new: usize,
    phi_args: Vec<Var>,
}

impl<Var> PhiVar<Var> {
    fn from_old(old: Var) -> PhiVar<Var> {
        PhiVar {
            old,
            new: usize::MAX,
            phi_args: Default::default(),
        }
    }

    fn set_new(&mut self, new: usize) {
        self.new = new;
    }

    fn add_arg(&mut self, var: Var) {
        self.phi_args.push(var);
    }
}

pub struct SSA<Graph, Var> {
    entry: NodeIndex,
    doms: Option<dominators::Dominators<NodeIndex>>,
    node_list: Vec<NodeIndex>,
    node_id: HashMap<NodeIndex, usize>,
    node_insts: Vec<Vec<Instruction<Var>>>,
    node_dvars: Vec<HashSet<Var>>,
    dom_fronts: Vec<HashSet<usize>>,
    node_phi: Vec<Vec<PhiVar<Var>>>,
    new_vars: HashMap<Var, Vec<Var>>,
    new_var_cache: RefCell<HashMap<(usize, usize), HashMap<Var, Var>>>,
    _phantom: PhantomData<Graph>,
}

impl<Graph, Var> SSA<Graph, Var>
where
    Graph: CFG,
    Var: Variable,
    <Graph as CFG>::Node: for<'a> CFGNode<'a, Variable = Var>,
{
    pub fn new() -> SSA<Graph, Var> {
        SSA {
            entry: NodeIndex::end(),
            node_list: Default::default(),
            node_id: Default::default(),
            node_insts: Default::default(),
            doms: None,
            dom_fronts: Default::default(),
            node_dvars: Default::default(),
            node_phi: Default::default(),
            new_vars: Default::default(),
            new_var_cache: Default::default(),
            _phantom: Default::default(),
        }
    }

    pub fn analysis(graph: Graph, entry: NodeIndex) {
        let mut state = SSA::<Graph, Var>::new();
        state.entry = entry;
        state.node_list = state.init_node_list(graph);
        state.node_id = state.init_node_id();
        state.node_insts = state.init_new_insts(graph);
        state.node_dvars = state.init_node_dvars();
        state.doms = Some(dominators::simple_fast(graph, entry));
        state.dom_fronts = state.dominance_frontiers(graph);
        state.node_phi = state.find_needed_phi_vars();
        state.new_vars = state.create_new_vars();
        state.new_var_cache = RefCell::new(HashMap::new());
        state.assign_dvars();
        state.assign_phi_args(graph);
        state.flush(graph);
    }

    fn init_node_list(&self, graph: Graph) -> Vec<NodeIndex> {
        graph.node_references().map(|node| node.id()).collect()
    }

    fn init_node_id(&self) -> HashMap<NodeIndex, usize> {
        self.node_list
            .iter()
            .enumerate()
            .map(|(id, node)| (*node, id))
            .collect()
    }

    fn init_new_insts(&self, graph: Graph) -> Vec<Vec<Instruction<Var>>> {
        let mut node_insts = Vec::new();
        for node in self.node_list.iter() {
            let weight = graph.node_weight(*node).unwrap().borrow();
            let insts = weight.instructions().map(Instruction::<Var>::new).collect();
            node_insts.push(insts);
        }
        node_insts
    }

    fn init_node_dvars(&self) -> Vec<HashSet<Var>> {
        let mut node_dvars = Vec::new();
        for node in 0..self.node_insts.len() {
            let mut dvars = HashSet::new();
            for inst in self.node_insts[node].iter() {
                if let Some(var) = inst.old_dvar() {
                    dvars.insert(var);
                }
            }
            node_dvars.push(dvars);
        }
        node_dvars
    }

    fn dominance_frontiers(&self, graph: Graph) -> Vec<HashSet<usize>> {
        let mut dom_fronts = vec![HashSet::new(); self.node_list.len()];
        let doms = self.doms.as_ref().unwrap();
        for node in graph.node_references() {
            let node = node.id();
            let cur_node = *self.node_id.get(&node).unwrap();
            let mut is_entry = 0;
            let idom = doms.immediate_dominator(node);
            if idom.is_none() {
                if node != self.entry {
                    continue;
                }
                is_entry = 1;
            }
            let preds: Vec<NodeIndex> =
                graph.neighbors_directed(node, petgraph::Incoming).collect();
            if preds.len() + is_entry < 2 {
                continue;
            }
            for pred in preds {
                let mut runner = pred;
                while Some(runner) != idom {
                    let runner_id = *self.node_id.get(&runner).unwrap();
                    dom_fronts[runner_id].insert(cur_node);
                    let up = doms.immediate_dominator(runner);
                    if up == idom {
                        break;
                    }
                    runner = up.unwrap();
                }
            }
        }
        dom_fronts
    }

    fn find_needed_phi_vars(&self) -> Vec<Vec<PhiVar<Var>>> {
        let mut need_phi: Vec<HashSet<Var>> = vec![HashSet::new(); self.node_list.len()];
        for node in 0..self.node_list.len() {
            for var in self.node_dvars[node].iter() {
                let mut queue: VecDeque<usize> =
                    self.dom_fronts[node].clone().into_iter().collect();
                while let Some(front) = queue.pop_front() {
                    if need_phi[front].insert(var.clone()) {
                        for new_front in self.dom_fronts[front].iter() {
                            let new_front = *new_front;
                            queue.push_back(new_front);
                        }
                    }
                }
            }
        }
        need_phi
            .into_iter()
            .map(|vars| vars.into_iter().map(PhiVar::from_old).collect())
            .collect()
    }

    fn create_new_vars(&self) -> HashMap<Var, Vec<Var>> {
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
                *var_count.entry(var.old.clone()).or_insert(0) += 1;
            }
        }
        var_count
            .iter()
            .map(|(var, count)| (var.clone(), var.split(*count)))
            .collect()
    }

    fn assign_dvars(&mut self) {
        let mut var_count: HashMap<Var, usize> =
            self.new_vars.keys().map(|var| (var.clone(), 0)).collect();
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

    fn assign_phi_args(&mut self, graph: Graph) {
        for (id, node) in self.node_list.iter().enumerate() {
            let node = *node;
            if !self.reachable(node) {
                continue;
            }
            let preds: Vec<NodeIndex> =
                graph.neighbors_directed(node, petgraph::Incoming).collect();
            for phi_id in 0..self.node_phi[id].len() {
                let pvar = &self.node_phi[id][phi_id];
                let mut args = HashSet::new();
                if node == self.entry {
                    args.insert(pvar.old.clone());
                }
                for pred in preds.iter() {
                    let arg = self.find_def_at_end(&pvar.old, *pred);
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

    fn find_def_at_end(&self, var: &Var, node: NodeIndex) -> Var {
        let id = *self.node_id.get(&node).unwrap();
        self.find_def(var, id, self.node_insts[id].len())
    }

    fn find_def_cache(
        &self,
        var: &Var,
        id: usize,
        last_inst_id: usize,
        cache: &mut RefMut<HashMap<(usize, usize), HashMap<Var, Var>>>,
    ) -> Var {
        let var_map = cache.entry((id, last_inst_id)).or_insert(HashMap::new());
        if let Some(ans) = var_map.get(var) {
            return ans.clone();
        }
        let ans = self.find_def_nocache(var, id, last_inst_id, cache);
        cache
            .get_mut(&(id, last_inst_id))
            .unwrap()
            .insert(var.clone(), ans.clone());
        ans
    }

    fn find_def(&self, var: &Var, id: usize, last_inst_id: usize) -> Var {
        let mut cache = self.new_var_cache.borrow_mut();
        self.find_def_cache(var, id, last_inst_id, &mut cache)
    }

    fn find_def_nocache(
        &self,
        var: &Var,
        id: usize,
        last_inst_id: usize,
        cache: &mut RefMut<HashMap<(usize, usize), HashMap<Var, Var>>>,
    ) -> Var {
        let node = self.node_list[id];
        if self.node_dvars[id].contains(var) && last_inst_id > 0 {
            for inst_id in (0..last_inst_id).rev() {
                let inst = &self.node_insts[id][inst_id];
                if let Some(dvar) = inst.dvar.as_ref() {
                    if dvar.old.eq(var) {
                        return self.get_new_var(var, dvar.new.unwrap());
                    }
                }
            }
        }
        for pvar in self.node_phi[id].iter() {
            if pvar.old.eq(var) {
                return self.get_new_var(var, pvar.new);
            }
        }
        if node == self.entry {
            return var.clone();
        }
        let idom = self.doms.as_ref().unwrap().immediate_dominator(node);
        let idom = *self.node_id.get(&idom.unwrap()).unwrap();
        return self.find_def_cache(var, idom, self.node_insts[idom].len(), cache);
    }

    fn get_new_var(&self, old: &Var, new: usize) -> Var {
        self.new_vars.get(old).unwrap()[new].clone()
    }

    fn flush(&self, graph: Graph) {
        for id in 0..self.node_list.len() {
            let node = self.node_list[id];
            if !self.reachable(node) {
                continue;
            }
            let mut weight = graph.node_weight(node).unwrap().borrow_mut();
            for pvar_id in 0..self.node_phi[id].len() {
                let pvar = self.node_phi[id][pvar_id].clone();
                let new_var = self.get_new_var(&pvar.old, pvar.new);
                weight.prepend_phi(pvar.phi_args, new_var);
            }
            for (inst_id, inst) in weight.instructions_mut().enumerate() {
                let myinst = &self.node_insts[id][inst_id];
                if let Some(dvar) = myinst.dvar.as_ref() {
                    let new_var = self.get_new_var(&dvar.old, dvar.new.unwrap());
                    inst.replace_def_var(new_var);
                }
                for uvar in myinst.uvars.iter() {
                    let new_var = self.find_def(uvar, id, inst_id);
                    inst.replace_use_var(uvar, new_var)
                }
            }
        }
    }
}
