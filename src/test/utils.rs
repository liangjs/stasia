use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::iter::FromIterator;

use petgraph::graph::NodeIndex;
use petgraph::{dot, visit::IntoNodeReferences};
use rand::{prelude::SliceRandom, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

use crate::{ssa_analysis, CFGNode, DefUseVars, CFG};

pub type ControlFlowGraph = petgraph::graph::DiGraph<RefCell<Node>, ()>;

impl CFG for &ControlFlowGraph {
    type Node = Node;
}

#[derive(Debug)]
pub struct Node {
    pub instructions: Vec<Instruction>,
    pub phi_vars: Vec<PhiVar>,
}

impl Node {
    pub fn new(instructions: Vec<Instruction>) -> Node {
        Node {
            instructions,
            phi_vars: Vec::new(),
        }
    }
}

impl ToString for Node {
    fn to_string(&self) -> String {
        let mut ans = String::new();
        for pvar in self.phi_vars.iter() {
            ans += &pvar.to_string();
            ans += "\n";
        }
        for inst in self.instructions.iter() {
            ans += &inst.to_string();
            ans += "\n";
        }
        ans
    }
}

impl<'a> CFGNode<'a> for Node {
    type Variable = Variable;
    type Instruction = Instruction;
    type InstIter = std::slice::Iter<'a, Instruction>;
    type InstIterMut = std::slice::IterMut<'a, Instruction>;

    fn instructions(&'a self) -> Self::InstIter {
        self.instructions.iter()
    }

    fn instructions_mut(&'a mut self) -> Self::InstIterMut {
        self.instructions.iter_mut()
    }

    fn prepend_phi(&mut self, src: Vec<Self::Variable>, dst: Self::Variable) {
        self.phi_vars.push(PhiVar { src, dst });
    }
}

#[derive(Debug)]
pub struct PhiVar {
    pub src: Vec<Variable>,
    pub dst: Variable,
}

impl ToString for PhiVar {
    fn to_string(&self) -> String {
        let def_part = self.dst.to_string();
        let use_part: Vec<String> = self.src.iter().map(Variable::to_string).collect();
        format!("{} = phi({})", def_part, use_part.join(", "))
    }
}

#[derive(Debug)]
pub struct Instruction {
    pub dvar: Option<Variable>,
    pub uvars: Vec<Variable>,
    pub new_dvar: Option<Variable>,
    pub new_uvars: Vec<Option<Variable>>,
}

impl Instruction {
    pub fn new(dvar: Option<Variable>, uvars: Vec<Variable>) -> Instruction {
        let num = uvars.len();
        Instruction {
            dvar,
            uvars,
            new_dvar: None,
            new_uvars: vec![None; num],
        }
    }

    fn combine_var_str(old: &Variable, new: &Option<Variable>) -> String {
        match new {
            Some(new) => {
                assert!(old.name == new.name);
                new.to_string()
            }
            None => old.to_string(),
        }
    }
}

impl ToString for Instruction {
    fn to_string(&self) -> String {
        let mut ans = String::new();
        if let Some(dvar) = self.dvar.as_ref() {
            ans += &Instruction::combine_var_str(dvar, &self.new_dvar);
            ans += " = ";
        }
        if self.uvars.is_empty() {
            ans += "?";
        } else {
            let use_part: Vec<String> = (0..self.uvars.len())
                .map(|i| Instruction::combine_var_str(&self.uvars[i], &self.new_uvars[i]))
                .collect();
            ans += &use_part.join(" + ");
        }
        ans
    }
}

impl DefUseVars for Instruction {
    type Variable = Variable;

    fn defined_var(&self) -> Option<Self::Variable> {
        self.dvar.clone()
    }

    fn used_vars(&self) -> Vec<Self::Variable> {
        self.uvars.clone()
    }

    fn replace_def_var(&mut self, new_var: Self::Variable) {
        assert!(self.dvar.is_some());
        self.new_dvar = Some(new_var);
    }

    fn replace_use_var(&mut self, old_var: &Self::Variable, new_var: Self::Variable) {
        for (i, v) in self.uvars.iter().enumerate() {
            if old_var.eq(v) {
                self.new_uvars[i] = Some(new_var.clone());
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Variable {
    pub name: String,
    pub id: usize,
}

impl Variable {
    pub fn new(name: String) -> Variable {
        Variable { name, id: 0 }
    }
}

impl ToString for Variable {
    fn to_string(&self) -> String {
        format!("{}_{}", self.name, self.id)
    }
}

impl crate::Variable for Variable {
    fn split(&self, num: usize) -> Vec<Self> {
        (0..num)
            .map(|i| Variable {
                name: self.name.clone(),
                id: self.id + i + 1,
            })
            .collect()
    }
}

pub fn dot_view<'a>(graph: &'a ControlFlowGraph, entry: NodeIndex) -> String {
    let config = [dot::Config::EdgeNoLabel, dot::Config::NodeNoLabel];
    let edge_attr = |_, _| String::new();
    let node_attr = |_graph: &'a ControlFlowGraph,
                     node: <&'a ControlFlowGraph as IntoNodeReferences>::NodeRef|
     -> String {
        let shape = if node.0 == entry {
            "shape=circle"
        } else {
            "shape=box"
        };
        let label = &*format!("label=\"{}\"", node.1.borrow().to_string());
        [shape, label].join(",")
    };
    let view = dot::Dot::with_attr_getters(graph, &config, &edge_attr, &node_attr);
    format!("{:?}", view)
}

pub fn build_graph(
    nodes: Vec<Node>,
    entry: usize,
    edges: Vec<(usize, usize)>,
) -> (ControlFlowGraph, NodeIndex) {
    let node_num = nodes.len();
    let mut graph = ControlFlowGraph::with_capacity(node_num, edges.len());
    let mut node_map = HashMap::new();
    for (i, mynode) in nodes.into_iter().enumerate() {
        let node = graph.add_node(RefCell::new(mynode));
        node_map.insert(i, node);
    }
    for e in edges.iter() {
        let e0 = node_map.get(&e.0).unwrap();
        let e1 = node_map.get(&e.1).unwrap();
        graph.add_edge(*e0, *e1, ());
    }
    let entry = node_map.get(&entry).unwrap();
    (graph, *entry)
}

pub fn random_graph<T: Rng>(
    rng: &mut T,
    nodes: Vec<Node>,
    density: f64,
) -> (ControlFlowGraph, NodeIndex) {
    let node_num = nodes.len();
    let mut edges: Vec<Vec<usize>> = Vec::with_capacity(node_num);
    edges.resize(node_num, Default::default());

    /* first, generate a random tree */
    for i in 1..node_num {
        let fr = rng.gen_range(0..i);
        edges[fr].push(i);
    }

    /* add random edges */
    let add_edge_num = (node_num as f64 * density).ceil() as usize;
    for _ in 0..add_edge_num {
        let x = rng.gen_range(0..node_num);
        let y = rng.gen_range(0..node_num);
        edges[x].push(y);
    }

    /* randomize node number */
    let mut order: Vec<usize> = (0..node_num).collect();
    order.shuffle(rng);

    /* collect edges */
    let mut edges_vec: Vec<(usize, usize)> = Vec::new();
    for x in 0..node_num {
        for y in edges[x].iter() {
            let y = *y;
            edges_vec.push((order[x], order[y]));
        }
    }
    let (graph, entry) = build_graph(nodes, order[0], edges_vec);
    (graph, entry)
}

pub fn random_nodes<T: Rng>(
    rng: &mut T,
    node_num: usize,
    var_pool: &Vec<Variable>,
    inst_num: usize,
    use_num: usize,
) -> Vec<Node> {
    let mut nodes = Vec::new();
    for _ in 0..node_num {
        let inum = rng.gen_range(0..inst_num);
        let mut insts = Vec::new();
        for _ in 0..inum {
            let dvar = if rng.gen_bool(0.5) {
                None
            } else {
                var_pool.choose(rng).and_then(|v| Some(v.clone()))
            };
            let uvars: Vec<Variable> = (0..rng.gen_range(0..use_num))
                .map(|_| var_pool.choose(rng).unwrap().clone())
                .collect();
            if dvar.is_some() || !uvars.is_empty() {
                insts.push(Instruction::new(dvar, uvars));
            }
        }
        nodes.push(Node::new(insts));
    }
    nodes
}

pub fn random_cfg<T: Rng>(
    rng: &mut T,
    var_num: usize,
    node_num: usize,
    inst_num: usize,
    use_num: usize,
    density: f64,
) -> ((ControlFlowGraph, NodeIndex), Vec<Variable>) {
    let var_pool = (0..var_num)
        .map(|id| Variable::new(format!("var{}", id)))
        .collect();
    let nodes = random_nodes(rng, node_num, &var_pool, inst_num, use_num);
    (random_graph(rng, nodes, density), var_pool)
}

pub fn random_test_seeded(
    seed: <ChaCha8Rng as SeedableRng>::Seed,
    var_num: usize,
    node_num: usize,
    inst_num: usize,
    use_num: usize,
    density: f64,
) {
    let mut rng = ChaCha8Rng::from_seed(seed);
    let ((graph, entry), var_pool) =
        random_cfg(&mut rng, var_num, node_num, inst_num, use_num, density);
    ssa_analysis(&graph, entry);
    println!("{}", dot_view(&graph, entry));
    Checker::check(&graph, entry, &var_pool);
}

type VarDef = HashMap<Variable, Vec<(NodeIndex, usize)>>;

struct Checker {
    entry: NodeIndex,
    phi_defs: HashMap<Variable, Vec<Variable>>,
    var_defs: HashMap<NodeIndex, Vec<VarDef>>,
    var_defs2: HashMap<Variable, (NodeIndex, usize)>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            entry: NodeIndex::end(),
            phi_defs: Default::default(),
            var_defs: Default::default(),
            var_defs2: Default::default(),
        }
    }

    pub fn check(graph: &ControlFlowGraph, entry: NodeIndex, var_pool: &Vec<Variable>) {
        let mut state = Checker::new();
        state.entry = entry;
        state.phi_defs = Checker::init_phi_defs(graph);
        state.var_defs = Checker::init_var_defs(graph, entry, var_pool);
        state.var_defs2 = Checker::init_var_defs2(graph, entry, var_pool);
        for (node_id, node) in graph.node_references() {
            for (inst_id, inst) in node.borrow().instructions.iter().enumerate() {
                let defs = &state.var_defs.get(&node_id).unwrap()[inst_id];
                for (uvar_id, uvar) in inst.uvars.iter().enumerate() {
                    let uvar_defs: HashSet<(NodeIndex, usize)> =
                        HashSet::from_iter(defs.get(uvar).unwrap().clone());
                    let uvar_defs2 = state.get_dvar_new(&inst.new_uvars[uvar_id]);
                    assert!(
                        uvar_defs == uvar_defs2,
                        "at ({},{},{})\n{:?}\n{:?};",
                        node_id.index(),
                        inst_id,
                        uvar_id,
                        uvar_defs,
                        uvar_defs2
                    );
                }
            }
        }
    }

    fn init_phi_defs(graph: &ControlFlowGraph) -> HashMap<Variable, Vec<Variable>> {
        let mut phi_defs = HashMap::new();
        for (_id, node) in graph.node_references() {
            let node = node.borrow();
            for pvar in node.phi_vars.iter() {
                let old_def = phi_defs.insert(pvar.dst.clone(), pvar.src.clone());
                assert!(old_def.is_none());
            }
        }
        phi_defs
    }

    fn get_phi_def(&self, var: &Variable) -> HashSet<Variable> {
        let mut ans: HashSet<Variable> = HashSet::new();
        let mut visit: HashSet<Variable> = HashSet::new();
        let mut queue: VecDeque<Variable> = VecDeque::new();
        for v in self.phi_defs.get(var).unwrap().iter() {
            visit.insert(v.clone());
            queue.push_back(v.clone());
        }
        while let Some(front) = queue.pop_front() {
            let defs = self.phi_defs.get(&front);
            if defs.is_none() {
                ans.insert(front.clone());
                continue;
            }
            for v in defs.unwrap().iter() {
                if visit.insert(v.clone()) {
                    queue.push_back(v.clone());
                }
            }
        }
        ans
    }

    fn init_var_defs2(
        graph: &ControlFlowGraph,
        entry: NodeIndex,
        var_pool: &Vec<Variable>,
    ) -> HashMap<Variable, (NodeIndex, usize)> {
        let mut var_defs2 = HashMap::new();
        for var in var_pool.iter() {
            var_defs2.insert(var.clone(), (entry, usize::MAX));
        }
        for (node_id, node) in graph.node_references() {
            let node = node.borrow();
            for (inst_id, inst) in node.instructions().enumerate() {
                if let Some(var) = inst.new_dvar.clone() {
                    var_defs2.insert(var, (node_id, inst_id));
                }
            }
        }
        var_defs2
    }

    fn init_var_defs(
        graph: &ControlFlowGraph,
        entry: NodeIndex,
        var_pool: &Vec<Variable>,
    ) -> HashMap<NodeIndex, Vec<VarDef>> {
        let mut var_defs = HashMap::new();
        for (node_id, node) in graph.node_references() {
            let node = node.borrow();
            var_defs.insert(node_id, vec![HashMap::new(); node.instructions.len()]);
        }
        for var in var_pool.iter() {
            Checker::flush_def_var(graph, &mut var_defs, entry, usize::MAX, var);
        }
        for (node_id, node) in graph.node_references() {
            let node = node.borrow();
            for (inst_id, inst) in node.instructions().enumerate() {
                if let Some(var) = inst.dvar.clone() {
                    Checker::flush_def_var(graph, &mut var_defs, node_id, inst_id, &var);
                }
            }
        }
        var_defs
    }

    fn flush_def_var(
        graph: &ControlFlowGraph,
        var_defs: &mut HashMap<NodeIndex, Vec<VarDef>>,
        node_id: NodeIndex,
        inst_id: usize,
        var: &Variable,
    ) {
        let mut queue = VecDeque::new();
        let mut visit = HashSet::new();
        visit.insert((node_id, inst_id));
        queue.push_back((node_id, inst_id));
        while let Some(front) = queue.pop_front() {
            let (fr_node, fr_inst) = front;
            if (fr_node != node_id || fr_inst != inst_id) && fr_inst != usize::MAX {
                let defs = var_defs.get_mut(&fr_node).unwrap();
                if fr_inst < defs.len() {
                    let defs = &mut defs[fr_inst];
                    let entry = defs.entry(var.clone()).or_insert(Vec::new());
                    entry.push((node_id, inst_id));
                }
            }
            for next in Checker::next_instruction(graph, fr_node, fr_inst) {
                let next_node = graph.node_weight(next.0).unwrap().borrow();
                if next.1 < next_node.instructions.len()
                    && next_node.instructions[next.1].dvar == Some(var.clone())
                {
                    continue;
                }
                if !visit.contains(&next) {
                    visit.insert(next);
                    queue.push_back(next);
                }
            }
        }
    }

    fn next_instruction(
        graph: &ControlFlowGraph,
        node_id: NodeIndex,
        inst_id: usize,
    ) -> Vec<(NodeIndex, usize)> {
        let node = graph.node_weight(node_id).unwrap().borrow();
        if inst_id == usize::MAX {
            return vec![(node_id, 0)];
        }
        if inst_id < node.instructions.len() {
            return vec![(node_id, inst_id + 1)];
        }
        graph
            .neighbors_directed(node_id, petgraph::Outgoing)
            .map(|next| (next, 0))
            .collect()
    }

    fn get_dvar_new(&self, new_uvar: &Option<Variable>) -> HashSet<(NodeIndex, usize)> {
        let find_def = |var| {
            //println!("{:?}", var);
            *self.var_defs2.get(var).unwrap()
        };
        match new_uvar {
            None => HashSet::from_iter(vec![(self.entry, usize::MAX)]),
            Some(var) => {
                if self.phi_defs.contains_key(var) {
                    self.get_phi_def(var).iter().map(find_def).collect()
                } else {
                    HashSet::from_iter(vec![find_def(var)])
                }
            }
        }
    }
}
