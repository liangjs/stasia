use petgraph::graph::NodeIndex;
use petgraph::{data as graph_data, visit as graph_visit};
use std::cell::RefCell;
use std::hash::Hash;

pub trait Variable
where
    Self: Hash + Clone + Eq,
{
    /// Create a series of new variables.
    /// The original variable (`self`) is still valid.
    fn split(&self, num: usize) -> Vec<Self>;
}

pub trait DefUseVars {
    type Variable: Variable;
    fn defined_var(&self) -> Option<Self::Variable>;
    fn used_vars(&self) -> Vec<Self::Variable>;
    fn replace_def_var(&mut self, new_var: Self::Variable);
    fn replace_use_var(&mut self, old_var: &Self::Variable, new_var: Self::Variable);
}

pub trait CFGNode<'a> {
    type Variable: Variable;
    type Instruction: DefUseVars<Variable = Self::Variable> + 'a;
    type InstIter: Iterator<Item = &'a Self::Instruction>;
    type InstIterMut: Iterator<Item = &'a mut Self::Instruction>;
    fn instructions(&'a self) -> Self::InstIter;
    fn instructions_mut(&'a mut self) -> Self::InstIterMut;
    fn prepend_phi(&mut self, src: Vec<Self::Variable>, dst: Self::Variable);
}

pub trait CFG
where
    Self: graph_visit::GraphBase<NodeId = NodeIndex>,
    Self: graph_visit::Data<NodeWeight = RefCell<Self::Node>>,
    Self: graph_visit::GraphProp<EdgeType = petgraph::Directed>,
    Self: graph_visit::IntoNeighborsDirected,
    Self: graph_visit::IntoNodeReferences,
    Self: graph_visit::Visitable,
    Self: graph_data::DataMap,
{
    type Node: for<'a> CFGNode<'a>;
}

mod ssa;
use ssa::SSA;

pub fn ssa_analysis<Graph, Var>(graph: Graph, entry: NodeIndex)
where
    Graph: CFG,
    Var: Variable,
    <Graph as CFG>::Node: for<'a> CFGNode<'a, Variable = Var>,
{
    SSA::<Graph, Var>::analysis(graph, entry);
}

#[cfg(test)]
mod test;
