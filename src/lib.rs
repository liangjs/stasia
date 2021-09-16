use petgraph::graph::NodeIndex;
use petgraph::{data as graph_data, visit as graph_visit};
use std::collections::HashMap;
use std::hash::Hash;

pub trait Variable
where
    Self: Hash + Clone + Eq,
{
}

pub trait DefUseVars {
    type Variable: Variable;
    fn defined_var(&self) -> Option<Self::Variable>;
    fn used_vars(&self) -> Vec<Self::Variable>;
}

pub trait CFGNode<'a> {
    type Variable: Variable;
    type Instruction: DefUseVars<Variable = Self::Variable> + 'a;
    type InstIter: Iterator<Item = &'a Self::Instruction>;
    fn instructions(&'a self) -> Self::InstIter;
}

pub trait CFG<Node>
where
    Self: graph_visit::GraphBase<NodeId = NodeIndex>,
    Self: graph_visit::Data<NodeWeight = Node>,
    Self: graph_visit::GraphProp<EdgeType = petgraph::Directed>,
    Self: graph_visit::IntoNeighborsDirected,
    Self: graph_visit::IntoNodeReferences,
    Self: graph_visit::Visitable,
    Self: graph_data::DataMap,
    Node: for<'a> CFGNode<'a>,
{
}

/// var_dst = phi(var_src)
pub struct PhiStmt<Var: Variable> {
    pub var: Var,
    pub src: Vec<usize>,
    pub dst: usize,
}

/// def_var = op(use_vars)
pub struct InstStmt<Var: Variable> {
    pub def_var: Option<usize>,
    pub use_vars: HashMap<Var, usize>,
}

pub struct SSA<Var: Variable> {
    pub phi: Vec<PhiStmt<Var>>,
    pub inst: Vec<InstStmt<Var>>,
}

mod ssa;

pub fn ssa_analysis<Graph, Node, Var>(
    graph: Graph,
    entry: NodeIndex,
) -> HashMap<NodeIndex, SSA<Var>>
where
    Graph: CFG<Node>,
    Var: Variable,
    Node: for<'a> CFGNode<'a, Variable = Var>,
{
    ssa::Analyser::analysis(graph, entry)
}

#[cfg(test)]
mod test;
