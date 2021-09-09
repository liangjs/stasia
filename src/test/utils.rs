use std::cell::RefCell;

use crate::{CFGNode, DefUseVars, CFG};

pub type Graph = petgraph::stable_graph::StableDiGraph<RefCell<Node>, petgraph::Directed>;

impl CFG for &Graph {
    type Node = Node;
}

pub struct Node {
    pub instructions: Vec<Instruction>,
    pub phi_vars: Vec<PhiVar>,
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

pub struct PhiVar {
    pub src: Vec<Variable>,
    pub dst: Variable,
}

pub struct Instruction {
    pub dvar: Option<Variable>,
    pub uvars: Vec<Variable>,
    pub new_dvar: Option<Variable>,
    pub new_uvar: Vec<Option<Variable>>,
}

impl Instruction {
    pub fn new(dvar: Option<Variable>, uvars: Vec<Variable>) -> Instruction {
        let num = uvars.len();
        Instruction {
            dvar,
            uvars,
            new_dvar: None,
            new_uvar: vec![None; num],
        }
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
                self.new_uvar[i] = Some(new_var.clone());
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    pub name: String,
    pub id: usize,
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
