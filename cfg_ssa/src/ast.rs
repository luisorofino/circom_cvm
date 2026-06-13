extern crate num_bigint_dig as num_bigint;

use num_bigint::BigInt;
use crate::types::*;

#[derive(Debug, Clone, PartialEq)]
pub enum ComponentCreationMode {
    Implicit,
    Explicit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AST {
    pub field: BigInt,
    pub signals_memory: usize,
    pub components_heap: usize,
    pub main_template: String,
    pub components_creation_mode: ComponentCreationMode,
    pub witness: Vec<usize>,
    pub inputs: Option<Vec<String>>,
    pub templates: Vec<Template>,
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub id: usize,
    pub name: String,
    pub inputs: Vec<(NumericType, Vec<usize>)>,
    pub output: Option<NumericType>,
    pub body: Vec<ASTNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Template {
    pub id: usize,
    pub name: String,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub signals: usize,
    pub components: Vec<usize>,
    pub body: Vec<ASTNode>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ASTNode {
    Operation {
        num_type: Option<NumericType>,
        operator: Option<Operator>,
        output: Option<String>,
        operands: Vec<Expression>,
    },
    IfThenElse {
        num_type: NumericType,
        condition: Expression,
        if_case: Vec<ASTNode>,
        else_case: Option<Vec<ASTNode>>,
    },
    Loop {
        body: Vec<ASTNode>,
    },
    Break,
    Continue,
}
