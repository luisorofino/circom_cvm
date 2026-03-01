pub mod ast;
pub mod types;
pub mod type_checking;
mod cfg_construction;
mod ssa_destruction;
mod tests;

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use ast::{Function, Template, AST};
use cfg_construction::CfgConstructor;

use serde::Serialize;

use crate::types::*;

fn replace_variable_in_expression(expr: &mut Expression, target: &str, replacement: &str) {
    match expr {
        Expression::Atomic(Atomic::Variable(v)) if v == target => {
            *v = replacement.to_string();
        }
        Expression::Atomic(_) => {}
        Expression::Parameter(param) => {
            let update_atomic = |a: &mut Atomic| {
                if let Atomic::Variable(v) = a {
                    if v == target {
                        *v = replacement.to_string();
                    }
                }
            };

            match param {
                Parameter::Signal { index, size }
                | Parameter::I64Memory { index, size }
                | Parameter::FfMemory { index, size } => {
                    update_atomic(index);
                    update_atomic(size);
                }
                Parameter::SubcmpSignal { component, index, size } => {
                    update_atomic(component);
                    update_atomic(index);
                    update_atomic(size);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct Value {
    pub(crate) operator: Option<Operator>,
    pub(crate) operands: Vec<Expression>,
}

#[derive(Clone, Serialize)]
pub struct Statement {
    pub(crate) num_type: Option<NumericType>,
    pub(crate) output: Option<String>,
    pub(crate) value: Value,
}

use std::fmt;
impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        if let Some(out) = &self.output {
            s.push_str(out);
            s.push_str(" = ");
        }
        if let Some(typ) = &self.num_type {
            s.push_str(match typ {
                NumericType::Integer => "i64.",
                NumericType::FiniteField => "ff."
            })
        }
        if let Some(op) = &self.value.operator {
            s.push_str(&format!("{:?} ", op).to_lowercase());
        }
        for op in self.value.operands.iter() {
            s.push_str(&format!("{:?} ", op));
        }
        write!(f, "{}", s)
    }
}


/// The list of possibilities are the name of the ssa variable and the block where it comes from
#[derive(Debug, Clone, Serialize)]
pub struct PhiPossibility {
    pub(crate) variable: String,
    pub(crate) block: usize,
}

#[derive(Clone, Serialize)]
pub struct PhiFunction {
    pub(crate) output: String,
    pub(crate) possibilities: Vec<PhiPossibility>,
}

impl fmt::Debug for PhiFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        s.push_str(&self.output);
        s.push_str(" = φ ");
        for phi in self.possibilities.iter() {
            s.push_str(&format!("{} (B{}), ", phi.variable, phi.block));
        }
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum Successor {
    Unconditional {
        to: usize,
    },
    Conditional {
        condition: Expression,
        to_then: usize,
        to_else: usize,
    },
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LineInstruction {
    pub(crate) is_phi: bool,
    pub(crate) line: usize,
}

type Stack<T> = Vec<T>;

#[derive(Debug, Serialize)]
pub struct BasicBlock {
    pub(crate) id: usize,
    pub(crate) phi_functions: Vec<PhiFunction>,
    pub(crate) statements: Vec<Statement>,
    pub(crate) predecessors: Vec<usize>,
    pub(crate) successors: Option<Successor>,
    ///Whether a variable is declared as a phi function and its position in the list of phi
    ///functions or statements accordingly
    pub(crate) declarations: BTreeMap<String, LineInstruction>,
    //Necessary data for liveness analysis
    ///Set with the variables that are used in phi functions in the successors of the block
    pub(crate) phi_uses: BTreeSet<String>,
    ///Set with the variables that are live in at the beginning of the block
    pub(crate) live_in: Stack<String>,
    ///Set with the variables that are live out at the end of the block
    pub(crate) live_out: Stack<String>,
}

impl BasicBlock {
    pub fn new(id: usize) -> Self {
        Self {
            id,
            phi_functions: Vec::new(),
            statements: Vec::new(),
            predecessors: Vec::new(),
            successors: None,
            declarations: BTreeMap::new(),
            phi_uses: BTreeSet::new(),
            live_in: Stack::new(),
            live_out: Stack::new(),
        }
    }

    /// Returns the position of the new PhiFunction
    fn add_phi_function(&mut self, phi: PhiFunction) -> LineInstruction {
        let line = LineInstruction { is_phi: true, line: self.phi_functions.len() };
        self.declarations.insert(phi.output.clone(), line.clone());
        self.phi_functions.push(phi);
        line
    }

    /// Returns the position of the new Statement
    pub(crate) fn add_instruction(&mut self, stmt: Statement) -> LineInstruction {
        let line = LineInstruction { is_phi: false, line: self.statements.len() };
        if let Some(output) = &stmt.output {
            self.declarations.insert(output.clone(), line.clone());
        }
        self.statements.push(stmt);
        line
    }

    /// Returns the declared variable in the instruction (if such variable exists)
    fn change_instruction_operands(&mut self, line: &LineInstruction, target: &str, replacement: &str) -> Option<String> {
        match line {
            LineInstruction { is_phi: true, line } => {
                let phi = self.phi_functions.get_mut(*line).expect("Missing phi function");
                for possibility in phi.possibilities.iter_mut() {
                    if possibility.variable == target {
                        possibility.variable = replacement.to_string();
                    }
                }
                Some(phi.output.clone())
            }
            LineInstruction { is_phi: false, line} => {
                let stmt = self.statements.get_mut(*line).expect("Missing statement");
                for op in stmt.value.operands.iter_mut() {
                    replace_variable_in_expression(op, target, replacement);
                }
                stmt.output.clone()
            }
        }
    }

    fn add_predecessor(&mut self, pred: usize) {
        self.predecessors.push(pred);
    }

    fn add_succesor(&mut self, suc: Successor) {
        self.successors = Some(suc);
    }

    fn change_condition(&mut self, target: &str, replacement: &str) {
        if let Some(Successor::Conditional { condition, to_then: _, to_else: _ }) = &mut self.successors {
            replace_variable_in_expression(condition, target, replacement);
        } else {
            panic!("Expected conditional successors");
        }
    }

    fn add_phi_use(&mut self, var: &str) {
        self.phi_uses.insert(var.to_string());
    }

    fn check_phi_use(&self, var: &str) -> bool {
        self.phi_uses.contains(var)
    }

    fn add_to_live_in(&mut self, v: &str) {
        self.live_in.push(v.to_string());
    }

    fn top_live_in(&self) -> Option<&String> {
        self.live_in.last()
    }

    fn add_to_live_out(&mut self, v: &str) {
        self.live_out.push(v.to_string());
    }

    fn top_live_out(&self) -> Option<&String> {
        self.live_out.last()
    }

}

#[derive(Debug, Clone, Serialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Use {
    /// Block and line in the block
    InInstruction(usize, LineInstruction),
    /// Block whose successor is conditional successor
    InCondition(usize),
}

#[derive(Default, Debug, Serialize)]
pub struct CFG {
    pub(crate) entry: usize,
    pub(crate) blocks: Vec<BasicBlock>,
    pub(crate) non_ssa_variables: usize,
    /// Key: Variable, Value: Block and line in that block where it is defined
    pub(crate) definitions: BTreeMap<String, (usize, LineInstruction)>,
    /// Key: Variable, Value: Set with all its uses
    pub(crate) def_use: BTreeMap<String, BTreeSet<Use>>,
}

impl CFG {
    pub fn new(entry: usize) -> Self {
        CFG { entry, blocks: vec![BasicBlock::new(entry)], non_ssa_variables: 0, definitions: BTreeMap::new(), def_use: BTreeMap::new() }
    }

    pub fn new_from_fun(f: Function) -> Result<Self, String> {
        let entry = 0;
        let mut cfg = CFG::new(entry);

        let mut constructor = CfgConstructor::new(&mut cfg);
        constructor.process_body(&f.body, entry, None)?;

        cfg.non_ssa_variables = constructor.get_non_ssa();

        cfg.compute_livesets_ssa_by_var()?;

        Ok(cfg)
    }

    pub fn new_from_template(t: Template) -> Result<Self, String> {
        let entry = 0;
        let mut cfg = CFG::new(entry);

        let mut constructor = CfgConstructor::new(&mut cfg);
        constructor.process_body(&t.body, entry, None)?;

        cfg.non_ssa_variables = constructor.get_non_ssa();

        cfg.compute_livesets_ssa_by_var()?;

        Ok(cfg)
    }

    pub fn add_phi_function(&mut self, block: usize, phi: PhiFunction) -> Result<LineInstruction, String> {
        let var = phi.output.clone();
        let line = self.blocks[block].add_phi_function(phi);
        //Add the variables to the phi uses of the predecessors
        //TODO: Consider avoiding cloning
        let preds = self.blocks[block].predecessors.clone();
        for pred in preds {
            self.blocks[pred].add_phi_use(&var);
        }
        if self.definitions.contains_key(&var) {
            // Check SSA property
            return Err(format!("Variable '{}' was defined twice", var));
        } else {
            self.definitions.insert(var, (block, line.clone()));
        }
        Ok(line)
    }

    pub fn add_instruction(&mut self, block: usize, stmt: Statement) -> Result<(), String> {
        let var = stmt.output.clone();
        let line = self.blocks[block].add_instruction(stmt);
        if let Some(output) = var {
            if self.definitions.contains_key(&output) {
                // Check SSA property
                return Err(format!("Variable '{}' was defined twice", output));
            } else {
                self.definitions.insert(output, (block, line));
            }
        }
        Ok(())
    }

    pub fn create_new_block(&mut self) -> usize {
        let id = self.blocks.len();
        let new_block = BasicBlock::new(id);
        self.blocks.push(new_block);

        id
    }

    pub fn check_empty_block(&self, block: usize) -> bool {
        self.blocks[block].statements.is_empty()
    }

    pub fn predecessors(&self, block: usize) -> &Vec<usize> {
        &self.blocks[block].predecessors
    }

    fn check_existing_successor(&self, block: usize) -> bool {
        self.blocks[block].successors.is_some()
    }

    pub fn add_uncond_link(&mut self, pred: usize, suc: usize) {
        //do not overwrite existing successors
        if !self.check_existing_successor(pred) {
            self.blocks[pred].add_succesor(Successor::Unconditional { to: suc });
            self.blocks[suc].add_predecessor(pred);
        }
    }

    pub fn add_cond_link(&mut self, pred: usize, condition: Expression, to_then: usize, to_else: usize) {
        //do not overwrite existing successors
        if !self.check_existing_successor(pred) {
            self.blocks[pred].add_succesor(Successor::Conditional { condition, to_then, to_else });
            self.blocks[to_then].add_predecessor(pred);
            self.blocks[to_else].add_predecessor(pred);
        }
    }

    pub fn get_entry(&self) -> usize {
        self.entry
    }

    fn track_use_instruction(&mut self, block: usize, target: String, line: LineInstruction) {
        self.def_use.entry(target).or_insert_with(BTreeSet::new).insert(Use::InInstruction(block, line));
    }

    fn track_use_condition(&mut self, block: usize, target: String) {
        self.def_use.entry(target).or_insert_with(BTreeSet::new).insert(Use::InCondition(block));
    }

    fn change_instruction_operands(&mut self, block: usize, line: &LineInstruction, target: &str, replacement: &str) -> Option<String> {
        let declared_var = self.blocks[block].change_instruction_operands(line, target, replacement);
        if let Some(uses) = self.def_use.get_mut(target) {
            uses.remove(&Use::InInstruction(block, line.clone()));
            if uses.is_empty() {
                self.def_use.remove(target);
            }
        }
        self.def_use.entry(replacement.to_string()).or_insert_with(BTreeSet::new).insert(Use::InInstruction(block, line.clone()));
        declared_var
    }

    fn change_condition_use(&mut self, block: usize, target: &str, replacement: &str) {
        if let Some(uses) = self.def_use.get_mut(target) {
            uses.remove(&Use::InCondition(block));
            if uses.is_empty() {
                self.def_use.remove(target);
            }
        }
        self.def_use.entry(replacement.to_string()).or_insert_with(BTreeSet::new).insert(Use::InCondition(block));
        self.blocks[block].change_condition(target, replacement);
    }

    ///Liveness analysis
    ///Taken from Domaine, & Brandner, Florian & Boissinot, Benoit & Darte, Alain & Dinechin, Benoît & Rastello, Fabrice. (2011). Computing Liveness Sets for SSA-Form Programs.
    fn compute_livesets_ssa_by_var(&mut self) -> Result<(), String> {
        for (var, uses) in &self.def_use {
            //Compute which blocks are dominated by the definition
            let (def_block, _) = match self.definitions.get(var) {
                Some(def) => def,
                None => return Err(format!("Variable {var} was used, but not defined!")),
            };
            let on_path = Self::on_path_from_def(&self.blocks, *def_block);

            for u in uses {
                match u {
                    Use::InCondition(block) |
                    Use::InInstruction(block, _)
                    => {
                        if self.blocks[*block].check_phi_use(var) {
                            self.blocks[*block].add_to_live_out(var);
                        }

                        let def_v = self.definitions.get(var).unwrap_or_else(|| {
                            panic!("Variable {var} was used, but not defined!")
                        });

                        if !on_path.contains(block) {
                            return Err(format!("Variable {var} was used without being dominated by its definition"));
                        }
                        Self::up_and_mark(&mut self.blocks, *block, var, def_v, &on_path);
                    }
                }
            }
        }

        Ok(())
    }

    ///Returns a list with all the blocks that the origin_block can reach through a bfs
    fn on_path_from_def(blocks: &Vec<BasicBlock>, origin_block: usize) -> BTreeSet<usize> {
        let mut reachable = BTreeSet::new();
        let mut queue = VecDeque::new();

        queue.push_back(origin_block);
        reachable.insert(origin_block);

        while let Some(current) = queue.pop_front() {
            if let Some(succ) = &blocks[current].successors {
                match succ {
                    Successor::Unconditional { to } => {
                        if reachable.insert(*to) {
                            queue.push_back(*to);
                        }
                    }
                    Successor::Conditional { to_then, to_else, .. } => {
                        if reachable.insert(*to_then) {
                            queue.push_back(*to_then);
                        }
                        if reachable.insert(*to_else) {
                            queue.push_back(*to_else);
                        }
                    }
                }
            }
        }

        reachable
    }

    ///Returns whether the definition reaches the use
    //TODO: Check inside a block (the line of the use is after the definition)
    fn up_and_mark(blocks: &mut Vec<BasicBlock>, block: usize, var: &str, def_v: &(usize, LineInstruction), on_path: &BTreeSet<usize>) {
        //Defined in the block (not phi) or propagation already done -> Stop
        if def_v.0 == block && !def_v.1.is_phi {
            return;
        }

        //We have gone though this block in a previous dfs
        if let Some(top_live_in) = blocks[block].top_live_in() {
            if var == top_live_in {
                return;
            }
        }

        blocks[block].add_to_live_in(var);

        if def_v.0 == block /*  && def_v.1.is_phi */ {
            return;
        }

        //TODO: Avoid cloning
        let preds = blocks[block].predecessors.clone();
        for pred in preds {
            if !on_path.contains(&pred) {
                //The predecessor does not reach the definition → not live
                continue;
            }

            if let Some(top_v) = blocks[pred].top_live_out() {
                if top_v != var {
                    blocks[pred].add_to_live_out(var);
                }
            }
            else {
                blocks[pred].add_to_live_out(var);
            }

            Self::up_and_mark(blocks, pred, var, def_v, on_path);
        }
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }

    pub fn to_dot(&self, id: usize) -> String {
        // helper: only escape quotes, leave \n alone
        fn esc(s: &str) -> String {
            s.replace('"', "\\\"")
        }

        let mut dot = String::new();
        dot.push_str(&format!("digraph G{} {{\n", id));

        for block in &self.blocks {
            // 1) collect one line per statement (with Debug)
            let mut lines = Vec::new();
            lines.push(format!("Block {}", block.id));
            
            lines.push(format!("Live in: {:?}", &block.live_in));

            for phi in &block.phi_functions {
                lines.push(format!("{:?}", phi));
            }

            for stmt in &block.statements {
                lines.push(format!("{:?}", stmt));
            }

            lines.push(format!("Live out: {:?}", &block.live_out));

            // 2) join with "\n"
            let raw_label = lines.join("\n");
            // 3) escape only quotes
            let label = esc(&raw_label);

            dot.push_str(&format!(
                    "  {} [label=\"{}\", shape=box];\n",
                    block.id, label
            ));

            // edges
            if let Some(succ) = &block.successors {
                match succ {
                    Successor::Unconditional { to } => {
                        dot.push_str(&format!("  {} -> {};\n", block.id, to));
                    }
                    Successor::Conditional { condition, to_then, to_else } => {
                        let cond = esc(&format!("{:?}", condition));
                        dot.push_str(&format!(
                                "  {} -> {} [label=\"{} != 0\"];\n",
                                block.id, to_then, cond
                        ));
                        dot.push_str(&format!("  {} -> {} [label=\"{} == 0\"];\n",
                                block.id, to_else, cond));
                    }
                }
            }
        }


        let mut du_lines = Vec::new();
        du_lines.push("Def-Use Chains".to_string());
        for (var, uses) in &self.def_use {
            // render each use as "BID:L(φ?)" or "BID:cond"
            let locs: Vec<String> = uses.iter().map(|u| {
                match u {
                    Use::InInstruction(bid, inst) => {
                        if inst.is_phi {
                            format!("{}:{}(φ)", bid, inst.line)
                        }
                        else {
                            format!("{}:{}", bid, inst.line + self.blocks.get(*bid).unwrap().phi_functions.len())
                        }
                        // format!("{}:{}", bid, inst.line) +
                        // if inst.is_phi { "(φ)" } else { "" }
                    }
                    Use::InCondition(bid) => {
                        format!("{bid}:c")
                    }
                }
            }).collect();

            du_lines.push(format!("{} → {}", var, locs.join(", ")));
        }
        // join lines with Graphviz left‑justified line breaks (\l)
        let du_label = esc(&du_lines.join("\\l")) + "\\l";

        // emit a single box with id "DU"
        dot.push_str(&format!(
            "  DU [shape=box, label=\"{}\"];\n",
            du_label
        ));

        // Variable definitions
        // Collect all definitions in a single box with id "DEF"
        // Each definition is "var → BID:line(φ?)"
        let mut def_lines = Vec::new();
        def_lines.push("Definitions".to_string());
        for (var, (bid, inst)) in &self.definitions {
            let suffix = if inst.is_phi { "(φ)" } else { "" };
            def_lines.push(format!(
                "{} → {}:{}{}",
                var,
                bid,
                inst.line,
                suffix
            ));
        }
        let def_label = esc(&def_lines.join("\\l")) + "\\l";

        dot.push_str(&format!(
            "  DEF [shape=box, label=\"{}\"];\n",
            def_label
        ));

        dot.push_str("}\n");
        dot
    }

    pub fn to_dot_destruction(&self, id: usize) -> String {
        fn esc(s: &str) -> String {
            s.replace('"', "\\\"")
        }

        let mut dot = String::new();
        dot.push_str(&format!("digraph G{} {{\n", id));

        for block in &self.blocks {
            let mut lines = Vec::new();
            lines.push(format!("Block {}", block.id));

            for phi in &block.phi_functions {
                lines.push(format!("{:?}", phi));
            }

            for stmt in &block.statements {
                lines.push(format!("{:?}", stmt));
            }

            let raw_label = lines.join("\n");
            let label = esc(&raw_label);

            dot.push_str(&format!(
                    "  {} [label=\"{}\", shape=box];\n",
                    block.id, label
            ));

            if let Some(succ) = &block.successors {
                match succ {
                    Successor::Unconditional { to } => {
                        dot.push_str(&format!("  {} -> {};\n", block.id, to));
                    }
                    Successor::Conditional { condition, to_then, to_else } => {
                        let cond = esc(&format!("{:?}", condition));
                        dot.push_str(&format!(
                                "  {} -> {} [label=\"{} != 0\"];\n",
                                block.id, to_then, cond
                        ));
                        dot.push_str(&format!("  {} -> {} [label=\"{} == 0\"];\n",
                                block.id, to_else, cond));
                    }
                }
            }
        }

        dot.push_str("}\n");
        dot
    }

    fn get_block_size(&self, block: usize) -> usize {
        self.blocks[block].statements.len()
    }
}

#[derive(Default, Debug, Serialize)]
pub struct CFGList {
    entry: usize,
    cfgs: Vec<CFG>,
}

impl CFGList {
    pub fn new(ast: AST) -> Result<Self, String> {
        let mut cfgs = Vec::new();
        let mut entry = 0;

        //CFGs for functions
        for f in ast.functions {
            cfgs.push(CFG::new_from_fun(f)?);
        }

        //CFGs for templates
        for t in ast.templates {
            if t.name == ast.main_template {
                entry = cfgs.len();
            }
            cfgs.push(CFG::new_from_template(t)?);
        }

        Ok(Self { entry, cfgs })
    }

    pub fn destroy_ssa_all(&mut self) {
        for cfg in &mut self.cfgs {
            cfg.destroy_ssa();
        }
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }

    pub fn to_dot(&self) -> Vec<String> {
        self.cfgs.iter().enumerate().map(|(id, cfg)| cfg.to_dot(id)).collect()
    }

    pub fn to_dot_destruction(&self) -> Vec<String> {
        self.cfgs.iter().enumerate().map(|(id, cfg)| cfg.to_dot_destruction(id)).collect()
    }

    ///Returns: num_cfgs, avg_blocks_per_cfg, avg_non_ssa_variables_per_cfg, avg_ssa_variables_per_cfg, avg_stmts_per_block
    pub fn get_metrics(&self) -> (usize, f64, f64, f64, f64) {
        let mut num_blocks: usize = 0;
        let mut num_non_ssa_variables: usize = 0;
        let mut num_ssa_variables: usize = 0;
        let mut total_stmts: usize = 0;

        for cfg in &self.cfgs {
            num_blocks += cfg.blocks.len();
            num_ssa_variables += cfg.definitions.len();
            num_non_ssa_variables += cfg.non_ssa_variables;
            for block in &cfg.blocks {
                total_stmts += block.phi_functions.len();
                total_stmts += block.statements.len();
            }
        }

        fn safe_div(numerator: usize, denominator: usize) -> f64 {
            if denominator == 0 {
                0.0
            } else {
                numerator as f64 / denominator as f64
            }
        }

        let avg_blocks_per_cfg = safe_div(num_blocks, self.cfgs.len());
        let avg_non_ssa_variables_per_cfg = safe_div(num_non_ssa_variables, self.cfgs.len());
        let avg_ssa_variables_per_cfg = safe_div(num_ssa_variables, self.cfgs.len());
        let avg_stmts_per_block = safe_div(total_stmts, num_blocks);

        (
            self.cfgs.len(),
            avg_blocks_per_cfg,
            avg_non_ssa_variables_per_cfg,
            avg_ssa_variables_per_cfg,
            avg_stmts_per_block,
        )
    }
}
