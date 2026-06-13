use std::collections::{BTreeMap, BTreeSet};

use crate::{ast::ASTNode, types::{Atomic, Expression, Operator, Parameter}, LineInstruction, PhiPossibility, Statement, Use, Value, CFG};

//TODO: These uses are duplicated in lib.rs, the problem is InMemoization which is neccesary when removing trivial phis
//but it is not when we have the final CFG.
/// Enum to represent the possible uses:
#[derive (Eq, Hash, PartialEq, Clone, Ord, PartialOrd)]
enum UseTemp {
    /// - In memoization (the block has written in its definitions this variable)
    InMemoization(usize),
    /// - In block (the block uses the variable in one of its instructions)
    InBlock(Use),
}

/// A SSA-based CFG builder
pub struct CfgConstructor<'a> {
    cfg: &'a mut CFG,

    /// Save for each block the definition of the variables it contains (the new name)
    /// Old name → SSA name
    definitions: Vec<BTreeMap<String, String>>,

    /// SSA name of the phi → List of possible values it can have depending on the execution
    phis: BTreeMap<String, Vec<PhiPossibility>>,

    /// Current SSA values: ssa name -> original name
    to_non_ssa: BTreeMap<String, String>,

    /// Tracks unfinished φ-nodes per block (tracked variable and its φ-node)
    incomplete_phis: Vec<BTreeSet<(String, String)>>,

    /// For each variable, we save a set of blocks where it is used and how
    uses: BTreeMap<String, BTreeSet<UseTemp>>,

    /// We keep track of the blocks that lead to exceptions (i.e., errors)
    exception_blocks: BTreeSet<usize>,

    /// Non-ssa names, to count the number of original variables
    non_ssa_names: BTreeSet<String>,

    sealed_blocks: Vec<bool>,
    next_ssa_num: usize,
}


impl<'a> CfgConstructor<'a> {
    pub fn new(cfg: &'a mut CFG) -> Self {
        Self {
            cfg,
            definitions: vec![BTreeMap::new()],
            phis: BTreeMap::new(),
            to_non_ssa: BTreeMap::new(),
            incomplete_phis: vec![BTreeSet::new()],
            uses: BTreeMap::new(),
            exception_blocks: BTreeSet::new(),
            non_ssa_names: BTreeSet::new(),
            sealed_blocks: vec![true],
            next_ssa_num: 0,
        }
    }

    /// Create a new block for the cfg, but, at the same time, increase the size of the block
    /// variable definition
    /// Returns position of block
    fn create_block(&mut self) -> usize {
        self.definitions.push(BTreeMap::new());
        self.incomplete_phis.push(BTreeSet::new());
        self.sealed_blocks.push(false);
        self.cfg.create_new_block()
    }

    /// Create a fresh SSA name
    /// Returns ssa name
    fn fresh(&mut self) -> String {
        //TODO: The ssa name could just be a number, no need of string
        let ssa_name = format!("v{:03}", self.next_ssa_num);
        self.next_ssa_num += 1;
        ssa_name
    }

    /// Seal a block: finish φ-nodes
    fn seal_block(&mut self, block: usize) -> Result<(), String> {
        let pending_phis = std::mem::take(&mut self.incomplete_phis[block]);
        for (non_ssa_name, ssa_phi_name) in pending_phis {
            self.add_phi_operands(&non_ssa_name, &ssa_phi_name, block)?;
        }
        self.sealed_blocks[block] = true;
        Ok(())
    }

    /// Write a new SSA binding for source `src` in `block` with `val`
    /// Returns ssa name
    fn write_variable(&mut self, non_ssa_name: &str, block: usize) -> String {
        if !self.non_ssa_names.contains(non_ssa_name) {
            self.non_ssa_names.insert(non_ssa_name.to_string());
        }
        let ssa_name = self.fresh();
        self.to_non_ssa.insert(ssa_name.clone(), non_ssa_name.to_string());
        self.definitions[block].insert(non_ssa_name.to_string(), ssa_name.clone());
        ssa_name
    }

    /// Write a new empty phi function for source `src` in `block`
    fn write_phi_function(&mut self, non_ssa_name: &str, block: usize) -> String {
        if !self.non_ssa_names.contains(non_ssa_name) {
            self.non_ssa_names.insert(non_ssa_name.to_string());
        }
        let ssa_name = self.fresh();
        self.phis.insert(ssa_name.clone(), Vec::new());
        self.to_non_ssa.insert(ssa_name.clone(), non_ssa_name.to_string());
        self.definitions[block].insert(non_ssa_name.to_string(), ssa_name.clone());
        ssa_name
    }

    /// Read a variable, inserting φ if needed
    /// Returns ssa name
    fn read_variable(&mut self, non_ssa_name: &str, block: usize) -> Result<String, String> {
        if let Some(ssa_name) = self.definitions[block].get(non_ssa_name) {
            return Ok(ssa_name.clone());
        }
        self.read_recursive(non_ssa_name, block)
    }

    /// Recursively tries to read a variable, inserting φ if needed
    /// Returns ssa name
    fn read_recursive(&mut self, non_ssa_name: &str, block: usize) -> Result<String, String> {
        if !self.sealed_blocks[block] {
            // Incomplete block: create φ placeholder
            let ssa_phi_name = self.write_phi_function(non_ssa_name, block);
            self.incomplete_phis[block].insert((non_ssa_name.to_string(), ssa_phi_name.clone()));
            return Ok(ssa_phi_name);
        }

        let predecessors = self.cfg.predecessors(block);

        // Single predecessor -> no φ needed
        if predecessors.len() == 1 {
            let v = self.read_variable(non_ssa_name, predecessors[0])?;

            // Don't write_variable because it creates a new SSA name

            // Avoid the recursive lookup in future cases
            self.definitions[block].insert(non_ssa_name.to_string(), v.clone());
            let usage = UseTemp::InMemoization(block);
            self.uses.entry(v.clone()).or_default().insert(usage);

            return Ok(v);
        }

        // Multiple predecessors -> φ
        // Break potential cycles with operandless phi
        let ssa_phi_name = self.write_phi_function(non_ssa_name, block);
        self.add_phi_operands(non_ssa_name, &ssa_phi_name, block)?;

        // In case phi is trivial, we read again
        self.read_variable(non_ssa_name, block)
    }

    /// Add φ operands from all predecessors for `name` in `block`
    fn add_phi_operands(&mut self, non_ssa_name: &str, ssa_phi_name: &str, block: usize) -> Result<(), String> {
        let mut operands = Vec::new();
        let predecessors: Vec<_> = self.cfg.predecessors(block).to_vec();

        for &pred in &predecessors {
            let operand = self.read_variable(non_ssa_name, pred)?;
            operands.push((operand.clone(), pred));
        }
        let phi_operation = match self.phis.get_mut(ssa_phi_name) {
            Some(op) => op,
            None => return Err(format!("Phi node '{}' missing", ssa_phi_name)),
        };
        phi_operation.extend(
            operands
                .into_iter()
                .map(|(variable, block)| PhiPossibility { variable, block })
        );

        let phi_operation = phi_operation.clone();
        if !self.try_remove_trivial(ssa_phi_name, non_ssa_name, block) {
            let phi = crate::PhiFunction { output: ssa_phi_name.to_string(), possibilities: phi_operation.clone() };
            let line = self.cfg.add_phi_function(block, phi)?;

            for op in phi_operation {
                self.track_use_instruction(&Expression::Atomic(Atomic::Variable(op.variable.to_string())), block, line.clone());
            }
        }

        Ok(())
    }

    /// Simplify trivial φ-nodes with identical operands
    /// Returns whether the 
    fn try_remove_trivial(&mut self, ssa_phi_name: &str, non_ssa_name: &str, block: usize) -> bool {
        let possibilities = match self.phis.get(ssa_phi_name) {
            Some(v) => v.clone(),
            _ => return false,
        };
        let mut repeated_operand: Option<String> = None;
        for pos in possibilities.iter() {
            if pos.variable == ssa_phi_name { continue; }   //Self reference
            if let Some(r) = &repeated_operand {
                //The phi merges at least two different values: not trivial
                if *r != pos.variable { return false; }
            }
            repeated_operand = Some(pos.variable.clone());
        }

        if let Some(repeated_op_name) = repeated_operand {
            if let Some(users) = self.uses.remove(ssa_phi_name) {
                for user in users {
                    match user {
                        UseTemp::InMemoization(block_u) => {
                            self.definitions[block_u].insert(non_ssa_name.to_string(), repeated_op_name.clone());
                        }
                        UseTemp::InBlock(Use::InCondition(block_u)) => {
                            self.cfg.change_condition_use(block_u, ssa_phi_name, &repeated_op_name);
                        }
                        UseTemp::InBlock(Use::InInstruction(block_u, line_instruction)) => {
                            let declared_var = self.cfg.change_instruction_operands(block_u, &line_instruction, ssa_phi_name, &repeated_op_name);

                            if let Some(user_ssa_name) = declared_var {
                                let non_ssa_name = self.to_non_ssa.get(&user_ssa_name).expect("Declaration not found").to_string();

                                //TODO: Possibly we need to remove the phi from the block if it has
                                //been written
                                let _ = self.try_remove_trivial(&user_ssa_name, &non_ssa_name, block_u);
                            }
                        }
                    }
                }
            }
            self.definitions[block].insert(non_ssa_name.to_string(), repeated_op_name.clone());
            let usage = UseTemp::InMemoization(block);
            self.uses.entry(repeated_op_name.clone()).or_default().insert(usage);

            self.phis.remove(ssa_phi_name);
            self.to_non_ssa.remove(ssa_phi_name);
        }
        //TODO: Case of same is None is impossible?

        true
    }

    fn read_expression(&mut self, op: &Expression, block: usize) -> Result<Expression, String> {
        match op {
            Expression::Atomic(Atomic::Variable(var)) => {
                Ok(Expression::Atomic(Atomic::Variable(self.read_variable(var, block)?)))
            }
            Expression::Atomic(atomic) => Ok(Expression::Atomic(atomic.clone())),
            Expression::Parameter(param) => {
                let mut new_param = param.clone();
                let mut update_atomic = |a: &mut Atomic| -> Result<(), String> {
                    if let Atomic::Variable(var) = a {
                        *var = self.read_variable(var, block)?;
                    }
                    Ok(())
                };

                match &mut new_param {
                    Parameter::Signal { index, size }
                    | Parameter::I64Memory { index, size }
                    | Parameter::FfMemory { index, size } => {
                        update_atomic(index)?;
                        update_atomic(size)?;
                    }
                    Parameter::SubcmpSignal { component, index, size } => {
                        update_atomic(component)?;
                        update_atomic(index)?;
                        update_atomic(size)?;
                    }
                }
                Ok(Expression::Parameter(new_param))
            }
        }
    }

    /// Process AST nodes into CFG, returning the last block
    /// loop_blocks: (entry, exit)
    pub fn process_body(&mut self, body: &[ASTNode], mut curr: usize, loop_blocks: Option<(usize, usize)>) -> Result<usize, String> {
        for stmt in body {
            curr = match stmt {
                ASTNode::Operation { num_type, operator, output, operands } => {
                    if let Some(Operator::Error) = operator {
                        let new_curr = self.handle_operation(curr, num_type, operator, output, operands)?;
                        self.exception_blocks.insert(new_curr);
                        return Ok(new_curr);
                    }
                    self.handle_operation(curr, num_type, operator, output, operands)?
                }
                ASTNode::Loop { body: loop_body } => self.handle_loop(loop_body, curr)?,
                ASTNode::IfThenElse { num_type, condition, if_case, else_case } => {
                    let cond = self.read_expression(condition, curr)?;
                    self.track_use_condition(&cond, curr)?;
                    self.handle_if(num_type, &cond, if_case, else_case, curr, loop_blocks)?
                }
                ASTNode::Break => {
                    let out = loop_blocks.expect("break outside loop").1;
                    self.cfg.add_uncond_link(curr, out);
                    break;
                }
                ASTNode::Continue => {
                    let entry = loop_blocks.expect("continue outside loop").0;
                    self.cfg.add_uncond_link(curr, entry);
                    break;
                }
            };
        }

        Ok(curr)
    }


    fn track_use_instruction(&mut self, used: &Expression, block: usize, line: LineInstruction) {
        let usage = UseTemp::InBlock(Use::InInstruction(block, line.clone()));
        if let Expression::Atomic(Atomic::Variable(var)) = used {
            self.uses.entry(var.clone()).or_default().insert(usage);
            self.cfg.track_use_instruction(block, var.clone(), line);
        } else if let Expression::Parameter(param) = used {
            let mut track_atomic = |a: &Atomic| {
                if let Atomic::Variable(var) = a {
                    self.uses.entry(var.clone()).or_default().insert(usage.clone());
                    self.cfg.track_use_instruction(block, var.clone(), line.clone());
                }
            };

            match param {
                Parameter::Signal { index, size }
                | Parameter::I64Memory { index, size }
                | Parameter::FfMemory { index, size } => {
                    track_atomic(index);
                    track_atomic(size);
                }

                Parameter::SubcmpSignal { component, index, size } => {
                    track_atomic(component);
                    track_atomic(index);
                    track_atomic(size);
                }
            }
        }
    }

    fn track_use_condition(&mut self, op: &Expression, block: usize) -> Result<(), String> {
        let usage = UseTemp::InBlock(Use::InCondition(block));
        if let Expression::Atomic(Atomic::Variable(var)) = op {
            self.uses.entry(var.clone()).or_default().insert(usage);
            self.cfg.track_use_condition(block, var.clone());
        }
        else if let Expression::Parameter(_) = op {
            return Err("The condition of a branch cannot be a parameter for a function".to_string());
        }
        Ok(())
    }

    fn handle_operation(
        &mut self, curr: usize,
        num_type: &Option<crate::types::NumericType>,
        operator: &Option<crate::types::Operator>,
        output: &Option<String>,
        operands: &Vec<Expression>,
    ) -> Result<usize, String> {
        let mut ops = Vec::new();
        for op in operands {
            ops.push(self.read_expression(op, curr)?);
        }

        let pos = self.cfg.get_block_size(curr);
        for op in &ops {
            self.track_use_instruction(op, curr, LineInstruction { is_phi: false, line: pos });
        }

        let val = Value { operator: operator.clone(), operands: ops };

        let var = output.as_ref().map(|v|
                                  self.write_variable(v, curr));

        let stmt = Statement { num_type: num_type.clone(), output: var, value: val };
        self.cfg.add_instruction(curr, stmt)?;

        Ok(curr)
    }

    /// Helper: create a new block and link from `curr`
    fn create_and_link(&mut self, curr: usize) -> usize {
        let b = self.create_block();
        self.cfg.add_uncond_link(curr, b);
        b
    }

    fn handle_loop(&mut self, loop_body: &[ASTNode], curr: usize) -> Result<usize, String> {
        // Add new block for the loop body (if the current is not empty)
        let entry = self.create_and_link(curr);

        // Add new block for the instructions after the loop
        let after = self.create_block();

        // The block that will be the last one in the loop
        let last = self.process_body(loop_body, entry, Some((entry, after)))?;
        if !self.cfg.predecessors(last).is_empty() && !self.exception_blocks.contains(&last) {
            self.cfg.add_uncond_link(last, after);
        }

        // Seal the blocks
        self.seal_block(entry)?;
        self.seal_block(after)?;

        // Continue after the loop
        Ok(after)
    }

    fn handle_if(
        &mut self,
        num_type: &crate::types::NumericType,
        condition: &Expression,
        if_case: &[ASTNode],
        else_case: &Option<Vec<ASTNode>>,
        curr: usize,
        loop_blocks: Option<(usize, usize)>,
    ) -> Result<usize, String> {
        // If body
        let then_b = self.create_block();

        // Convergence block
        // TODO: Create this always or only when there are more instructions?
        let join = self.create_block();

        // Add else block (optional)
        let else_b = if else_case.is_some() { self.create_block() }
                            else { join };

        // Link current block with the then and else blocks
        self.cfg.add_cond_link(curr, num_type.clone(), condition.clone(), then_b, else_b);

        // Seal the blocks that start then and else
        self.seal_block(then_b)?;
        // Ensure the join is not accidentally sealed
        if else_case.is_some() {
            self.seal_block(else_b)?;
        }

        // Process then case
        let end_then = self.process_body(if_case, then_b, loop_blocks)?;
        if !self.exception_blocks.contains(&end_then) {
            self.cfg.add_uncond_link(end_then, join);
        }

        if let Some(else_stmts) = else_case {
            let end_else = self.process_body(else_stmts, else_b, loop_blocks)?;
            if !self.exception_blocks.contains(&end_else) {
                self.cfg.add_uncond_link(end_else, join);
            }
        }

        // Seal join
        self.seal_block(join)?;

        Ok(join)
    }

    pub(crate) fn get_non_ssa(&self) -> usize {
        self.non_ssa_names.len()
    }

    //TODO
    // pub fn remove_unreachable_blocks(&mut self) {
    //     todo!();
    // }
}

#[cfg(test)]
mod tests {
    use num_bigint_dig::BigInt;

    use crate::{ast::Template, types::*};

    use super::*;

    #[test]
    fn test_simple_ast() {
        let template = Template {
            id: 0,
            name: "template_0".to_string(),
            outputs: vec!["output".to_string()],
            inputs: vec!["input1".to_string(), "input2".to_string()],
            signals: 10,
            components: vec![5, 3, 2],
            body: vec![
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: None,
                    output: Some("x".to_string()),
                    operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::FF(BigInt::from(1))))],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: None,
                    output: Some("y".to_string()),
                    operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::FF(BigInt::from(10))))],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: None,
                    output: Some("z".to_string()),
                    operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::FF(BigInt::from(9))))],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: Some(Operator::Add),
                    output: Some("a".to_string()),
                    operands: vec![
                        Expression::Atomic(Atomic::Variable("y".to_string())),
                        Expression::Atomic(Atomic::Variable("z".to_string())),
                    ],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: None,
                    output: Some("condition".to_string()),
                    operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::I64(1)))],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: None,
                    output: Some("loop_condition".to_string()),
                    operands: vec![Expression::Atomic(Atomic::Constant(ConstantType::I64(1)))],
                },
                ASTNode::IfThenElse {
                    num_type: NumericType::Integer,
                    condition: Expression::Atomic(Atomic::Variable("condition".to_string())),
                    if_case: vec![
                        ASTNode::Operation {
                            num_type: Some(NumericType::FiniteField),
                            operator: Some(Operator::Sub),
                            output: Some("x".to_string()),
                            operands: vec![
                                Expression::Atomic(Atomic::Variable("x".to_string())),
                                Expression::Atomic(Atomic::Variable("y".to_string())),
                            ],
                        },
                    ],
                    else_case: None,
                },
                ASTNode::Loop {
                    body: vec![
                        ASTNode::Operation {
                            num_type: Some(NumericType::FiniteField),
                            operator: Some(Operator::Mul),
                            output: Some("b".to_string()),
                            operands: vec![
                                Expression::Atomic(Atomic::Variable("x".to_string())),
                                Expression::Atomic(Atomic::Variable("z".to_string())),
                            ],
                        },
                        ASTNode::IfThenElse {
                            num_type: NumericType::Integer,
                            condition: Expression::Atomic(Atomic::Variable("loop_condition".to_string())),
                            if_case: vec![
                                ASTNode::Operation {
                                    num_type: Some(NumericType::FiniteField),
                                    operator: Some(Operator::Div),
                                    output: Some("c".to_string()),
                                    operands: vec![
                                        Expression::Atomic(Atomic::Variable("x".to_string())),
                                        Expression::Atomic(Atomic::Variable("z".to_string())),
                                    ],
                                },
                                ASTNode::Break,
                            ],
                            else_case: Some(vec![
                                ASTNode::Operation {
                                    num_type: Some(NumericType::FiniteField),
                                    operator: Some(Operator::Sub),
                                    output: Some("x".to_string()),
                                    operands: vec![
                                        Expression::Atomic(Atomic::Variable("x".to_string())),
                                        Expression::Atomic(Atomic::Variable("z".to_string())),
                                    ],
                                },
                                ASTNode::Continue,
                            ]),
                        },
                        ],
                },
                ASTNode::Operation {
                    num_type: Some(NumericType::FiniteField),
                    operator: Some(Operator::Add),
                    output: Some("x".to_string()),
                    operands: vec![
                        Expression::Atomic(Atomic::Variable("y".to_string())),
                        Expression::Atomic(Atomic::Variable("z".to_string())),
                    ],
                },
                ],
        };
        let cfg = CFG::new_from_template(template);

        let cfg = cfg.unwrap_or_else(|err| {
            eprintln!("Error at CFG construction: {}", err);
            std::process::exit(1);
        });

        let dot_representation = cfg.to_dot(0);
        std::fs::create_dir_all("./test").expect("Unable to create test directory");
        std::fs::write("./test/cfg_output.dot", dot_representation).expect("Unable to write DOT file");
        let json_representation = cfg.to_json();
        assert_eq!(json_representation, r#"{"entry":0,"blocks":[{"id":0,"phi_functions":[],"statements":[{"num_type":"FiniteField","output":"v000","value":{"operator":null,"operands":[{"Atomic":{"Constant":{"FF":[1,[1]]}}}]}},{"num_type":"FiniteField","output":"v001","value":{"operator":null,"operands":[{"Atomic":{"Constant":{"FF":[1,[10]]}}}]}},{"num_type":"FiniteField","output":"v002","value":{"operator":null,"operands":[{"Atomic":{"Constant":{"FF":[1,[9]]}}}]}},{"num_type":"FiniteField","output":"v003","value":{"operator":"Add","operands":[{"Atomic":{"Variable":"v001"}},{"Atomic":{"Variable":"v002"}}]}},{"num_type":"FiniteField","output":"v004","value":{"operator":null,"operands":[{"Atomic":{"Constant":{"I64":1}}}]}},{"num_type":"FiniteField","output":"v005","value":{"operator":null,"operands":[{"Atomic":{"Constant":{"I64":1}}}]}}],"predecessors":[],"successors":{"Conditional":{"condition":{"Atomic":{"Variable":"v004"}},"to_then":1,"to_else":2}},"declarations":{"v000":{"is_phi":false,"line":0},"v001":{"is_phi":false,"line":1},"v002":{"is_phi":false,"line":2},"v003":{"is_phi":false,"line":3},"v004":{"is_phi":false,"line":4},"v005":{"is_phi":false,"line":5}},"phi_uses":["v014"],"live_in":[],"live_out":["v000","v001","v002","v005"]},{"id":1,"phi_functions":[],"statements":[{"num_type":"FiniteField","output":"v006","value":{"operator":"Sub","operands":[{"Atomic":{"Variable":"v000"}},{"Atomic":{"Variable":"v001"}}]}}],"predecessors":[0],"successors":{"Unconditional":{"to":2}},"declarations":{"v006":{"is_phi":false,"line":0}},"phi_uses":["v014"],"live_in":["v000","v001","v002","v005"],"live_out":["v000","v001","v002","v005","v006"]},{"id":2,"phi_functions":[{"output":"v014","possibilities":[{"variable":"v000","block":0},{"variable":"v006","block":1}]}],"statements":[],"predecessors":[0,1],"successors":{"Unconditional":{"to":3}},"declarations":{"v014":{"is_phi":true,"line":0}},"phi_uses":["v007"],"live_in":["v000","v001","v002","v005","v006","v014"],"live_out":["v001","v002","v005","v014"]},{"id":3,"phi_functions":[{"output":"v007","possibilities":[{"variable":"v014","block":2},{"variable":"v012","block":7}]}],"statements":[{"num_type":"FiniteField","output":"v009","value":{"operator":"Mul","operands":[{"Atomic":{"Variable":"v007"}},{"Atomic":{"Variable":"v002"}}]}}],"predecessors":[2,7],"successors":{"Conditional":{"condition":{"Atomic":{"Variable":"v005"}},"to_then":5,"to_else":7}},"declarations":{"v007":{"is_phi":true,"line":0},"v009":{"is_phi":false,"line":0}},"phi_uses":[],"live_in":["v001","v002","v005","v007","v012","v014"],"live_out":["v001","v002","v005","v007","v014"]},{"id":4,"phi_functions":[],"statements":[{"num_type":"FiniteField","output":"v018","value":{"operator":"Add","operands":[{"Atomic":{"Variable":"v001"}},{"Atomic":{"Variable":"v002"}}]}}],"predecessors":[5],"successors":null,"declarations":{"v018":{"is_phi":false,"line":0}},"phi_uses":[],"live_in":["v001","v002"],"live_out":[]},{"id":5,"phi_functions":[],"statements":[{"num_type":"FiniteField","output":"v011","value":{"operator":"Div","operands":[{"Atomic":{"Variable":"v007"}},{"Atomic":{"Variable":"v002"}}]}}],"predecessors":[3],"successors":{"Unconditional":{"to":4}},"declarations":{"v011":{"is_phi":false,"line":0}},"phi_uses":[],"live_in":["v001","v002","v007"],"live_out":["v001","v002"]},{"id":6,"phi_functions":[],"statements":[],"predecessors":[],"successors":null,"declarations":{},"phi_uses":[],"live_in":[],"live_out":[]},{"id":7,"phi_functions":[],"statements":[{"num_type":"FiniteField","output":"v012","value":{"operator":"Sub","operands":[{"Atomic":{"Variable":"v007"}},{"Atomic":{"Variable":"v002"}}]}}],"predecessors":[3],"successors":{"Unconditional":{"to":3}},"declarations":{"v012":{"is_phi":false,"line":0}},"phi_uses":["v007"],"live_in":["v001","v002","v005","v007","v014"],"live_out":["v001","v002","v005","v007","v012","v014"]}],"definitions":{"v000":[0,{"is_phi":false,"line":0}],"v001":[0,{"is_phi":false,"line":1}],"v002":[0,{"is_phi":false,"line":2}],"v003":[0,{"is_phi":false,"line":3}],"v004":[0,{"is_phi":false,"line":4}],"v005":[0,{"is_phi":false,"line":5}],"v006":[1,{"is_phi":false,"line":0}],"v007":[3,{"is_phi":true,"line":0}],"v009":[3,{"is_phi":false,"line":0}],"v011":[5,{"is_phi":false,"line":0}],"v012":[7,{"is_phi":false,"line":0}],"v014":[2,{"is_phi":true,"line":0}],"v018":[4,{"is_phi":false,"line":0}]},"def_use":{"v000":[{"InInstruction":[1,{"is_phi":false,"line":0}]},{"InInstruction":[2,{"is_phi":true,"line":0}]}],"v001":[{"InInstruction":[0,{"is_phi":false,"line":3}]},{"InInstruction":[1,{"is_phi":false,"line":0}]},{"InInstruction":[4,{"is_phi":false,"line":0}]}],"v002":[{"InInstruction":[0,{"is_phi":false,"line":3}]},{"InInstruction":[3,{"is_phi":false,"line":0}]},{"InInstruction":[4,{"is_phi":false,"line":0}]},{"InInstruction":[5,{"is_phi":false,"line":0}]},{"InInstruction":[7,{"is_phi":false,"line":0}]}],"v004":[{"InCondition":0}],"v005":[{"InCondition":3}],"v006":[{"InInstruction":[2,{"is_phi":true,"line":0}]}],"v007":[{"InInstruction":[3,{"is_phi":false,"line":0}]},{"InInstruction":[5,{"is_phi":false,"line":0}]},{"InInstruction":[7,{"is_phi":false,"line":0}]}],"v012":[{"InInstruction":[3,{"is_phi":true,"line":0}]}],"v014":[{"InInstruction":[3,{"is_phi":true,"line":0}]}]}}"#);
        std::fs::write("./test/cfg_output.json", json_representation).expect("Unable to write JSON file");
    }
}
