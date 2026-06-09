use std::collections::{HashMap, VecDeque};

use crate::{CFG, Statement, Value};
use crate::types::{Expression, Atomic};

/// Sequentialize a set of parallel copies using topological sort with
/// cycle-breaking (Boissinot et al. 2009 / Rastello Algorithm 21.2).
///
/// Input:  parallel copies as (destination, source) pairs.
/// Output: sequential copies in an order that preserves parallel semantics.
///         Cycles are broken by introducing fresh temporaries (_seq_NNN).
fn sequentialize_parallel_copies(copies: Vec<(String, String)>) -> Vec<(String, String)> {
    let copies: Vec<_> = copies.into_iter().filter(|(d, s)| d != s).collect();
    if copies.is_empty() {
        return vec![];
    }

    let mut result = Vec::new();
    let mut src_of: HashMap<String, String> = HashMap::new();
    let mut ref_count: HashMap<String, usize> = HashMap::new();

    for (d, s) in &copies {
        src_of.insert(d.clone(), s.clone());
        *ref_count.entry(s.clone()).or_insert(0) += 1;
    }

    let mut ready: VecDeque<String> = VecDeque::new();
    for d in src_of.keys() {
        if *ref_count.get(d).unwrap_or(&0) == 0 {
            ready.push_back(d.clone());
        }
    }

    let mut next_seq_tmp: usize = 0;

    while !src_of.is_empty() {
        while let Some(d) = ready.pop_front() {
            if let Some(s) = src_of.remove(&d) {
                result.push((d, s.clone()));
                if let Some(count) = ref_count.get_mut(&s) {
                    *count -= 1;
                    if *count == 0 && src_of.contains_key(&s) {
                        ready.push_back(s);
                    }
                }
            }
        }

        if !src_of.is_empty() {
            let d = src_of.keys().next().unwrap().clone();
            let s = src_of.get(&d).unwrap().clone();
            let t = format!("_seq_{:03}", next_seq_tmp);
            next_seq_tmp += 1;

            result.push((t.clone(), s.clone()));

            src_of.insert(d.clone(), t.clone());
            if let Some(count) = ref_count.get_mut(&s) {
                *count -= 1;
                if *count == 0 && src_of.contains_key(&s) {
                    ready.push_back(s);
                }
            }
            *ref_count.entry(t).or_insert(0) += 1;
        }
    }

    result
}

impl CFG {
    /// Phase 1: Isolate phi-functions by inserting copies to fresh temporaries.
    /// After this, the CFG is in Conventional SSA (C-SSA): phi-webs are interference-free.
    /// Phi-functions remain present but with all-fresh variables.
    pub fn isolate_phis(&mut self) {
        let mut next_tmp: usize = 0;

        for block_id in 0..self.blocks.len() {
            if self.blocks[block_id].phi_functions.is_empty() {
                continue;
            }

            let phis = self.blocks[block_id].phi_functions.clone();
            let predecessors = self.blocks[block_id].predecessors.clone();

            // For each phi, allocate a fresh temp for the output.
            // join_copies[i] = (original_output, t_0)
            let join_copies: Vec<(String, String)> = phis.iter()
                .map(|phi| (phi.output.clone(), Self::fresh_tmp(&mut next_tmp)))
                .collect();

            // phi_updates[phi_idx] stores the new variable names for each possibility.
            // phi_updates[phi_idx][possibility_idx] = fresh temp name
            let mut phi_updates: Vec<Vec<(usize, String)>> = phis.iter()
                .map(|_| Vec::new())
                .collect();

            for &pred_id in &predecessors {
                for (phi_idx, phi) in phis.iter().enumerate() {
                    // Find the possibility corresponding to this predecessor
                    let (poss_idx, possibility) = phi.possibilities.iter().enumerate()
                        .find(|(_, p)| p.block == pred_id)
                        .expect("Missing phi operand for predecessor");

                    // Create fresh temp and append copy: t_i <- a_i
                    let t_i = Self::fresh_tmp(&mut next_tmp);
                    let stmt = Self::make_copy(t_i.clone(), possibility.variable.clone());
                    self.blocks[pred_id].add_instruction(stmt);

                    // Record that this possibility should be renamed to t_i
                    phi_updates[phi_idx].push((poss_idx, t_i));
                }
            }

            // Update phi functions: rename arguments and output
            for (phi_idx, phi) in self.blocks[block_id].phi_functions.iter_mut().enumerate() {
                // Rename each argument to its fresh temp
                for (poss_idx, new_var) in &phi_updates[phi_idx] {
                    phi.possibilities[*poss_idx].variable = new_var.clone();
                }
                // Rename output to fresh temp
                phi.output = join_copies[phi_idx].1.clone();
            }

            // Prepend join copies: original_output <- t_0
            let join_stmts: Vec<Statement> = join_copies.iter()
                .map(|(original_out, t_0)| Self::make_copy(original_out.clone(), t_0.clone()))
                .collect();
            let old_stmts = std::mem::replace(&mut self.blocks[block_id].statements, join_stmts);
            self.blocks[block_id].statements.extend(old_stmts);
        }
    }

    /// Phase 2: Destroy Conventional SSA by replacing phi-resolution copies with
    /// correctly sequentialized parallel copies, then removing phi functions.
    ///
    /// For each join block with phis, for each predecessor:
    ///   1. Collect the parallel copies (phi_target <- copy_source) for each phi
    ///   2. Remove the old copy statements from the predecessor
    ///   3. Sequentialize the parallel copies (topological sort + cycle-breaking)
    ///   4. Append the correctly-ordered copies
    pub fn destroy_cssa(&mut self) {
        for block_id in 0..self.blocks.len() {
            if self.blocks[block_id].phi_functions.is_empty() {
                continue;
            }

            let phis = self.blocks[block_id].phi_functions.clone();
            let predecessors = self.blocks[block_id].predecessors.clone();

            for &pred_id in &predecessors {
                let mut parallel_copies: Vec<(String, String)> = Vec::new();
                let mut stmts_to_remove: Vec<usize> = Vec::new();

                for phi in &phis {
                    let target = &phi.output;
                    let arg_name = phi.possibilities.iter()
                        .find(|p| p.block == pred_id)
                        .expect("Missing phi operand for predecessor")
                        .variable.clone();

                    if *target == arg_name {
                        continue;
                    }

                    let mut found = false;
                    for (idx, stmt) in self.blocks[pred_id].statements.iter().enumerate().rev() {
                        if stmt.output.as_ref() == Some(&arg_name) {
                            if stmt.value.operator.is_none() && stmt.value.operands.len() == 1 {
                                if let Expression::Atomic(Atomic::Variable(ref src)) = stmt.value.operands[0] {
                                    parallel_copies.push((target.clone(), src.clone()));
                                    stmts_to_remove.push(idx);
                                    found = true;
                                }
                            }
                            break;
                        }
                    }

                    if !found {
                        // The phi-resolution copy was an identity removed by coloring
                        // (source and temp got the same color). The arg already holds
                        // the correct value, so use it directly.
                        parallel_copies.push((target.clone(), arg_name.clone()));
                    }
                }

                stmts_to_remove.sort_unstable();
                stmts_to_remove.dedup();
                for &idx in stmts_to_remove.iter().rev() {
                    self.blocks[pred_id].statements.remove(idx);
                }

                let sequential = sequentialize_parallel_copies(parallel_copies);
                for (dst, src) in sequential {
                    let stmt = Self::make_copy(dst, src);
                    self.blocks[pred_id].statements.push(stmt);
                }
            }

            self.blocks[block_id].phi_functions.clear();
        }

        // Remove identity copies (may remain from tree_scan_coloring or trivial phis)
        for block in &mut self.blocks {
            block.statements.retain(|stmt| {
                if let Some(ref output) = stmt.output {
                    if stmt.value.operator.is_none() && stmt.value.operands.len() == 1 {
                        if let Expression::Atomic(Atomic::Variable(ref input)) = stmt.value.operands[0] {
                            if output == input {
                                return false;
                            }
                        }
                    }
                }
                true
            });
        }
    }

    /// Builds a copy statement: output <- input
    fn make_copy(output: String, input: String) -> Statement {
        Statement {
            num_type: None,
            output: Some(output),
            value: Value {
                operator: None,
                operands: vec![Expression::Atomic(Atomic::Variable(input))],
            },
        }
    }

    /// Builds a fresh temporary variable name
    fn fresh_tmp(next_tmp: &mut usize) -> String {
        let name = format!("tmp_{:03}", next_tmp);
        *next_tmp += 1;
        name
    }
}
