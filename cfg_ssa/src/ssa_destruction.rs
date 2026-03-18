use crate::{CFG, Statement, Value};
use crate::types::{Expression, Atomic};

impl CFG {
    /// Replaces all phi functions with copy instructions in predecessor blocks.
    /// Uses temporaries to guarantee parallel copy semantics (swap-safe).

    pub fn destroy_ssa(&mut self) {
        let mut next_tmp: usize = 0;

        for block_id in 0..self.blocks.len() {
            if self.blocks[block_id].phi_functions.is_empty() {
                continue;
            }

            let phis = self.blocks[block_id].phi_functions.clone();
            let predecessors = self.blocks[block_id].predecessors.clone();

            // For each phi, allocate one primed temporary shared across all predecessors.
            // join_copies[i] = (phi_out, phi_p)
            let join_copies: Vec<(String, String)> = phis.iter()
                .map(|phi| (phi.output.clone(), Self::fresh_tmp(&mut next_tmp)))
                .collect();

            for &pred_id in &predecessors {
                // Collect (phi_p, source) for each phi
                let mut copies: Vec<(String, String)> = Vec::new();

                for (i, phi) in phis.iter().enumerate() {
                    let mut found_src = None;
                    for possibility in &phi.possibilities {
                        if possibility.block == pred_id {
                            found_src = Some(possibility);
                            break;
                        }
                    }
                    let src = found_src.expect("Missing phi operand for predecessor");
                    // Destination is phi_p
                    copies.push((join_copies[i].1.clone(), src.variable.clone()));
                }

                // Phase 1: save all sources into temps (avoids swap problem)
                let mut tmp_names: Vec<String> = Vec::new();
                for (_dst, src) in &copies {
                    let tmp = Self::fresh_tmp(&mut next_tmp);
                    let stmt = Self::make_copy(tmp.clone(), src.clone());
                    self.blocks[pred_id].add_instruction(stmt);
                    tmp_names.push(tmp);
                }

                // Phase 2: copy temps into primed destinations (phi_p = tmp)
                for (i, (phi_p, _src)) in copies.iter().enumerate() {
                    let stmt = Self::make_copy(phi_p.clone(), tmp_names[i].clone());
                    self.blocks[pred_id].add_instruction(stmt);
                }
            }

            // Insert join-block copies at the beginning: phi_out = phi_p
            // These must precede all existing statements
            let join_stmts: Vec<Statement> = join_copies.iter()
                .map(|(dst, phi_p)| Self::make_copy(dst.clone(), phi_p.clone()))
                .collect();
            let old_stmts = std::mem::replace(&mut self.blocks[block_id].statements, join_stmts);
            self.blocks[block_id].statements.extend(old_stmts);

            // Remove all phi functions from this block
            self.blocks[block_id].phi_functions.clear();
        }
    }

    //Builds a copy statement
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

    //Builds a fresh temporary variable name
    fn fresh_tmp(next_tmp: &mut usize) -> String {
        let name = format!("tmp_{:03}", next_tmp);
        *next_tmp += 1;
        name
    }
}
