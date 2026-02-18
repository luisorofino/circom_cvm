use crate::{CFG, Statement, Value};
use crate::types::{Expression, Atomic};

impl CFG {
    /// Replaces all phi functions with copy instructions in predecessor blocks.
    /// Uses temporaries to guarantee parallel copy semantics.
    pub fn destroy_ssa(&mut self) {
        let mut next_tmp: usize = 0;

        for block_id in 0..self.blocks.len() {
            if self.blocks[block_id].phi_functions.is_empty() {
                continue;
            }

            let phis = self.blocks[block_id].phi_functions.clone();
            let predecessors = self.blocks[block_id].predecessors.clone();

            for &pred_id in &predecessors {
                // Collect (destination, source) for each phi
                let mut copies: Vec<(String, String)> = Vec::new();

                for phi in &phis {
                    let mut found_src = None;
                    for possibility in &phi.possibilities {
                        if possibility.block == pred_id {
                            found_src = Some(possibility);
                            break;
                        }
                    }
                    let src = found_src.expect("Missing phi operand for predecessor");
                    copies.push((phi.output.clone(), src.variable.clone()));
                }

                // Phase 1: save all sources into temps
                let mut tmp_names: Vec<String> = Vec::new();
                for (_dst, src) in &copies {
                    let tmp = Self::fresh_tmp(&mut next_tmp);
                    let stmt = Self::make_copy(tmp.clone(), src.clone());
                    self.blocks[pred_id].statements.push(stmt);
                    tmp_names.push(tmp);
                }

                // Phase 2: copy temps into final destinations
                for (i, (dst, _src)) in copies.iter().enumerate() {
                    let stmt = Self::make_copy(dst.clone(), tmp_names[i].clone());
                    self.blocks[pred_id].statements.push(stmt);
                }
            }

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
