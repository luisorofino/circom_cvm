use std::collections::{HashMap, HashSet};
use crate::CFG;
use crate::cvm_emission::compute_idom;
use crate::types::{get_variable_names, Expression, Atomic};

impl CFG {
    /// Tree Scan register coloring (Rastello 2022, Algorithm 22.1).
    /// Operates on C-SSA form (after isolate_phis, before destroy_cssa).
    /// Assigns colors to variables and renames them, eliminating identity copies.
    pub fn tree_scan_coloring(&mut self) {
        if self.blocks.is_empty() {
            return;
        }

        // Step 1: Compute dominance tree
        let idom = compute_idom(&self.blocks, self.entry);
        let children = build_dom_children(&idom, self.blocks.len(), self.entry);

        // Step 2: Compute liveness (live-on-edge semantics) and last-use information
        let (live_in, live_out) = compute_fresh_live_out(&self.blocks);
        let last_use_at = compute_last_uses(&self.blocks, &live_out);

        // Step 3: Run tree scan to assign colors
        let mut color: HashMap<String, usize> = HashMap::new();
        let mut num_colors: usize = 0;

        assign_colors(
            self.entry,
            &self.blocks,
            &children,
            &last_use_at,
            &live_in,
            &mut color,
            &mut num_colors,
        );

        // Step 4: Build renaming map (color -> canonical name)
        let mut color_to_name: HashMap<usize, String> = HashMap::new();
        for (var, &c) in &color {
            color_to_name.entry(c).or_insert_with(|| var.clone());
        }
        let rename: HashMap<String, String> = color.iter()
            .map(|(var, &c)| (var.clone(), color_to_name[&c].clone()))
            .collect();

        // Step 5: Apply renaming and remove identity copies
        apply_coloring(&mut self.blocks, &rename);
    }
}

/// Build children list for the dominance tree.
fn build_dom_children(idom: &[Option<usize>], n: usize, entry: usize) -> Vec<Vec<usize>> {
    let mut children = vec![Vec::new(); n];
    for b in 0..n {
        if b == entry { continue; }
        if let Some(parent) = idom[b] {
            if parent != b {
                children[parent].push(b);
            }
        }
    }
    children
}

/// Compute fresh (live_in, live_out) sets via iterative backward dataflow analysis.
///
/// This operates directly on the current block structure (including any variables
/// introduced by isolate_phis), rather than relying on the stale live_out sets
/// computed during SSA construction.
///
/// Dataflow equations (with phi-edge / live-on-edge semantics):
///   gen(B)      = variables used in B (stmts + terminator) before being defined
///   kill(B)     = variables defined in B (phi outputs + stmt outputs)
///   live_out(B) = union over successors S: (live_in(S) - phi_defs(S)) union phi_args_from(B, S)
///   live_in(B)  = gen(B) union (live_out(B) - kill(B))
fn compute_fresh_live_out(
    blocks: &[crate::BasicBlock],
) -> (Vec<HashSet<String>>, Vec<HashSet<String>>) {
    let n = blocks.len();
    let mut gen = vec![HashSet::new(); n];
    let mut kill = vec![HashSet::new(); n];

    for block in blocks {
        let b = block.id;

        for phi in &block.phi_functions {
            kill[b].insert(phi.output.clone());
        }

        for stmt in &block.statements {
            for operand in &stmt.value.operands {
                for var in get_variable_names(operand) {
                    if !kill[b].contains(&var) {
                        gen[b].insert(var);
                    }
                }
            }
            if let Some(output) = &stmt.output {
                kill[b].insert(output.clone());
            }
        }

        if let Some(crate::Successor::Conditional { condition, .. }) = &block.successors {
            for var in get_variable_names(condition) {
                if !kill[b].contains(&var) {
                    gen[b].insert(var);
                }
            }
        }
    }

    // Precompute phi_defs(S) and phi_args_from(B, S) for each edge B→S
    let phi_defs: Vec<HashSet<String>> = blocks.iter().map(|block| {
        block.phi_functions.iter().map(|phi| phi.output.clone()).collect()
    }).collect();

    let mut phi_args: Vec<HashMap<usize, HashSet<String>>> = vec![HashMap::new(); n];
    for block in blocks {
        let s = block.id;
        for phi in &block.phi_functions {
            for poss in &phi.possibilities {
                phi_args[s].entry(poss.block).or_default().insert(poss.variable.clone());
            }
        }
    }

    let mut live_in: Vec<HashSet<String>> = vec![HashSet::new(); n];
    let mut live_out: Vec<HashSet<String>> = vec![HashSet::new(); n];

    let mut changed = true;
    while changed {
        changed = false;
        for b in (0..n).rev() {
            let successors: Vec<usize> = match &blocks[b].successors {
                Some(crate::Successor::Unconditional { to }) => vec![*to],
                Some(crate::Successor::Conditional { to_then, to_else, .. }) => vec![*to_then, *to_else],
                None => vec![],
            };

            let mut new_out = HashSet::new();
            for &s in &successors {
                for var in &live_in[s] {
                    if !phi_defs[s].contains(var) {
                        new_out.insert(var.clone());
                    }
                }
                if let Some(args) = phi_args[s].get(&b) {
                    new_out.extend(args.iter().cloned());
                }
            }

            let new_in: HashSet<String> = gen[b].iter().cloned()
                .chain(new_out.difference(&kill[b]).cloned())
                .collect();

            if new_out != live_out[b] {
                live_out[b] = new_out;
                changed = true;
            }
            if new_in != live_in[b] {
                live_in[b] = new_in;
                changed = true;
            }
        }
    }

    (live_in, live_out)
}

/// For each program point (block, stmt_index), compute which variables have their last use there.
/// Uses a sentinel index: stmt_index == usize::MAX means "at the terminator / block exit".
/// For phi arguments, the "use" is at the exit of the predecessor (live-on-edge semantics).
fn compute_last_uses(
    blocks: &[crate::BasicBlock],
    live_out: &[HashSet<String>],
) -> HashMap<(usize, usize), Vec<String>> {
    // Collect all use sites for each variable
    let mut all_uses: HashMap<String, Vec<(usize, usize)>> = HashMap::new();

    for block in blocks {
        let block_id = block.id;

        // Uses in statements
        for (idx, stmt) in block.statements.iter().enumerate() {
            for operand_expr in &stmt.value.operands {
                for var in get_variable_names(operand_expr) {
                    all_uses.entry(var).or_default().push((block_id, idx));
                }
            }
        }

        // Uses in terminator condition
        if let Some(crate::Successor::Conditional { condition, .. }) = &block.successors {
            for var in get_variable_names(condition) {
                all_uses.entry(var).or_default().push((block_id, usize::MAX));
            }
        }

        // Phi argument uses: "used" at the exit of the predecessor block.
        for phi in &block.phi_functions {
            for possibility in &phi.possibilities {
                all_uses.entry(possibility.variable.clone())
                    .or_default()
                    .push((possibility.block, usize::MAX));
            }
        }
    }

    // For each variable, find its last use position within each block.
    let mut last_use_in_block: HashMap<(usize, String), usize> = HashMap::new();
    for (var, uses) in &all_uses {
        for &(block_id, idx) in uses {
            let key = (block_id, var.clone());
            let entry = last_use_in_block.entry(key).or_insert(0);
            if idx == usize::MAX || idx >= *entry {
                *entry = idx;
            }
        }
    }

    // A variable's last use in block B triggers color freeing only if the variable
    // is NOT live-out of B (i.e., not used in any successor block).
    let mut result: HashMap<(usize, usize), Vec<String>> = HashMap::new();
    for ((block_id, var), last_idx) in &last_use_in_block {
        let is_live_out = live_out[*block_id].contains(var);
        if !is_live_out {
            result.entry((*block_id, *last_idx))
                .or_default()
                .push(var.clone());
        }
    }

    result
}

/// Choose the first available color. If none available, extend the palette.
fn choose_color(available: &mut Vec<bool>, num_colors: &mut usize) -> usize {
    for (i, &avail) in available.iter().enumerate() {
        if avail {
            if i >= *num_colors {
                *num_colors = i + 1;
            }
            return i;
        }
    }
    // Extend palette
    let c = available.len();
    available.push(true);
    *num_colors = c + 1;
    c
}

/// Recursive DFS on the dominance tree, assigning colors.
fn assign_colors(
    block_id: usize,
    blocks: &[crate::BasicBlock],
    children: &[Vec<usize>],
    last_use_at: &HashMap<(usize, usize), Vec<String>>,
    live_in: &[HashSet<String>],
    color: &mut HashMap<String, usize>,
    num_colors: &mut usize,
) {
    let block = &blocks[block_id];

    // Build this block's palette from its live-in set: a color is occupied iff some
    // variable that is live at block entry holds it. Because a variable's live range is
    // a subtree of the dominance tree, this makes the available set reflect exactly the
    // variables whose live range contains this block. In particular, a variable that is
    // live in a sibling subtree but dead here leaves its color free (unlike a naive
    // inheritance of the immediate dominator's exit state). This is what guarantees the
    // assignment uses no more than Maxlive = omega(G_I) colors.
    let mut available = vec![true; 1024];
    for var in &live_in[block_id] {
        if let Some(&c) = color.get(var) {
            available[c] = false;
        }
    }

    // Process phi outputs, which are defined at block entry (their arguments are used at
    // the predecessors' exits, so they are not freed here).
    for phi in &block.phi_functions {
        let c = choose_color(&mut available, num_colors);
        available[c] = false;
        color.insert(phi.output.clone(), c);
    }

    // Process statements in order
    for (idx, stmt) in block.statements.iter().enumerate() {
        // Free colors of variables whose last use is this statement
        if let Some(vars) = last_use_at.get(&(block_id, idx)) {
            for var in vars {
                if let Some(&c) = color.get(var) {
                    available[c] = true;
                }
            }
        }

        // Assign color to defined variable
        if let Some(output) = &stmt.output {
            // Only color if not already colored (might be pre-existing variable without
            // a definition in this block — shouldn't happen in SSA but defensive)
            if !color.contains_key(output) {
                let c = choose_color(&mut available, num_colors);
                available[c] = false;
                color.insert(output.clone(), c);
            }
        }
    }

    // Free colors of variables whose last use is at the block exit (terminator)
    if let Some(vars) = last_use_at.get(&(block_id, usize::MAX)) {
        for var in vars {
            if let Some(&c) = color.get(var) {
                available[c] = true;
            }
        }
    }

    // Recurse into the dominance-tree children. Each child rebuilds its own palette from
    // its live-in set on entry, so no availability state is threaded down here.
    for &child in &children[block_id] {
        assign_colors(
            child,
            blocks,
            children,
            last_use_at,
            live_in,
            color,
            num_colors,
        );
    }
}

/// Apply the coloring: rename all variables and remove identity copies.
fn apply_coloring(blocks: &mut Vec<crate::BasicBlock>, rename: &HashMap<String, String>) {
    for block in blocks.iter_mut() {
        // Rename phi functions
        for phi in &mut block.phi_functions {
            if let Some(new_name) = rename.get(&phi.output) {
                phi.output = new_name.clone();
            }
            for poss in &mut phi.possibilities {
                if let Some(new_name) = rename.get(&poss.variable) {
                    poss.variable = new_name.clone();
                }
            }
        }

        // Rename statements
        for stmt in &mut block.statements {
            if let Some(ref output) = stmt.output {
                if let Some(new_name) = rename.get(output) {
                    stmt.output = Some(new_name.clone());
                }
            }
            for operand in &mut stmt.value.operands {
                rename_in_expression(operand, rename);
            }
        }

        // Rename terminator condition
        if let Some(crate::Successor::Conditional { condition, .. }) = &mut block.successors {
            rename_in_expression(condition, rename);
        }

        // Remove identity copies (where output == sole operand, both are variables)
        block.statements.retain(|stmt| {
            if let Some(ref output) = stmt.output {
                if stmt.value.operator.is_none() && stmt.value.operands.len() == 1 {
                    if let Expression::Atomic(Atomic::Variable(ref input)) = stmt.value.operands[0] {
                        if output == input {
                            return false; // identity copy, remove
                        }
                    }
                }
            }
            true
        });
    }
}

/// Rename variables inside an expression using the rename map.
fn rename_in_expression(expr: &mut Expression, rename: &HashMap<String, String>) {
    match expr {
        Expression::Atomic(Atomic::Variable(v)) => {
            if let Some(new_name) = rename.get(v.as_str()) {
                *v = new_name.clone();
            }
        }
        Expression::Atomic(_) => {}
        Expression::Parameter(param) => {
            let update = |a: &mut Atomic| {
                if let Atomic::Variable(v) = a {
                    if let Some(new_name) = rename.get(v.as_str()) {
                        *v = new_name.clone();
                    }
                }
            };
            match param {
                crate::types::Parameter::Signal { index, size }
                | crate::types::Parameter::I64Memory { index, size }
                | crate::types::Parameter::FfMemory { index, size } => {
                    update(index);
                    update(size);
                }
                crate::types::Parameter::SubcmpSignal { component, index, size } => {
                    update(component);
                    update(index);
                    update(size);
                }
            }
        }
    }
}
