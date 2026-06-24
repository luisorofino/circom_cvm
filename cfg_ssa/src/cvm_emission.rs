use std::collections::HashSet;

use crate::types::*;
use crate::{BasicBlock, CFG, Statement, Successor};

pub fn operator_to_cvm(op: &Operator) -> &'static str {
    match op {
        Operator::Add => "add",
        Operator::Sub => "sub",
        Operator::Mul => "mul",
        Operator::Div => "div",
        Operator::Rem => "rem",
        Operator::IDiv => "idiv",
        Operator::Pow => "pow",
        Operator::Greater => "gt",
        Operator::GreaterEqual => "ge",
        Operator::Less => "lt",
        Operator::LessEqual => "le",
        Operator::Equal => "eq",
        Operator::NotEqual => "neq",
        Operator::EqualZero => "eqz",
        Operator::And => "and",
        Operator::Or => "or",
        Operator::ShiftRight => "shr",
        Operator::ShiftLeft => "shl",
        Operator::BitAnd => "band",
        Operator::BitOr => "bor",
        Operator::BitXor => "bxor",
        Operator::BitNot => "bnot",
        Operator::Extend => "extend_i64",
        Operator::Wrap => "wrap_ff",
        Operator::Load => "load",
        Operator::Store => "store",
        Operator::MStore => "mstore",
        Operator::MStoreFromSignal => "mstore_from_signal",
        Operator::MStoreFromCmpSignal => "mstore_from_cmp_signal",
        Operator::GetSignal => "get_signal",
        Operator::GetCmpSignal => "get_cmp_signal",
        Operator::SetSignal => "set_signal",
        Operator::MSetSignal => "mset_signal",
        Operator::MSetSignalFromMemory => "mset_signal_from_mem",
        Operator::SetCmpIn => "set_cmp_input",
        Operator::SetCmpInCnt => "set_cmp_input_cnt",
        Operator::SetCmpInRun => "set_cmp_input_run",
        Operator::SetCmpInCntCheck => "set_cmp_input_cnt_check",
        Operator::MSetCmpIn => "mset_cmp_input",
        Operator::MSetCmpInCnt => "mset_cmp_input_cnt",
        Operator::MSetCmpInRun => "mset_cmp_input_run",
        Operator::MSetCmpInCntCheck => "mset_cmp_input_cnt_check",
        Operator::MSetCmpInFromCmp => "mset_cmp_input_from_cmp",
        Operator::MSetCmpInFromCmpCnt => "mset_cmp_input_from_cmp_cnt",
        Operator::MSetCmpInFromCmpRun => "mset_cmp_input_from_cmp_run",
        Operator::MSetCmpInFromCmpCntCheck => "mset_cmp_input_from_cmp_cnt_check",
        Operator::MSetCmpInFromMemory => "mset_cmp_input_from_memory",
        Operator::MSetCmpInFromMemoryCnt => "mset_cmp_input_from_memory_cnt",
        Operator::MSetCmpInFromMemoryRun => "mset_cmp_input_from_memory_run",
        Operator::MSetCmpInFromMemoryCntCheck => "mset_cmp_input_from_memory_cnt_check",
        Operator::Call => "call",
        Operator::MCall => "mcall",
        Operator::Return => "return",
        Operator::MReturn => "mreturn",
        Operator::GetTemplateId => "get_template_id",
        Operator::GetTemplateSignalPosition => "get_template_signal_position",
        Operator::GetTemplateSignalSize => "get_template_signal_size",
        Operator::GetTemplateSignalDim => "get_template_signal_dimension",
        Operator::GetTemplateSignalType => "get_template_signal_type",
        Operator::GetBusSignalPos => "get_bus_signal_position",
        Operator::GetBusSignalSize => "get_bus_signal_size",
        Operator::GetBusSignalDim => "get_bus_signal_dimension",
        Operator::GetBusSignalType => "get_bus_signal_type",
        Operator::Error => "error",
    }
}

pub fn atomic_to_cvm(a: &Atomic) -> String {
    match a {
        Atomic::Constant(ConstantType::I64(v)) => format!("i64.{}", v),
        Atomic::Constant(ConstantType::FF(v)) => format!("ff.{}", v),
        Atomic::Variable(name) => name.clone(),
        Atomic::Function(name) => format!("${}", name),
    }
}

pub fn parameter_to_cvm(p: &Parameter) -> String {
    match p {
        Parameter::Signal { index, size } => {
            format!("signal({},{})", atomic_to_cvm(index), atomic_to_cvm(size))
        }
        Parameter::SubcmpSignal { component, index, size } => {
            format!("subcmpsignal({},{},{})", atomic_to_cvm(component), atomic_to_cvm(index), atomic_to_cvm(size))
        }
        Parameter::I64Memory { index, size } => {
            format!("i64.memory({},{})", atomic_to_cvm(index), atomic_to_cvm(size))
        }
        Parameter::FfMemory { index, size } => {
            format!("ff.memory({},{})", atomic_to_cvm(index), atomic_to_cvm(size))
        }
    }
}

pub fn expression_to_cvm(e: &Expression) -> String {
    match e {
        Expression::Atomic(a) => atomic_to_cvm(a),
        Expression::Parameter(p) => parameter_to_cvm(p),
    }
}

pub fn statement_to_cvm(stmt: &Statement) -> String {
    let mut s = String::new();
    if let Some(out) = &stmt.output {
        s.push_str(out);
        s.push_str(" = ");
    }
    if let Some(typ) = &stmt.num_type {
        s.push_str(match typ {
            NumericType::Integer => "i64.",
            NumericType::FiniteField => "ff.",
        });
    }
    if let Some(op) = &stmt.value.operator {
        s.push_str(operator_to_cvm(op));
        if !stmt.value.operands.is_empty() {
            s.push(' ');
        }
    }
    let ops: Vec<String> = stmt.value.operands.iter().map(expression_to_cvm).collect();
    s.push_str(&ops.join(" "));
    s
}

// --- Dominance computation (Cooper-Harvey-Kennedy) ---

pub(crate) fn compute_idom(blocks: &[BasicBlock], entry: usize) -> Vec<Option<usize>> {
    let n = blocks.len();
    let rpo = reverse_postorder(blocks, entry);
    let mut rpo_number = vec![0usize; n];
    for (i, &b) in rpo.iter().enumerate() {
        rpo_number[b] = i;
    }

    let mut idom: Vec<Option<usize>> = vec![None; n];
    idom[entry] = Some(entry);

    let intersect = |mut a: usize, mut b: usize, idom: &[Option<usize>]| -> usize {
        while a != b {
            while rpo_number[a] > rpo_number[b] {
                a = idom[a].unwrap();
            }
            while rpo_number[b] > rpo_number[a] {
                b = idom[b].unwrap();
            }
        }
        a
    };

    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            if b == entry {
                continue;
            }
            let mut new_idom: Option<usize> = None;
            for &pred in &blocks[b].predecessors {
                if idom[pred].is_some() {
                    new_idom = Some(match new_idom {
                        None => pred,
                        Some(cur) => intersect(cur, pred, &idom),
                    });
                }
            }
            if new_idom != idom[b] {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }

    idom
}

pub(crate) fn reverse_postorder(blocks: &[BasicBlock], entry: usize) -> Vec<usize> {
    let n = blocks.len();
    let mut visited = vec![false; n];
    let mut order = Vec::with_capacity(n);

    fn dfs(b: usize, blocks: &[BasicBlock], visited: &mut Vec<bool>, order: &mut Vec<usize>) {
        visited[b] = true;
        if let Some(succ) = &blocks[b].successors {
            match succ {
                Successor::Unconditional { to } => {
                    if !visited[*to] { dfs(*to, blocks, visited, order); }
                }
                Successor::Conditional { to_then, to_else, .. } => {
                    if !visited[*to_then] { dfs(*to_then, blocks, visited, order); }
                    if !visited[*to_else] { dfs(*to_else, blocks, visited, order); }
                }
            }
        }
        order.push(b);
    }

    dfs(entry, blocks, &mut visited, &mut order);
    order.reverse();
    order
}

fn dominates(a: usize, b: usize, idom: &[Option<usize>]) -> bool {
    if a == b { return true; }
    let mut cur = b;
    while let Some(d) = idom[cur] {
        if d == a { return true; }
        if d == cur { break; }
        cur = d;
    }
    false
}

// --- Natural loop detection ---

#[allow(dead_code)]
struct LoopInfo {
    header: usize,
    exit: usize,
    body: HashSet<usize>,
}

fn find_loops(blocks: &[BasicBlock], idom: &[Option<usize>]) -> Vec<LoopInfo> {
    let mut back_edges: Vec<(usize, usize)> = Vec::new();
    for block in blocks {
        if let Some(succ) = &block.successors {
            let targets: Vec<usize> = match succ {
                Successor::Unconditional { to } => vec![*to],
                Successor::Conditional { to_then, to_else, .. } => vec![*to_then, *to_else],
            };
            for &t in &targets {
                if dominates(t, block.id, idom) {
                    back_edges.push((block.id, t));
                }
            }
        }
    }

    let mut loops: Vec<LoopInfo> = Vec::new();
    for (tail, header) in back_edges {
        let mut body = HashSet::new();
        body.insert(header);
        let mut stack = vec![tail];
        while let Some(node) = stack.pop() {
            if body.insert(node) {
                for &pred in &blocks[node].predecessors {
                    stack.push(pred);
                }
            }
        }

        // The loop exit is the block control transfers to when the loop terminates
        // normally: the loop header's successor that lies outside the body (circom loops
        // test their condition at the header). Scanning every body block for an out-of-body
        // successor was both ambiguous —an `assert`/`error` block inside the body also
        // leaves the loop— and order-dependent (it iterated a HashSet and kept the *last*
        // candidate), which could misplace the `break` and corrupt the emitted control flow.
        let mut exit = header;
        match &blocks[header].successors {
            Some(Successor::Conditional { to_then, to_else, .. }) => {
                if !body.contains(to_then) {
                    exit = *to_then;
                } else if !body.contains(to_else) {
                    exit = *to_else;
                }
            }
            _ => {
                // Fallback: header is not a conditional. Pick the out-of-body successor
                // deterministically (smallest block id over body blocks visited in order).
                let mut sorted: Vec<usize> = body.iter().copied().collect();
                sorted.sort_unstable();
                'outer: for b in sorted {
                    if let Some(succ) = &blocks[b].successors {
                        let targets: Vec<usize> = match succ {
                            Successor::Unconditional { to } => vec![*to],
                            Successor::Conditional { to_then, to_else, .. } => vec![*to_then, *to_else],
                        };
                        for t in targets {
                            if !body.contains(&t) {
                                exit = t;
                                break 'outer;
                            }
                        }
                    }
                }
            }
        }

        loops.push(LoopInfo { header, exit, body });
    }

    loops
}

// --- Structural walk: CFG → CVM body ---

#[allow(dead_code)]
struct Emitter<'a> {
    blocks: &'a [BasicBlock],
    loops: &'a [LoopInfo],
    idom: &'a [Option<usize>],
    indent: usize,
    output: String,
}

impl<'a> Emitter<'a> {
    fn new(blocks: &'a [BasicBlock], loops: &'a [LoopInfo], idom: &'a [Option<usize>]) -> Self {
        Self { blocks, loops, idom, indent: 0, output: String::new() }
    }

    fn emit_line(&mut self, line: &str) {
        // NOTE: no leading indentation is emitted. The CVM consumer (cvm-compile /
        // circom-witnesscalc) rejects any leading whitespace on a line ("invalid line"),
        // so block bodies must start at column 0 even inside `ff.if` / `loop` blocks.
        // `self.indent` is kept (and still tracked) only as potential structural metadata.
        self.output.push_str(line);
        self.output.push('\n');
    }

    fn emit_statements(&mut self, block_id: usize) {
        let block = &self.blocks[block_id];
        for stmt in &block.statements {
            self.emit_line(&statement_to_cvm(stmt));
        }
    }

    fn find_loop_for_header(&self, header: usize) -> Option<usize> {
        self.loops.iter().position(|l| l.header == header)
    }

    #[allow(dead_code)]
    fn find_containing_loop(&self, block: usize) -> Option<usize> {
        self.loops.iter().position(|l| l.body.contains(&block))
    }

    fn find_join(&self, then_b: usize, else_b: usize) -> Option<usize> {
        let then_forward = self.collect_reachable_forward(then_b);
        let else_forward = self.collect_reachable_forward(else_b);

        let rpo = reverse_postorder(self.blocks, 0);
        for &b in &rpo {
            if b == then_b || b == else_b { continue; }
            if then_forward.contains(&b) && else_forward.contains(&b) {
                return Some(b);
            }
        }

        None
    }

    fn collect_reachable_forward(&self, start: usize) -> HashSet<usize> {
        let mut visited = HashSet::new();
        let mut stack = vec![start];
        while let Some(b) = stack.pop() {
            if !visited.insert(b) { continue; }
            if let Some(succ) = &self.blocks[b].successors {
                let targets: Vec<usize> = match succ {
                    Successor::Unconditional { to } => vec![*to],
                    Successor::Conditional { to_then, to_else, .. } => vec![*to_then, *to_else],
                };
                for t in targets {
                    if !dominates(t, b, self.idom) {
                        stack.push(t);
                    }
                }
            }
        }
        visited
    }

    fn emit_block(&mut self, block_id: usize, loop_header: Option<usize>, loop_exit: Option<usize>, visited: &mut HashSet<usize>) {
        if visited.contains(&block_id) {
            return;
        }
        if Some(block_id) == loop_exit {
            self.emit_line("break");
            return;
        }
        visited.insert(block_id);

        self.emit_statements(block_id);

        let succ = self.blocks[block_id].successors.clone();
        match succ {
            None => {}
            Some(Successor::Unconditional { to }) => {
                if Some(to) == loop_header {
                    self.emit_line("continue");
                } else if Some(to) == loop_exit {
                    self.emit_line("break");
                } else if let Some(li) = self.find_loop_for_header(to) {
                    let loop_info = &self.loops[li];
                    let exit = loop_info.exit;
                    self.emit_line("loop");
                    self.indent += 1;
                    self.emit_block(to, Some(to), Some(exit), visited);
                    self.indent -= 1;
                    self.emit_line("end");
                    self.emit_block(exit, loop_header, loop_exit, visited);
                } else {
                    self.emit_block(to, loop_header, loop_exit, visited);
                }
            }
            Some(Successor::Conditional { num_type, condition, to_then, to_else }) => {
                let ctype = match num_type {
                    NumericType::Integer => "i64",
                    NumericType::FiniteField => "ff",
                };
                let cond_str = expression_to_cvm(&condition);
                self.emit_line(&format!("{}.if {}", ctype, cond_str));
                self.indent += 1;

                let join = self.find_join(to_then, to_else);
                if let Some(j) = join {
                    visited.insert(j);
                }

                self.emit_block(to_then, loop_header, loop_exit, visited);
                self.indent -= 1;

                let then_forward = self.collect_reachable_forward(to_then);
                // No-else (normal): to_else IS the join point
                let no_else_join = join == Some(to_else);
                // No-else (exception): then-branch never reaches to_else (e.g. ends in `error`)
                let no_else_exc = join.is_none()
                    && !then_forward.contains(&to_else)
                    && Some(to_else) != loop_exit;
                let no_else = no_else_join || no_else_exc;
                // Loop-condition: else is just a break → emit `end` then `break`
                let break_after = join.is_none() && Some(to_else) == loop_exit;

                if !no_else && !break_after {
                    self.emit_line("else");
                    self.indent += 1;
                    self.emit_block(to_else, loop_header, loop_exit, visited);
                    self.indent -= 1;
                }
                self.emit_line("end");

                if break_after {
                    self.emit_line("break");
                }

                if let Some(j) = join {
                    visited.remove(&j);
                    self.emit_block(j, loop_header, loop_exit, visited);
                } else if no_else_exc {
                    // to_else is the continuation after the if (not emitted as else)
                    self.emit_block(to_else, loop_header, loop_exit, visited);
                }
            }
        }
    }
}

pub fn cfg_to_cvm_body(cfg: &CFG) -> String {
    let idom = compute_idom(&cfg.blocks, cfg.entry);
    let loops = find_loops(&cfg.blocks, &idom);
    let mut emitter = Emitter::new(&cfg.blocks, &loops, &idom);
    let mut visited = HashSet::new();
    emitter.emit_block(cfg.entry, None, None, &mut visited);
    emitter.output
}
