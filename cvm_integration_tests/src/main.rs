use std::env;
use std::fs;
use std::time::Instant;

use cvm_parser::parse_program;
use cfg_ssa::type_checking::TypeChecker;
use cfg_ssa::CFGList;

use serde::Serialize;

#[derive(Serialize)]
struct Metrics {
    file: String,
    num_lines: usize,
    num_cfgs: usize,
    avg_blocks_per_cfg: f64,
    avg_non_ssa_variables_per_cfg: f64,
    avg_ssa_variables_per_cfg: f64,
    avg_stmts_per_block: f64,
    time_read: f64,
    time_parse: f64,
    time_typecheck: f64,
    time_cfg: f64,
    time_json: f64,
    time_dot: f64,
}

fn main() {
    // General
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} [--metrics] <file.cvm>", args[0]);
        std::process::exit(1);
    }
    let mut metrics_mode = false;
    let mut file_path = "";

    for arg in &args[1..] {
        if arg == "--metrics" {
            metrics_mode = true;
        } else {
            file_path = arg;
        }
    }

    if file_path.is_empty() {
        eprintln!("Error: no .cvm file provided");
        std::process::exit(1);
    }

    let file_no_suffix = file_path.strip_suffix(".cvm").unwrap_or(file_path);

    // Read the .cvm file
    let t_read_start = Instant::now();
    let file_content = match fs::read_to_string(file_path) {
        Ok(content) => content,
        Err(err) => {
            eprintln!("Error at reading file {}: {}", &file_path, err);
            std::process::exit(1);
        }
    };
    let read_time = t_read_start.elapsed();

    // Parse the file
    let t_parse_start = Instant::now();
    let parsed_program = match parse_program(&file_content) {
        Ok((_, program)) => program,
        Err(err) => {
            eprintln!("Error at parsing file {}: {}", &file_path, err);
            std::process::exit(1);
        }
    };
    let parse_time = t_parse_start.elapsed();


    // Typecheck the parsed program
    let t_typecheck_start = Instant::now();
    let mut checker = TypeChecker::new();
    if let Err(err) = checker.check(&parsed_program) {
        eprintln!("Error at typechecking: {}", err);
        std::process::exit(1);
    }
    let typecheck_time = t_typecheck_start.elapsed();


    // Construct the control flow graph (CFG)
    let t_cfg_start = Instant::now();
    let mut cfg = CFGList::new(parsed_program);
    let mut cfg = cfg.unwrap_or_else(|err| {
        eprintln!("Error at SSA construction: {}", err);
        std::process::exit(1);
    });
    let cfg_time = t_cfg_start.elapsed();

    // Write the SSA CFG to JSON and DOT files
    let t_json_start = Instant::now();
    let json_output_path = format!("{}.json", file_no_suffix);
    if let Err(err) = fs::write(&json_output_path, cfg.to_json()) {
        eprintln!("Error at writing JSON file {}: {}", json_output_path, err);
        std::process::exit(1);
    }
    let json_time = t_json_start.elapsed();

    let t_dot_start = Instant::now();
    let dot_files = cfg.to_dot();
    for (index, dot_content) in dot_files.iter().enumerate() {
        let dot_output_path = format!("{}_{}.dot", file_no_suffix, index);
        if let Err(err) = fs::write(&dot_output_path, dot_content) {
            eprintln!("Error at writing DOT file {}: {}", dot_output_path, err);
            std::process::exit(1);
        }
    }
    let dot_time = t_dot_start.elapsed();

    // Destroy SSA and write post-destruction DOT files
    cfg.destroy_ssa_all();
    let dot_destroyed = cfg.to_dot();
    for (index, dot_content) in dot_destroyed.iter().enumerate() {
        let dot_output_path = format!("{}_destroyed_{}.dot", file_no_suffix, index);
        if let Err(err) = fs::write(&dot_output_path, dot_content) {
            eprintln!("Error at writing destroyed DOT file {}: {}", dot_output_path, err);
            std::process::exit(1);
        }
    }
    

    // --- Metrics mode ---
    if metrics_mode {
        // Structural metrics
        let num_lines = file_content.lines().count();
        let (num_cfgs, avg_blocks_per_cfg, avg_non_ssa_variables_per_cfg, avg_ssa_variables_per_cfg,  avg_stmts_per_block) = cfg.get_metrics();

        let metrics = Metrics {
            file: file_path.to_string(),
            num_lines,
            num_cfgs,
            avg_blocks_per_cfg,
            avg_non_ssa_variables_per_cfg,
            avg_ssa_variables_per_cfg,
            avg_stmts_per_block,
            time_read: read_time.as_secs_f64(),
            time_parse: parse_time.as_secs_f64(),
            time_typecheck: typecheck_time.as_secs_f64(),
            time_cfg: cfg_time.as_secs_f64(),
            time_json: json_time.as_secs_f64(),
            time_dot: dot_time.as_secs_f64(),
        };

        println!("{}", serde_json::to_string(&metrics).unwrap());
        return;
    }

    println!(
        "CFGList successfully written to {} (JSON: {:.6}s, DOT: {:.6}s)",
        json_output_path,
        json_time.as_secs_f64(),
        dot_time.as_secs_f64()
    );
}
