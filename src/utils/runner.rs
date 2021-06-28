use crate::{analyses, checkers, ir, loaders, utils};

use crate::{IRMap, VW_Metadata, VW_CFG};
use loaders::utils::{VwFuncInfo, to_system_v};
use analyses::{StackAnalyzer, HeapAnalyzer, CallAnalyzer};
use analyses::reaching_defs::{analyze_reaching_defs, ReachingDefnAnalyzer};
use analyses::run_worklist;
use analyses::locals_analyzer::LocalsAnalyzer;
use checkers::{check_calls,check_heap,check_stack};
use ir::utils::has_indirect_calls;
use ir::VwArch;
use loaders::ExecutableType;
use utils::utils::{fully_resolved_cfg, get_data};
use std::convert::TryFrom;
use std::collections::HashMap;
use std::iter::FromIterator;

use loaders::Loadable;
use serde_json;
use std::fs;
use std::panic;
use std::time::Instant;
use yaxpeax_core::analyses::control_flow::check_cfg_integrity;

#[derive(Debug)]
pub struct PassConfig {
    pub stack: bool,
    pub linear_mem: bool,
    pub call: bool,
    pub zero_cost: bool, 
}

pub struct Config {
    pub module_path: String,
    pub _num_jobs: u32,
    pub output_path: String,
    pub has_output: bool,
    pub _quiet: bool,
    pub only_func: Option<String>,
    pub executable_type: ExecutableType,
    pub active_passes: PassConfig,
    pub architecture: VwArch,
}

fn run_locals(func_addrs_map: &HashMap<u64, String>, func_signatures: &VwFuncInfo, func_name: &String, cfg: &VW_CFG, irmap: &IRMap) -> bool {
    if let Some(fun_type) = func_signatures.indexes.get(func_name)
        .and_then(|index| func_signatures.signatures.get(usize::try_from(*index).unwrap()))
        .map(to_system_v) {
            let locals_analyzer = LocalsAnalyzer {
                fun_type,
                symbol_table: func_signatures,
                name_addr_map: func_addrs_map,
            };
        let locals_result = run_worklist(&cfg, &irmap, &locals_analyzer);
        // let stack_safe = check_stack(stack_result, &irmap, &locals_analyzer);
    }
    false
}

fn run_stack(cfg: &VW_CFG, irmap: &IRMap) -> bool {
    let stack_analyzer = StackAnalyzer {};
    let stack_result = run_worklist(&cfg, &irmap, &stack_analyzer);
    let stack_safe = check_stack(stack_result, &irmap, &stack_analyzer);
    stack_safe
}

fn run_heap(cfg: &VW_CFG, irmap: &IRMap, metadata: &VW_Metadata) -> bool {
    let heap_analyzer = HeapAnalyzer {
        metadata: metadata.clone(),
    };
    let heap_result = run_worklist(&cfg, &irmap, &heap_analyzer);
    let heap_safe = check_heap(heap_result, &irmap, &heap_analyzer);
    heap_safe
}

fn run_calls(
    cfg: &VW_CFG,
    irmap: &IRMap,
    metadata: &VW_Metadata,
    valid_funcs: &Vec<u64>,
    plt: (u64, u64),
) -> bool {
    let reaching_defs = analyze_reaching_defs(&cfg, &irmap, metadata.clone());
    let call_analyzer = CallAnalyzer {
        metadata: metadata.clone(),
        reaching_defs: reaching_defs.clone(),
        reaching_analyzer: ReachingDefnAnalyzer {
            cfg: cfg.clone(),
            irmap: irmap.clone(),
        },
        funcs: valid_funcs.clone(),
    };
    let call_result = run_worklist(&cfg, &irmap, &call_analyzer);
    let call_safe = check_calls(call_result, &irmap, &call_analyzer, &valid_funcs, &plt);
    call_safe
}

pub fn run(config: Config) {
    let program = config.executable_type.load_program(&config.module_path);
    let metadata = config.executable_type.load_metadata(&program);
    let (x86_64_data, func_addrs, plt) = get_data(&program, &config.executable_type);

    let mut func_counter = 0;
    let mut info: Vec<(std::string::String, usize, f64, f64, f64, f64)> = vec![];
    let valid_funcs: Vec<u64> = func_addrs.clone().iter().map(|x| x.0).collect();
    let func_signatures = config.executable_type.get_func_signatures(&program);
    // println!("{:?}", func_signatures);
    let func_addrs_map = HashMap::from_iter(func_addrs.clone());
    for (addr, func_name) in func_addrs {
        if config.only_func.is_some() && func_name != config.only_func.as_ref().unwrap().as_str() {
            continue;
        }
        println!("Generating CFG for {:?}", func_name);
        let start = Instant::now();
        let (cfg, irmap) = fully_resolved_cfg(&program, &x86_64_data.contexts, &metadata, addr);
        func_counter += 1;
        println!("Analyzing: {:?}", func_name);
        check_cfg_integrity(&cfg.blocks, &cfg.graph);

        let locals_start = Instant::now();
        if config.active_passes.zero_cost {
            println!("Checking Locals Safety");
            let locals_safe = run_locals(&func_addrs_map, &func_signatures, &func_name, &cfg, &irmap);
            if !locals_safe {
                panic!("Not Locals Safe");
            }
        }

        let stack_start = Instant::now();
        if config.active_passes.stack {
            println!("Checking Stack Safety");
            let stack_safe = run_stack(&cfg, &irmap);
            if !stack_safe {
                panic!("Not Stack Safe");
            }
        }

        let heap_start = Instant::now();
        if config.active_passes.linear_mem {
            println!("Checking Heap Safety");
            let heap_safe = run_heap(&cfg, &irmap, &metadata);
            if !heap_safe {
                panic!("Not Heap Safe");
            }
        }

        let call_start = Instant::now();
        if config.active_passes.linear_mem {
            println!("Checking Call Safety");
            if has_indirect_calls(&irmap) {
                let call_safe = run_calls(&cfg, &irmap, &metadata, &valid_funcs, plt);
                if !call_safe {
                    panic!("Not Call Safe");
                }
            }
        }
        let end = Instant::now();
        info.push((
            func_name.to_string(),
            cfg.blocks.len(),
            (stack_start - locals_start).as_secs_f64(),
            (heap_start - stack_start).as_secs_f64(),
            (call_start - heap_start).as_secs_f64(),
            (end - call_start).as_secs_f64(),
        ));
        println!(
            "Verified {:?} at {:?} blocks. CFG: {:?}s Stack: {:?}s Heap: {:?}s Calls: {:?}s",
            func_name,
            cfg.blocks.len(),
            (stack_start - locals_start).as_secs_f64(),
            (heap_start - stack_start).as_secs_f64(),
            (call_start - heap_start).as_secs_f64(),
            (end - call_start).as_secs_f64()
        );
    }
    if config.has_output {
        let data = serde_json::to_string(&info).unwrap();
        println!("Dumping Stats to {}", config.output_path);
        fs::write(config.output_path, data).expect("Unable to write file");
    }

    let mut total_cfg_time = 0.0;
    let mut total_stack_time = 0.0;
    let mut total_heap_time = 0.0;
    let mut total_call_time = 0.0;
    for (_, _, cfg_time, stack_time, heap_time, call_time) in &info {
        total_cfg_time += cfg_time;
        total_stack_time += stack_time;
        total_heap_time += heap_time;
        total_call_time += call_time;
    }
    println!("Verified {:?} functions", func_counter);
    println!(
        "Total time = {:?}s CFG: {:?} Stack: {:?}s Heap: {:?}s Call: {:?}s",
        total_cfg_time + total_stack_time + total_heap_time + total_call_time,
        total_cfg_time,
        total_stack_time,
        total_heap_time,
        total_call_time
    );
    println!("Done!");
}
