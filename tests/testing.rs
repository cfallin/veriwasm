#![allow(dead_code, unused_imports, unused_variables)]

use analyses::call_analyzer::CallAnalyzer;
use analyses::heap_analyzer::HeapAnalyzer;
use analyses::reaching_defs::{analyze_reaching_defs, ReachingDefnAnalyzer};
use analyses::run_worklist;
use analyses::stack_analyzer::StackAnalyzer;
use checkers::call_checker::check_calls;
use checkers::heap_checker::check_heap;
use checkers::stack_checker::check_stack;
use ir::utils::has_indirect_calls;
use loaders::utils::VwFuncInfo;
use loaders::{ExecutableType, Loadable};
use lucet_module::{Signature, ValueType};
use std::collections::HashMap;
use std::iter::FromIterator;
use std::panic;
use utils::runner::run_locals;
use utils::utils::{fully_resolved_cfg, get_data, get_one_resolved_cfg};
use veriwasm::{analyses, checkers, ir, loaders, utils};
use yaxpeax_core::analyses::control_flow::check_cfg_integrity;

fn full_test_helper(path: &str, format: ExecutableType) {
    let _ = env_logger::builder().is_test(true).try_init();
    let program = format.load_program(&path);
    println!("Loading Metadata");
    let metadata = format.load_metadata(&program);
    let (x86_64_data, func_addrs, plt, all_addrs) = get_data(&program, &format);
    let valid_funcs: Vec<u64> = func_addrs.clone().iter().map(|x| x.0).collect();
    let all_addrs_map = HashMap::from_iter(all_addrs.clone());
    for (addr, func_name) in func_addrs {
        let (cfg, irmap) = fully_resolved_cfg(&program, &x86_64_data.contexts, &metadata, addr);
        check_cfg_integrity(&cfg.blocks, &cfg.graph);
        println!("Analyzing: {:?} @ {:x}", func_name, addr);
        println!("Checking Stack Safety");
        let stack_analyzer = StackAnalyzer {};
        let stack_result = run_worklist(&cfg, &irmap, &stack_analyzer);
        let stack_safe = check_stack(stack_result, &irmap, &stack_analyzer);
        assert!(stack_safe);
        println!("Checking Heap Safety");
        let heap_analyzer = HeapAnalyzer {
            metadata: metadata.clone(),
        };
        let heap_result = run_worklist(&cfg, &irmap, &heap_analyzer);
        let heap_safe = check_heap(heap_result, &irmap, &heap_analyzer, &all_addrs_map);
        assert!(heap_safe);
        println!("Checking Call Safety");
        if has_indirect_calls(&irmap) {
            let reaching_defs = analyze_reaching_defs(&cfg, &irmap, metadata.clone());
            let call_analyzer = CallAnalyzer {
                metadata: metadata.clone(),
                reaching_defs: reaching_defs.clone(),
                reaching_analyzer: ReachingDefnAnalyzer {
                    cfg: cfg.clone(),
                    irmap: irmap.clone(),
                },
                funcs: vec![],
                cfg: cfg.clone(),
                irmap: irmap.clone(),
            };
            let call_result = run_worklist(&cfg, &irmap, &call_analyzer);
            let call_safe = check_calls(call_result, &irmap, &call_analyzer, &valid_funcs, &plt);
            assert!(call_safe);
        }
    }
    println!("Done!");
}

fn negative_test_helper(path: &str, func_name: &str, format: ExecutableType) {
    let _ = env_logger::builder().is_test(true).try_init();
    let program = format.load_program(&path);
    let (x86_64_data, func_addrs, plt, all_addrs) = get_data(&program, &format);
    let all_addrs_map = HashMap::from_iter(all_addrs.clone());
    let valid_funcs: Vec<u64> = func_addrs.clone().iter().map(|x| x.0).collect();
    println!("Loading Metadata");
    let metadata = format.load_metadata(&program);
    let ((cfg, irmap), x86_64_data) = get_one_resolved_cfg(path, func_name, &program, &format);
    println!("Analyzing: {:?}", func_name);
    check_cfg_integrity(&cfg.blocks, &cfg.graph);
    println!("Checking Stack Safety");
    let stack_analyzer = StackAnalyzer {};
    let stack_result = run_worklist(&cfg, &irmap, &stack_analyzer);
    let stack_safe = check_stack(stack_result, &irmap, &stack_analyzer);
    assert!(stack_safe);
    println!("Checking Heap Safety");
    let heap_analyzer = HeapAnalyzer {
        metadata: metadata.clone(),
    };
    let heap_result = run_worklist(&cfg, &irmap, &heap_analyzer);
    let heap_safe = check_heap(heap_result, &irmap, &heap_analyzer, &all_addrs_map);
    assert!(heap_safe);
    println!("Checking Call Safety");
    if has_indirect_calls(&irmap) {
        let reaching_defs = analyze_reaching_defs(&cfg, &irmap, metadata.clone());
        let call_analyzer = CallAnalyzer {
            metadata: metadata.clone(),
            reaching_defs: reaching_defs.clone(),
            reaching_analyzer: ReachingDefnAnalyzer {
                cfg: cfg.clone(),
                irmap: irmap.clone(),
            },
            funcs: vec![],
            cfg: cfg.clone(),
            irmap: irmap.clone(),
        };
        let call_result = run_worklist(&cfg, &irmap, &call_analyzer);
        let call_safe = check_calls(call_result, &irmap, &call_analyzer, &valid_funcs, &plt);
        assert!(call_safe);
    }
    println!("Done! ");
}

/*
#[derive(Clone, Debug)]
pub struct VwFuncInfo {
    // Index -> Type
    pub signatures: Vec<Signature>,
    // Name -> Index
    pub indexes: HashMap<String, u32>,
}
*/

fn get_proxy_func_signatures() -> VwFuncInfo {
    let mut signatures: Vec<Signature> = Vec::new();
    // sig0 :: i32 -> ()
    let sig0 = Signature {
        params: vec![ValueType::I32],
        ret_ty: None,
    };
    // sig1 :: i32 -> i32 -> ()
    let sig1 = Signature {
        params: vec![ValueType::I32, ValueType::I32],
        ret_ty: None,
    };
    // sig2 :: i32 -> i32
    let sig2 = Signature {
        params: vec![ValueType::I32],
        ret_ty: Some(ValueType::I32),
    };
    signatures.push(sig0);
    signatures.push(sig1);
    signatures.push(sig2);

    let mut indexes: HashMap<String, u32> = HashMap::new();
    indexes.insert("func1".to_string(), 0);
    indexes.insert("func2".to_string(), 0);
    indexes.insert("func3".to_string(), 1);
    indexes.insert("func4".to_string(), 0);
    indexes.insert("func5".to_string(), 0);
    indexes.insert("subfunc5".to_string(), 1);
    indexes.insert("func6".to_string(), 0);
    indexes.insert("func7".to_string(), 2);
    indexes.insert("func8".to_string(), 0);
    indexes.insert("func9".to_string(), 0);

    VwFuncInfo {
        signatures,
        indexes,
    }
}

fn negative_test_with_locals(path: &str, func_name: &str, format: ExecutableType) {
    let _ = env_logger::builder().is_test(true).try_init();
    let program = format.load_program(&path);
    let (x86_64_data, func_addrs, plt, all_addrs) = get_data(&program, &format);
    let all_addrs_map = HashMap::from_iter(all_addrs.clone());
    let valid_funcs: Vec<u64> = func_addrs.clone().iter().map(|x| x.0).collect();
    println!("Loading Metadata");
    let metadata = format.load_metadata(&program);
    let ((cfg, irmap), x86_64_data) = get_one_resolved_cfg(path, func_name, &program, &format);
    println!("Analyzing: {:?}", func_name);
    check_cfg_integrity(&cfg.blocks, &cfg.graph);
    println!("Checking Stack Safety");
    let stack_analyzer = StackAnalyzer {};
    let stack_result = run_worklist(&cfg, &irmap, &stack_analyzer);
    let stack_safe = check_stack(stack_result, &irmap, &stack_analyzer);
    assert!(stack_safe);
    println!("Checking Heap Safety");
    let heap_analyzer = HeapAnalyzer {
        metadata: metadata.clone(),
    };
    let heap_result = run_worklist(&cfg, &irmap, &heap_analyzer);
    let heap_safe = check_heap(heap_result, &irmap, &heap_analyzer, &all_addrs_map);
    assert!(heap_safe);
    println!("Checking Call Safety");
    let reaching_defs = analyze_reaching_defs(&cfg, &irmap, metadata.clone());
    let call_analyzer = CallAnalyzer {
        metadata: metadata.clone(),
        reaching_defs: reaching_defs.clone(),
        reaching_analyzer: ReachingDefnAnalyzer {
            cfg: cfg.clone(),
            irmap: irmap.clone(),
        },
        funcs: vec![],
        cfg: cfg.clone(),
        irmap: irmap.clone(),
    };
    let call_result = run_worklist(&cfg, &irmap, &call_analyzer);
    let call_safe = check_calls(
        call_result.clone(),
        &irmap,
        &call_analyzer,
        &valid_funcs,
        &plt,
    );
    assert!(call_safe);

    // Not actually used by locals checker
    let plt = (0, 0);
    // Fairly confident this will break
    //let func_signatures = format.get_func_signatures(&program);
    let func_signatures = get_proxy_func_signatures();
    println!("Checking Locals safety");
    let locals_safe = run_locals(
        reaching_defs,
        call_result,
        plt,
        &all_addrs_map,
        &func_signatures,
        &func_name.to_string(),
        &cfg,
        &irmap,
        &metadata,
        &valid_funcs,
    );
    assert!(locals_safe);

    println!("Done! ");
}

#[test]
#[should_panic(expected = "assertion failed: stack_safe")]
fn negative_test_zerocost_1() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func1",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: stack_safe")]
fn negative_test_zerocost_2() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func2",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: stack_safe")]
fn negative_test_zerocost_3() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func3",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: locals_safe")]
fn negative_test_zerocost_4() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func4",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: locals_safe")]
fn negative_test_zerocost_5() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func5",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: locals_safe")]
fn negative_test_zerocost_6() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func6",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: locals_safe")]
fn negative_test_zerocost_7() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func7",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic]
fn negative_test_zerocost_8() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func8",
        ExecutableType::Lucet,
    );
}

#[test]
#[should_panic(expected = "assertion failed: call_safe")]
fn negative_test_zerocost_9() {
    negative_test_with_locals(
        "veriwasm_public_data/negative_tests/negative_tests_locals.so",
        "func9",
        ExecutableType::Lucet,
    );
}

// #[test]
// fn full_test_libgraphite() {
//     full_test_helper(
//         "./veriwasm_public_data/firefox_libs/libgraphitewasm.so",
//         ExecutableType::Lucet,
//     )
// }

// #[test]
// fn full_test_libogg() {
//     full_test_helper(
//         "./veriwasm_public_data/firefox_libs/liboggwasm.so",
//         ExecutableType::Lucet,
//     )
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_1() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_1_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_2() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_2_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_3() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_3_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "Jump Targets Broken, target = None")]
// fn negative_test_4() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_4_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: call_safe")]
// fn negative_test_5() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_5_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "Jump Targets Broken, target = None")]
// fn negative_test_6() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_6_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: heap_safe")]
// fn negative_test_7() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_7_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: heap_safe")]
// fn negative_test_8() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_8_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: heap_safe")]
// fn negative_test_9() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_9_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: heap_safe")]
// fn negative_test_10() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_10_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: heap_safe")]
// fn negative_test_11() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_11_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_12() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_12_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_13() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_13_testfail",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_14() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_14_testfail",
//         ExecutableType::Lucet,
//     );
// }

// // # NaCl issue #23
// #[test]
// #[should_panic(expected = "assertion failed: call_safe")]
// fn negative_test_nacl_23() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_23",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_nacl_323_1() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_323_1",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_nacl_323_2() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_323_2",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_nacl_323_3() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_323_3",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_nacl_323_4() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_323_4",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_nacl_390() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_390",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "Illegal RSP access")]
// fn negative_test_nacl_1585() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_1585",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "not implemented")]
// fn negative_test_nacl_2532() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_nacl_2532",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic]
// fn negative_test_bakersfield_1() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_bakersfield_1",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "assertion failed: stack_safe")]
// fn negative_test_misfit_1() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_misfit_1",
//         ExecutableType::Lucet,
//     );
// }

// #[test]
// #[should_panic(expected = "Jump Targets Broken, target = None")]
// fn negative_test_cranelift_805() {
//     negative_test_helper(
//         "veriwasm_public_data/negative_tests/negative_tests.so",
//         "guest_func_cranelift_805",
//         ExecutableType::Lucet,
//     );
// }

// // #[test]
// // fn wasmtime_wasm_callback() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/callback.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_fib() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/fib-wasm.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_fraction_norm() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/fraction-norm.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_hello() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/hello.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_memory() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/memory.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_reflect() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/reflect.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_serialize() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/serialize.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_table() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/table.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_trap() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/trap.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_fib_wasm_dwarf5() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/fib-wasm-dwarf5.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_finalize() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/finalize.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_global() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/global.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_issue_1306() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/issue-1306-name-section-with-u32-max-function-index.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_multi() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/multi.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_reverse_str() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/reverse-str.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_start() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/start.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wasm_threads() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wasm/threads.wasm",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_fuel() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/fuel.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_greeter_reactor() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/greeter_reactor.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_illop_invoke() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/iloop-invoke.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_linking2() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/linking2.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_minimal_reactor() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/minimal-reactor.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_threads() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/threads.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_exit125_wasi_snapshot1() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/exit125_wasi_snapshot1.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_gcd() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/gcd.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_hello_wasi_snapshot0() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/hello_wasi_snapshot0.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_iloop_start() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/iloop-start.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_loop_params() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/loop-params.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_multi() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/multi.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_unreachable() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/unreachable.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_exit_with_saved_fprs() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/exit_with_saved_fprs.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_greeter_callable_command() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/greeter_callable_command.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_interrupt() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/interrupt.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_memory() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/memory.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_rs2wasm_add_func() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/rs2wasm-add-func.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_externref() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/externref.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_greeter_command() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/greeter_command.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_hello() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/hello.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_linking1() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/linking1.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_minimal_command() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/minimal-command.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }

// // #[test]
// // fn wasmtime_wat_simple() {
// //     full_test_helper(
// //         "./veriwasm_public_data/wasmtime/bin/wat/simple.wat",
// //         ExecutableType::Wasmtime,
// //     )
// // }
