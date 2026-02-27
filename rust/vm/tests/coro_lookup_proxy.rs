#![allow(missing_docs)]

use std::collections::BTreeMap;

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::loader::CodeImage;
use telltale_vm::{Instr, VMConfig, VM};

fn simple_single_role_image() -> CodeImage {
    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), vec![Instr::Yield, Instr::Halt]);
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

#[test]
fn coroutine_lookup_proxy_stays_stable_for_large_id_sets() {
    let config = VMConfig {
        max_sessions: 1024,
        max_coroutines: 4096,
        ..VMConfig::default()
    };
    let mut vm = VM::new(config);
    let image = simple_single_role_image();
    let session_count = 256usize;

    for _ in 0..session_count {
        vm.load_choreography(&image).expect("load choreography");
    }

    for _ in 0..32 {
        for coro_id in 0..session_count {
            let coro = vm.coroutine(coro_id).expect("coroutine id should exist");
            assert_eq!(coro.id, coro_id);
        }
    }
}
