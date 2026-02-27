#![allow(missing_docs)]

use std::collections::BTreeMap;

use proptest::prelude::*;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Fault;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{RunStatus, VMError};
#[cfg(feature = "multi-thread")]
use telltale_vm::ThreadedVM;
use telltale_vm::{Instr, VMConfig, VM};

struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_vm::Value],
    ) -> Result<telltale_vm::Value, String> {
        Ok(telltale_vm::Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::Value>,
        _payload: &telltale_vm::Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no label".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_vm::Value>) -> Result<(), String> {
        Ok(())
    }
}

fn assert_out_of_registers(result: Result<RunStatus, VMError>) {
    match result {
        Err(VMError::Fault { fault, .. }) => assert!(matches!(fault, Fault::OutOfRegisters)),
        other => panic!("expected OutOfRegisters fault, got {other:?}"),
    }
}

fn single_role_move_image(src: u16) -> CodeImage {
    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![Instr::Move { dst: 1, src }, Instr::Halt],
    );
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn recv_oob_image(dst: u16) -> CodeImage {
    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![Instr::Send { chan: 0, val: 1 }, Instr::Halt],
    );
    programs.insert(
        "B".to_string(),
        vec![Instr::Receive { chan: 0, dst }, Instr::Halt],
    );
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
    );
    CodeImage {
        programs,
        global_type: GlobalType::send("A", "B", Label::new("m"), GlobalType::End),
        local_types,
    }
}

proptest! {
    #[test]
    fn cooperative_move_oob_register_faults(offset in 0u16..256) {
        let src = 16u16.saturating_add(offset);
        let image = single_role_move_image(src);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 8));
    }

    #[test]
    fn cooperative_receive_dst_oob_register_faults(offset in 0u16..256) {
        let dst = 16u16.saturating_add(offset);
        let image = recv_oob_image(dst);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 16));
    }
}

#[cfg(feature = "multi-thread")]
proptest! {
    #[test]
    fn threaded_move_oob_register_faults(offset in 0u16..256) {
        let src = 16u16.saturating_add(offset);
        let image = single_role_move_image(src);
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 1);
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 8));
    }

    #[test]
    fn threaded_receive_dst_oob_register_faults(offset in 0u16..256) {
        let dst = 16u16.saturating_add(offset);
        let image = recv_oob_image(dst);
        let mut vm = ThreadedVM::with_workers(VMConfig::default(), 1);
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 16));
    }
}
