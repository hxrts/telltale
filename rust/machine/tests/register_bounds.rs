#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

use cfg_if::cfg_if;
use std::collections::BTreeMap;

use proptest::prelude::*;
use telltale_machine::coroutine::Fault;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{Instr, ProtocolMachine, ProtocolMachineConfig};
use telltale_machine::{ProtocolMachineError, RunStatus};
use telltale_types::{GlobalType, Label, LocalTypeR};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_machine::ThreadedGuestRuntime;
    }
}

struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no label")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn assert_out_of_registers(result: Result<RunStatus, ProtocolMachineError>) {
    match result {
        Err(ProtocolMachineError::Fault { fault, .. }) => {
            assert!(matches!(fault, Fault::OutOfRegisters))
        }
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
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 8));
    }

    #[test]
    fn cooperative_receive_dst_oob_register_faults(offset in 0u16..256) {
        let dst = 16u16.saturating_add(offset);
        let image = recv_oob_image(dst);
        let mut vm = ProtocolMachine::new(ProtocolMachineConfig::default());
        vm.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(vm.run(&NoopHandler, 16));
    }
}

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        proptest! {
            #[test]
            fn threaded_move_oob_register_faults(offset in 0u16..256) {
                let src = 16u16.saturating_add(offset);
                let image = single_role_move_image(src);
                let mut vm = ThreadedGuestRuntime::with_workers(ProtocolMachineConfig::default(), 1);
                vm.load_choreography_owned(&image, "tests/register_bounds")
                    .expect("load choreography");
                assert_out_of_registers(vm.run(&NoopHandler, 8));
            }

            #[test]
            fn threaded_receive_dst_oob_register_faults(offset in 0u16..256) {
                let dst = 16u16.saturating_add(offset);
                let image = recv_oob_image(dst);
                let mut vm = ThreadedGuestRuntime::with_workers(ProtocolMachineConfig::default(), 1);
                vm.load_choreography_owned(&image, "tests/register_bounds")
                    .expect("load choreography");
                assert_out_of_registers(vm.run(&NoopHandler, 16));
            }
        }
    }
}
