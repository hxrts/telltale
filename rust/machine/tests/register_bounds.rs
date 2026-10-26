#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Property tests for register and resource bound enforcement.

use cfg_if::cfg_if;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use proptest::prelude::*;
use telltale_machine::coroutine::Fault;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{Instr, ProtocolMachine, ProtocolMachineConfig};
use telltale_machine::{ProtocolMachineError, RunStatus};
use telltale_types::{GlobalType, Label, LocalTypeR};

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_machine::ThreadedProtocolMachine;
    }
}

#[derive(Default)]
struct NoopHandler {
    receive_calls: AtomicUsize,
}

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
        self.receive_calls.fetch_add(1, Ordering::SeqCst);
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
            assert!(
                matches!(fault, Fault::OutOfRegisters),
                "expected OutOfRegisters, got {fault:?}"
            )
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

fn recv_image(dst: u16) -> CodeImage {
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
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");
        assert_out_of_registers(machine.run(&NoopHandler::default(), 8));
    }

    #[test]
    fn cooperative_receive_dst_oob_register_faults(offset in 0u16..256) {
        let dst = 16u16.saturating_add(offset);
        let image = recv_image(dst);
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load choreography");
        let handler = NoopHandler::default();
        assert_out_of_registers(machine.run(&handler, 16));
        assert_eq!(handler.receive_calls.load(Ordering::SeqCst), 0);
    }
}

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        proptest! {
            #[test]
            fn threaded_move_oob_register_faults(offset in 0u16..256) {
                let src = 16u16.saturating_add(offset);
                let image = single_role_move_image(src);
                let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
                let owner = machine.load_choreography_owned(&image, "tests/register_bounds")
                    .expect("load choreography");
                let result = machine.run(&NoopHandler::default(), 8);
                let closed = machine.close_and_reap_session(owner.session_id());
                let disposal = machine.shutdown_worker_pool();
                assert!(closed.is_ok(), "original session cleanup failed: {closed:?}; run: {result:?}");
                let disposal = disposal.unwrap_or_else(|failure| panic!("original worker cleanup failed: {failure:?}; run: {result:?}"));
                assert_eq!(disposal.joined_workers(), 1);
                assert!(disposal.worker_panics().is_empty());
                assert_out_of_registers(result);
            }

            #[test]
            fn threaded_receive_dst_oob_register_faults(offset in 0u16..256) {
                let dst = 16u16.saturating_add(offset);
                let image = recv_image(dst);
                let mut machine = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 1);
                let owner = machine.load_choreography_owned(&image, "tests/register_bounds")
                    .expect("load choreography");
                let handler = NoopHandler::default();
                let result = machine.run(&handler, 16);
                let receive_calls = handler.receive_calls.load(Ordering::SeqCst);
                let closed = machine.close_and_reap_session(owner.session_id());
                let disposal = machine.shutdown_worker_pool();
                assert!(closed.is_ok(), "original session cleanup failed: {closed:?}; run: {result:?}");
                let disposal = disposal.unwrap_or_else(|failure| panic!("original worker cleanup failed: {failure:?}; run: {result:?}"));
                assert_eq!(disposal.joined_workers(), 1);
                assert!(disposal.worker_panics().is_empty());
                assert_out_of_registers(result);
                assert_eq!(receive_calls, 0);
            }
        }
    }
}

#[test]
fn cooperative_receive_valid_destination_invokes_host_once() {
    let config = ProtocolMachineConfig::default();
    let image = recv_image(config.num_registers - 1);
    let mut machine = ProtocolMachine::new(config);
    machine
        .load_choreography(&image)
        .expect("load valid receive choreography");
    let handler = NoopHandler::default();
    assert!(matches!(machine.run(&handler, 16), Ok(RunStatus::AllDone)));
    assert_eq!(handler.receive_calls.load(Ordering::SeqCst), 1);
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_receive_valid_destination_invokes_host_once() {
    let config = ProtocolMachineConfig::default();
    let image = recv_image(config.num_registers - 1);
    let mut machine = ThreadedProtocolMachine::with_workers(config, 1);
    let owner = machine
        .load_choreography_owned(&image, "tests/register_bounds")
        .expect("load valid receive choreography");
    let handler = NoopHandler::default();
    let result = machine.run(&handler, 16);
    let receive_calls = handler.receive_calls.load(Ordering::SeqCst);
    let closed = machine.close_and_reap_session(owner.session_id());
    let disposal = machine.shutdown_worker_pool();
    assert!(
        closed.is_ok(),
        "original session cleanup failed: {closed:?}; run: {result:?}"
    );
    let disposal = disposal.unwrap_or_else(|failure| {
        panic!("original worker cleanup failed: {failure:?}; run: {result:?}")
    });
    assert_eq!(disposal.joined_workers(), 1);
    assert!(disposal.worker_panics().is_empty());
    assert!(matches!(result, Ok(RunStatus::AllDone)), "run: {result:?}");
    assert_eq!(receive_calls, 1);
}
