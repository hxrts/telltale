#![cfg(not(target_arch = "wasm32"))]
//! Monitor precheck and deterministic cost-budget tests.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use assert_matches::assert_matches;
use telltale_vm::coroutine::Fault;
use telltale_vm::instr::Instr;
#[cfg(feature = "multi-thread")]
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{MonitorMode, VMConfig, VMError, VM};

use helpers::PassthroughHandler;

#[test]
fn cooperative_monitor_precheck_catches_mismatched_instr_shape() {
    let mut image = helpers::simple_send_recv_image("A", "B", "msg");
    image.programs.insert(
        "A".to_string(),
        vec![Instr::Receive { chan: 0, dst: 0 }, Instr::Halt],
    );

    let mut vm = VM::new(VMConfig {
        monitor_mode: MonitorMode::SessionTypePrecheck,
        ..VMConfig::default()
    });
    vm.load_choreography(&image).expect("load image");

    let err = vm
        .run(&PassthroughHandler, 32)
        .expect_err("expected mismatch");
    assert_matches!(
        err,
        VMError::Fault {
            fault: Fault::TypeViolation {
                ref message,
                ..
            },
            ..
        } if message.contains("[monitor]")
    );
}

#[test]
fn cooperative_out_of_credits_faults_before_dispatch() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig {
        initial_cost_budget: 0,
        instruction_cost: 1,
        ..VMConfig::default()
    });
    vm.load_choreography(&image).expect("load image");

    let err = vm
        .run(&PassthroughHandler, 32)
        .expect_err("expected out-of-credits");
    assert_matches!(
        err,
        VMError::Fault {
            fault: Fault::OutOfCredits,
            ..
        }
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_out_of_credits_faults_before_dispatch() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = ThreadedVM::with_workers(
        VMConfig {
            initial_cost_budget: 0,
            instruction_cost: 1,
            ..VMConfig::default()
        },
        2,
    );
    vm.load_choreography(&image).expect("load image");

    let err = vm
        .run(&PassthroughHandler, 32)
        .expect_err("expected out-of-credits");
    assert_matches!(
        err,
        VMError::Fault {
            fault: Fault::OutOfCredits,
            ..
        }
    );
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_monitor_precheck_catches_mismatched_instr_shape() {
    let mut image = helpers::simple_send_recv_image("A", "B", "msg");
    image.programs.insert(
        "A".to_string(),
        vec![Instr::Receive { chan: 0, dst: 0 }, Instr::Halt],
    );

    let mut vm = ThreadedVM::with_workers(
        VMConfig {
            monitor_mode: MonitorMode::SessionTypePrecheck,
            ..VMConfig::default()
        },
        2,
    );
    vm.load_choreography(&image).expect("load image");

    let err = vm
        .run(&PassthroughHandler, 32)
        .expect_err("expected mismatch");
    assert_matches!(
        err,
        VMError::Fault {
            fault: Fault::TypeViolation {
                ref message,
                ..
            },
            ..
        } if message.contains("[monitor]")
    );
}
