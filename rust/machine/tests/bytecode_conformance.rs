#![cfg(not(target_arch = "wasm32"))]
//! Mutation-based malformed bytecode conformance checks.

use std::collections::BTreeMap;

use telltale_machine::instr::{ImmValue, Instr};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};
use telltale_types::{GlobalType, LocalTypeR};

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use test_support::PassthroughHandler;

fn fault_name(err: &ProtocolMachineError) -> Option<&'static str> {
    match err {
        ProtocolMachineError::Fault { fault, .. } => Some(match fault {
            telltale_machine::coroutine::Fault::TypeViolation { .. } => "type_violation",
            telltale_machine::coroutine::Fault::UnknownLabel { .. } => "unknown_label",
            telltale_machine::coroutine::Fault::Transfer { .. } => "transfer_fault",
            telltale_machine::coroutine::Fault::OutOfRegisters => "out_of_registers",
            telltale_machine::coroutine::Fault::Close { .. } => "close_fault",
            telltale_machine::coroutine::Fault::Speculation { .. } => "spec_fault",
            _ => "other_fault",
        }),
        _ => None,
    }
}

fn base_image() -> CodeImage {
    test_support::simple_send_recv_image("A", "B", "m")
}

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), program);
            m
        },
        global_type: GlobalType::End,
        local_types: {
            let mut m = BTreeMap::new();
            m.insert("A".to_string(), LocalTypeR::End);
            m
        },
    }
}

#[test]
fn mutated_programs_are_deterministically_rejected() {
    let mut cases: Vec<(&str, CodeImage, &str)> = Vec::new();

    // Mutate channel operand out of register bounds.
    let mut chan_oob = base_image();
    chan_oob.programs.get_mut("A").expect("A program")[0] = Instr::Send { chan: 99, val: 1 };
    cases.push(("send_chan_oob", chan_oob, "out_of_registers"));

    // Mutate endpoint register to a non-endpoint before receive.
    let mut recv_wrong_chan = base_image();
    recv_wrong_chan.programs.insert(
        "B".to_string(),
        vec![
            Instr::Set {
                dst: 0,
                val: ImmValue::Nat(1),
            },
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Halt,
        ],
    );
    cases.push((
        "receive_non_endpoint_chan",
        recv_wrong_chan,
        "type_violation",
    ));

    // Mutate close to use a non-endpoint register value.
    let close_non_endpoint = single_role_end_image(vec![
        Instr::Set {
            dst: 0,
            val: ImmValue::Nat(1),
        },
        Instr::Close { session: 0 },
    ]);
    cases.push(("close_non_endpoint", close_non_endpoint, "type_violation"));

    // Mutate transfer target register to non-nat.
    let transfer_non_nat = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Str("x".to_string()),
        },
        Instr::Transfer {
            endpoint: 0,
            target: 1,
            bundle: 0,
        },
    ]);
    cases.push((
        "transfer_non_nat_target",
        transfer_non_nat,
        "transfer_fault",
    ));

    // Mutate check knowledge payload to malformed shape.
    let malformed_check = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(1),
        },
        Instr::Set {
            dst: 2,
            val: ImmValue::Str("Observer".to_string()),
        },
        Instr::Check {
            knowledge: 1,
            target: 2,
            dst: 3,
        },
    ]);
    cases.push(("check_malformed_fact", malformed_check, "transfer_fault"));

    let mut observed = Vec::new();
    for (name, image, expected_fault) in cases {
        let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
        machine.load_choreography(&image).expect("load mutated image");
        let result = machine.run(&PassthroughHandler, 32);
        let tag = match result {
            Ok(_) => "ok",
            Err(ref err) => fault_name(err).unwrap_or("non_fault_error"),
        };
        observed.push((name, tag));
        assert_eq!(tag, expected_fault, "mutation case {name} mismatch");
    }

    let expected = vec![
        ("send_chan_oob", "out_of_registers"),
        ("receive_non_endpoint_chan", "type_violation"),
        ("close_non_endpoint", "type_violation"),
        ("transfer_non_nat_target", "transfer_fault"),
        ("check_malformed_fact", "transfer_fault"),
    ];
    assert_eq!(observed, expected);
}
