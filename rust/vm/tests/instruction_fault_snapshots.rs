#![cfg(not(target_arch = "wasm32"))]
//! Fault-shape snapshots for instruction families.

use assert_matches::assert_matches;
use std::collections::BTreeMap;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Fault;
use telltale_vm::instr::{ImmValue, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{VMConfig, VM, VMError};

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::PassthroughHandler;

fn fault_name(fault: &Fault) -> &'static str {
    match fault {
        Fault::TypeViolation { .. } => "type_violation",
        Fault::UnknownLabel { .. } => "unknown_label",
        Fault::ChannelClosed { .. } => "channel_closed",
        Fault::InvalidSignature { .. } => "invalid_signature",
        Fault::InvokeFault { .. } => "invoke_fault",
        Fault::AcquireFault { .. } => "acquire_fault",
        Fault::TransferFault { .. } => "transfer_fault",
        Fault::SpecFault { .. } => "spec_fault",
        Fault::CloseFault { .. } => "close_fault",
        Fault::FlowViolation { .. } => "flow_violation",
        Fault::NoProgressToken { .. } => "no_progress_token",
        Fault::OutputConditionFault { .. } => "output_condition_fault",
        Fault::OutOfRegisters => "out_of_registers",
        Fault::PcOutOfBounds => "pc_out_of_bounds",
        Fault::BufferFull { .. } => "buffer_full",
        Fault::OutOfCredits => "out_of_credits",
    }
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
fn snapshot_fault_tags_for_core_instruction_families() {
    let mut observed = Vec::new();
    let handler = PassthroughHandler;

    // send: instruction/type mismatch
    {
        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), vec![Instr::Send { chan: 0, val: 1 }]);
                m.insert("B".to_string(), vec![Instr::Halt]);
                m
            },
            global_type: GlobalType::send("B", "A", Label::new("m"), GlobalType::End),
            local_types: {
                let mut m = BTreeMap::new();
                m.insert(
                    "A".to_string(),
                    LocalTypeR::Recv {
                        partner: "B".to_string(),
                        branches: vec![(Label::new("m"), None, LocalTypeR::End)],
                    },
                );
                m.insert(
                    "B".to_string(),
                    LocalTypeR::Send {
                        partner: "A".to_string(),
                        branches: vec![(Label::new("m"), None, LocalTypeR::End)],
                    },
                );
                m
            },
        };
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("send/type_mismatch", fault_name(&fault)));
    }

    // close: endpoint register required
    {
        let image = single_role_end_image(vec![
            Instr::Set {
                dst: 0,
                val: ImmValue::Nat(1),
            },
            Instr::Close { session: 0 },
        ]);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("close/non_endpoint", fault_name(&fault)));
    }

    // invoke: destination register bounds check
    {
        let image = single_role_end_image(vec![Instr::Invoke { action: 0, dst: 99 }]);
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("invoke/dst_oob", fault_name(&fault)));
    }

    // transfer: target must be Nat coroutine id
    {
        let image = single_role_end_image(vec![
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
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("transfer/non_nat_target", fault_name(&fault)));
    }

    // check: malformed knowledge fact shape
    {
        let image = single_role_end_image(vec![
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
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("check/malformed_knowledge", fault_name(&fault)));
    }

    // fork: ghost sid must be Nat and speculation must be enabled.
    {
        let image = single_role_end_image(vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Str("ghost".to_string()),
            },
            Instr::Fork { ghost: 1 },
        ]);
        let mut vm = VM::new(VMConfig {
            speculation_enabled: true,
            ..VMConfig::default()
        });
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 8);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("fork/non_nat_ghost", fault_name(&fault)));
    }

    // choose: missing table mapping for received branch.
    {
        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert(
                    "A".to_string(),
                    vec![
                        Instr::Offer {
                            chan: 0,
                            label: "yes".to_string(),
                        },
                        Instr::Halt,
                    ],
                );
                m.insert(
                    "B".to_string(),
                    vec![
                        Instr::Choose {
                            chan: 0,
                            table: vec![("no".to_string(), 1)],
                        },
                        Instr::Halt,
                    ],
                );
                m
            },
            global_type: GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("yes"), GlobalType::End),
                    (Label::new("no"), GlobalType::End),
                ],
            ),
            local_types: {
                let mut m = BTreeMap::new();
                m.insert(
                    "A".to_string(),
                    LocalTypeR::send_choice(
                        "B",
                        vec![
                            (Label::new("yes"), None, LocalTypeR::End),
                            (Label::new("no"), None, LocalTypeR::End),
                        ],
                    ),
                );
                m.insert(
                    "B".to_string(),
                    LocalTypeR::recv_choice(
                        "A",
                        vec![
                            (Label::new("yes"), None, LocalTypeR::End),
                            (Label::new("no"), None, LocalTypeR::End),
                        ],
                    ),
                );
                m
            },
        };
        let mut vm = VM::new(VMConfig::default());
        vm.load_choreography(&image).expect("load");
        let result = vm.run(&handler, 16);
        let fault = match result {
            Err(VMError::Fault { fault, .. }) => fault,
            other => panic!("expected fault, got {other:?}"),
        };
        observed.push(("choose/unknown_label", fault_name(&fault)));
    }

    let expected = vec![
        ("send/type_mismatch", "type_violation"),
        ("close/non_endpoint", "type_violation"),
        ("invoke/dst_oob", "out_of_registers"),
        ("transfer/non_nat_target", "transfer_fault"),
        ("check/malformed_knowledge", "transfer_fault"),
        ("fork/non_nat_ghost", "type_violation"),
        ("choose/unknown_label", "unknown_label"),
    ];
    assert_eq!(observed, expected);
}

#[test]
fn snapshot_fault_api_shape_is_vm_fault_wrapper() {
    let image = single_role_end_image(vec![Instr::Invoke { action: 0, dst: 99 }]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load");
    let result = vm.run(&PassthroughHandler, 8);
    assert_matches!(result, Err(VMError::Fault { .. }));
}

