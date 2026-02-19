#![cfg(not(target_arch = "wasm32"))]
//! Fault-shape snapshots for instruction families.

use std::collections::BTreeMap;
use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Fault;
use telltale_vm::instr::{ImmValue, Instr, InvokeAction};
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{VMConfig, VMError, VM};

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::PassthroughHandler;

fn fault_name(fault: &Fault) -> &'static str {
    match fault {
        Fault::TypeViolation { .. } => "type_violation",
        Fault::UnknownLabel { .. } => "unknown_label",
        Fault::ChannelClosed { .. } => "channel_closed",
        Fault::InvalidSignature { .. } => "invalid_signature",
        Fault::VerificationFailed { .. } => "verification_failed",
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

/// Run a CodeImage and expect a fault, returning its name.
fn expect_fault(image: &CodeImage, config: VMConfig, max_steps: usize) -> &'static str {
    let mut vm = VM::new(config);
    vm.load_choreography(image).expect("load");
    let result = vm.run(&PassthroughHandler, max_steps);
    match result {
        Err(VMError::Fault { fault, .. }) => fault_name(&fault),
        other => panic!("expected fault, got {other:?}"),
    }
}

fn case_send_type_mismatch() -> (&'static str, CodeImage) {
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
    ("send/type_mismatch", image)
}

fn case_close_non_endpoint() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 0,
            val: ImmValue::Nat(1),
        },
        Instr::Close { session: 0 },
    ]);
    ("close/non_endpoint", image)
}

fn case_invoke_dst_oob() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![Instr::Invoke {
        action: InvokeAction::Reg(0),
        dst: Some(99),
    }]);
    ("invoke/dst_oob", image)
}

fn case_transfer_non_nat_target() -> (&'static str, CodeImage) {
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
    ("transfer/non_nat_target", image)
}

fn case_check_malformed_knowledge() -> (&'static str, CodeImage) {
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
    ("check/malformed_knowledge", image)
}

fn case_fork_non_nat_ghost() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Str("ghost".to_string()),
        },
        Instr::Fork { ghost: 1 },
    ]);
    ("fork/non_nat_ghost", image)
}

fn case_fork_speculation_disabled() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(1),
        },
        Instr::Fork { ghost: 1 },
    ]);
    ("fork/speculation_disabled", image)
}

fn case_join_without_speculation() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![Instr::Join]);
    ("join/without_speculation", image)
}

fn case_abort_without_speculation() -> (&'static str, CodeImage) {
    let image = single_role_end_image(vec![Instr::Abort]);
    ("abort/without_speculation", image)
}

fn case_choose_unknown_label() -> (&'static str, CodeImage) {
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
    ("choose/unknown_label", image)
}

#[test]
fn snapshot_fault_tags_for_core_instruction_families() {
    let mut observed = Vec::new();
    let default_config = VMConfig::default();

    // Test cases with default config
    let default_cases = [
        case_send_type_mismatch(),
        case_close_non_endpoint(),
        case_invoke_dst_oob(),
        case_transfer_non_nat_target(),
        case_check_malformed_knowledge(),
        case_fork_speculation_disabled(),
        case_join_without_speculation(),
        case_abort_without_speculation(),
        case_choose_unknown_label(),
    ];

    for (name, image) in &default_cases {
        let steps = if *name == "choose/unknown_label" {
            16
        } else {
            8
        };
        observed.push((*name, expect_fault(image, default_config.clone(), steps)));
    }

    // Fork case needs speculation enabled
    let (fork_name, fork_image) = case_fork_non_nat_ghost();
    let spec_config = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    observed.push((fork_name, expect_fault(&fork_image, spec_config, 8)));

    // Sort by case name to match expected order
    observed.sort_by_key(|(name, _)| *name);
    observed.sort_by_key(|(name, _)| match *name {
        "send/type_mismatch" => 0,
        "close/non_endpoint" => 1,
        "invoke/dst_oob" => 2,
        "transfer/non_nat_target" => 3,
        "check/malformed_knowledge" => 4,
        "fork/non_nat_ghost" => 5,
        "fork/speculation_disabled" => 6,
        "join/without_speculation" => 7,
        "abort/without_speculation" => 8,
        "choose/unknown_label" => 9,
        _ => 99,
    });

    let expected = vec![
        ("send/type_mismatch", "type_violation"),
        ("close/non_endpoint", "type_violation"),
        ("invoke/dst_oob", "out_of_registers"),
        ("transfer/non_nat_target", "transfer_fault"),
        ("check/malformed_knowledge", "transfer_fault"),
        ("fork/non_nat_ghost", "type_violation"),
        ("fork/speculation_disabled", "spec_fault"),
        ("join/without_speculation", "spec_fault"),
        ("abort/without_speculation", "spec_fault"),
        ("choose/unknown_label", "unknown_label"),
    ];
    assert_eq!(observed, expected);
}

#[test]
fn snapshot_fault_api_shape_is_vm_fault_wrapper() {
    use assert_matches::assert_matches;
    let image = single_role_end_image(vec![Instr::Invoke {
        action: InvokeAction::Reg(0),
        dst: Some(99),
    }]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).expect("load");
    let result = vm.run(&PassthroughHandler, 8);
    assert_matches!(result, Err(VMError::Fault { .. }));
}
