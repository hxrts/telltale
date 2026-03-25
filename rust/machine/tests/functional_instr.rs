#![cfg(not(target_arch = "wasm32"))]
//! Per-instruction functional tests for the ProtocolMachine.
#![allow(
    clippy::approx_constant,
    clippy::needless_collect,
    clippy::let_underscore_must_use
)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;

use assert_matches::assert_matches;
use telltale_machine::buffer::{BackpressurePolicy, BufferConfig, BufferMode};
use telltale_machine::coroutine::{CoroStatus, Fault, Value};
use telltale_machine::instr::{Endpoint, ImmValue, Instr, InvokeAction};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError,
    StepResult,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

use test_support::{FailingHandler, PassthroughHandler, RecordingHandler};

// ============================================================================
// Send
// ============================================================================

#[test]
fn test_send_success() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let sent = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Sent { label, .. } if label == "msg"));
    assert!(sent, "expected Sent event");
    assert!(machine.session_coroutines(sid).iter().all(|c| c.is_terminal()));
}

#[test]
fn test_send_type_mismatch() {
    // Give A a Recv type but a Send instruction.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Recv {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Send {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("B", "A", Label::new("msg"), GlobalType::End);

    // Override A's code to be a Send instruction (mismatched with Recv type).
    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![Instr::Send { chan: 0, val: 1 }, Instr::Halt],
    );
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Invoke {
                action: InvokeAction::Reg(0),
            },
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

#[test]
fn test_send_no_type() {
    // Create image, then remove the type for A before stepping.
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let ep_a = Endpoint {
        sid,
        role: "A".into(),
    };
    machine.sessions_mut().remove_type(&ep_a);

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

#[test]
fn test_send_buffer_full_error() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let config = ProtocolMachineConfig {
        buffer_config: BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 1,
            policy: BackpressurePolicy::Error,
        },
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(config);
    let sid = machine.load_choreography(&image).unwrap();

    // Pre-fill the buffer so the next send fails.
    let session = machine.sessions_mut().get_mut(sid).unwrap();
    let _ = session.send("A", "B", Value::Nat(99));

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::BufferFull { .. },
            ..
        })
    );
}

#[test]
fn test_send_buffer_full_block() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let config = ProtocolMachineConfig {
        buffer_config: BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 1,
            policy: BackpressurePolicy::Block,
        },
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(config);
    let sid = machine.load_choreography(&image).unwrap();

    // Pre-fill the buffer.
    let session = machine.sessions_mut().get_mut(sid).unwrap();
    let _ = session.send("A", "B", Value::Nat(99));

    let handler = PassthroughHandler;
    // Step: A should try to send and block.
    // Step scheduler until A runs.
    for _ in 0..10 {
        match machine.step(&handler) {
            Ok(StepResult::Continue) => {}
            Ok(StepResult::Stuck) => break,
            Ok(StepResult::AllDone) => break,
            Err(_) => break,
        }
    }

    // A should be blocked, type unchanged.
    let ep_a = Endpoint {
        sid,
        role: "A".into(),
    };
    let ty = machine.sessions().lookup_type(&ep_a);
    assert_matches!(ty, Some(LocalTypeR::Send { .. }));
}

#[test]
fn test_send_buffer_full_drop() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let config = ProtocolMachineConfig {
        buffer_config: BufferConfig {
            mode: BufferMode::Fifo,
            initial_capacity: 1,
            policy: BackpressurePolicy::Drop,
        },
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(config);
    let sid = machine.load_choreography(&image).unwrap();

    // Pre-fill.
    let session = machine.sessions_mut().get_mut(sid).unwrap();
    let _ = session.send("A", "B", Value::Nat(99));

    let handler = PassthroughHandler;
    // Should not fault — message dropped, type advances.
    machine.run(&handler, 100).unwrap();

    // A's type should have advanced past Send.
    let ep_a = Endpoint {
        sid,
        role: "A".into(),
    };
    // Type removed on Halt.
    assert!(machine.sessions().lookup_type(&ep_a).is_none());
}

#[test]
fn test_send_handler_error() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = FailingHandler::new("handler failed");
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::Invoke { .. },
            ..
        })
    );
}

// ============================================================================
// Recv
// ============================================================================

#[test]
fn test_recv_success() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let recv = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Received { label, .. } if label == "msg"));
    assert!(recv, "expected Received event");
}

#[test]
fn test_recv_blocks_when_empty() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;

    // B will try to recv first if scheduled first and block.
    // After some steps, should complete.
    let ep_b = Endpoint {
        sid,
        role: "B".into(),
    };
    let ty_before = machine.sessions().lookup_type(&ep_b).cloned();
    assert_matches!(ty_before, Some(LocalTypeR::Recv { .. }));

    machine.run(&handler, 100).unwrap();
    assert!(machine.session_coroutines(sid).iter().all(|c| c.is_terminal()));
}

#[test]
fn test_recv_type_mismatch() {
    // B has Send type but Recv instruction.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Recv {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Send {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("B", "A", Label::new("msg"), GlobalType::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![Instr::Receive { chan: 0, dst: 1 }, Instr::Halt],
    );
    // Give B a Recv instruction, but B has Send type → mismatch.
    programs.insert(
        "B".to_string(),
        vec![Instr::Receive { chan: 0, dst: 1 }, Instr::Halt],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

#[test]
fn test_recv_unblocks_on_send() {
    // Standard send/recv: B blocks, A sends, B unblocks.
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    assert!(machine.session_coroutines(sid).iter().all(|c| c.is_terminal()));

    let recv = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Received { .. }));
    assert!(recv);
}

// ============================================================================
// Choose
// ============================================================================

#[test]
fn test_choose_success() {
    let image = test_support::choice_image("A", "B", &["yes", "no"]);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let sent = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Sent { label, .. } if label == "yes"));
    assert!(sent);
}

#[test]
fn test_choose_unknown_label() {
    // A offers "unknown" which is not in the send-type branches.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );

    let global = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Offer {
                chan: 0,
                label: "unknown".into(),
            },
            Instr::Halt,
        ],
    );
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Choose {
                chan: 0,
                table: vec![("yes".into(), 1), ("no".into(), 2)],
            },
            Instr::Halt,
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::UnknownLabel { .. },
            ..
        })
    );
}

#[test]
fn test_choose_type_not_send() {
    // A has Send type but Choose instruction.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Choose {
                chan: 0,
                table: vec![("msg".into(), 1)],
            },
            Instr::Halt,
        ],
    );
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Invoke {
                action: InvokeAction::Reg(0),
            },
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

// ============================================================================
// Offer
// ============================================================================

#[test]
fn test_offer_recv_mode_success() {
    let image = test_support::choice_image("A", "B", &["yes", "no"]);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let recv = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Received { label, .. } if label == "yes"));
    assert!(recv);
}

#[test]
fn test_offer_recv_mode_blocks() {
    // B Choose before A Offer → B blocks until A sends label.
    let image = test_support::choice_image("A", "B", &["go"]);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    // Both should complete.
    assert!(machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Received { .. })));
}

#[test]
fn test_offer_unknown_label_in_table() {
    // Choose receives a label not in the jump table.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv_choice(
            "A",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        ),
    );

    let global = GlobalType::comm(
        "A",
        "B",
        vec![
            (Label::new("yes"), GlobalType::End),
            (Label::new("no"), GlobalType::End),
        ],
    );

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Offer {
                chan: 0,
                label: "yes".into(),
            },
            Instr::Halt,
        ],
    );
    // B's Choose table is missing "yes".
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Choose {
                chan: 0,
                table: vec![("no".into(), 1)],
            },
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::UnknownLabel { .. },
            ..
        })
    );
}

#[test]
fn test_offer_wrong_type() {
    // Endpoint type is End, but instruction is Offer.
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let global = GlobalType::End;

    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), vec![Instr::Halt]);
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Offer {
                chan: 0,
                label: "x".into(),
            },
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::TypeViolation { .. },
            ..
        })
    );
}

// ============================================================================
// Close / Open
// ============================================================================

#[test]
fn test_close_empty_buffers() {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ],
    );
    programs.insert(
        "B".to_string(),
        vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ],
    );

    let image = CodeImage {
        programs,
        global_type: global,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let closed = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Closed { .. }));
    assert!(closed);
}

#[test]
fn test_open_creates_session() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let opened = machine
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Opened { session, .. } if *session == sid));
    assert!(opened);
}

// ============================================================================
// Invoke
// ============================================================================

#[test]
fn test_invoke_calls_step() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = RecordingHandler::new();
    machine.run(&handler, 100).unwrap();

    assert!(
        !handler
            .steps
            .lock()
            .expect("recording handler lock poisoned")
            .is_empty(),
        "handler.step() should have been called"
    );
}

#[test]
fn test_invoke_handler_error() {
    // Use a program with just Invoke to test handler error path.
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let image = CodeImage::from_local_types(&local_types, &global);

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    // FailingHandler: handle_send returns Err.
    let handler = FailingHandler::new("invoke error");
    let result = machine.run(&handler, 100);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::Invoke { .. },
            ..
        })
    );
}

// ============================================================================
// LoadImm / Mov / Jmp / Yield / Halt
// ============================================================================

#[test]
fn test_loadimm_all_types() {
    // Create a program that loads various immediates then halts.
    let program = vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Unit,
        },
        Instr::Set {
            dst: 2,
            val: ImmValue::Nat(42),
        },
        Instr::Set {
            dst: 3,
            val: ImmValue::Nat(314),
        },
        Instr::Set {
            dst: 4,
            val: ImmValue::Bool(true),
        },
        Instr::Set {
            dst: 5,
            val: ImmValue::Str("hello".into()),
        },
        Instr::Halt,
    ];

    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), program);

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let coro = machine.coroutine(0).unwrap();
    assert_eq!(coro.regs[1], Value::Unit);
    assert_eq!(coro.regs[2], Value::Nat(42));
    assert_eq!(coro.regs[3], Value::Nat(314));
    assert_eq!(coro.regs[4], Value::Bool(true));
    assert_eq!(coro.regs[5], Value::Str("hello".into()));
}

#[test]
fn test_mov_copies_register() {
    let program = vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(99),
        },
        Instr::Move { dst: 2, src: 1 },
        Instr::Halt,
    ];

    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), program);

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let coro = machine.coroutine(0).unwrap();
    assert_eq!(coro.regs[2], Value::Nat(99));
}

#[test]
fn test_jmp_sets_pc() {
    // Jmp to Halt at index 2, skipping LoadImm at index 1.
    let program = vec![
        Instr::Jump { target: 2 },
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(999),
        },
        Instr::Halt,
    ];

    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), program);

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let coro = machine.coroutine(0).unwrap();
    // Reg 1 should still be Unit because LoadImm was skipped.
    assert_eq!(coro.regs[1], Value::Unit);
}

#[test]
fn test_yield_advances_pc_and_reschedules() {
    let program = vec![
        Instr::Yield,
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(7),
        },
        Instr::Halt,
    ];

    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), program);

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    let coro = machine.coroutine(0).unwrap();
    assert_eq!(coro.regs[1], Value::Nat(7));
    assert_matches!(coro.status, CoroStatus::Done);
}

#[test]
fn test_halt_sets_done_removes_type() {
    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    machine.run(&handler, 100).unwrap();

    // Both types should be removed.
    let ep_a = Endpoint {
        sid,
        role: "A".into(),
    };
    let ep_b = Endpoint {
        sid,
        role: "B".into(),
    };
    assert!(machine.sessions().lookup_type(&ep_a).is_none());
    assert!(machine.sessions().lookup_type(&ep_b).is_none());

    // Both coroutines Done.
    for c in machine.session_coroutines(sid) {
        assert_matches!(c.status, CoroStatus::Done);
    }
}

// ============================================================================
// Limits
// ============================================================================

#[test]
fn test_max_sessions_exceeded() {
    let config = ProtocolMachineConfig {
        max_sessions: 1,
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(config);

    let image = test_support::simple_send_recv_image("A", "B", "msg");
    machine.load_choreography(&image).unwrap();

    let result = machine.load_choreography(&image);
    assert_matches!(result, Err(ProtocolMachineError::TooManySessions { .. }));
}

#[test]
fn test_max_coroutines_exceeded() {
    let config = ProtocolMachineConfig {
        max_coroutines: 1,
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ProtocolMachine::new(config);

    let image = test_support::simple_send_recv_image("A", "B", "msg");
    let result = machine.load_choreography(&image);
    assert_matches!(result, Err(ProtocolMachineError::TooManyCoroutines { .. }));
}

#[test]
fn test_pc_out_of_bounds() {
    let mut programs = BTreeMap::new();
    programs.insert("A".to_string(), vec![]); // empty program

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    let result = machine.run(&handler, 10);
    assert_matches!(
        result,
        Err(ProtocolMachineError::Fault {
            fault: Fault::PcOutOfBounds,
            ..
        })
    );
}
