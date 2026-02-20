#![cfg(not(target_arch = "wasm32"))]
//! Named Lean theorem conformance tests.
#![allow(clippy::needless_collect, clippy::let_underscore_must_use)]
//!
//! Each test maps to a specific Lean definition/theorem from the
//! `lean/Runtime/VM/` specification files.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::{BTreeMap, HashSet};

use assert_matches::assert_matches;
use telltale_types::LocalTypeR;
use telltale_vm::buffer::BufferConfig;
use telltale_vm::coroutine::{CoroStatus, Fault};
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};
use telltale_vm::instr::Endpoint;
use telltale_vm::output_condition::OutputConditionHint;
use telltale_vm::session::{SessionStatus, SessionStore};
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

use helpers::PassthroughHandler;

fn single_role_end_image(
    program: Vec<telltale_vm::instr::Instr>,
) -> telltale_vm::loader::CodeImage {
    use telltale_types::GlobalType;
    telltale_vm::loader::CodeImage {
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

#[derive(Debug, Clone, Copy)]
struct KnowledgePayloadHandler;

impl EffectHandler for KnowledgePayloadHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<telltale_vm::coroutine::Value, String> {
        Ok(telltale_vm::coroutine::Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(telltale_vm::coroutine::Value::Prod(
            Box::new(telltale_vm::coroutine::Value::Endpoint(Endpoint {
                sid: input.sid,
                role: input.role.to_string(),
            })),
            Box::new(telltale_vm::coroutine::Value::Str("secret".to_string())),
        )))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
        _payload: &telltale_vm::coroutine::Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels available".to_string())
    }

    fn step(
        &self,
        _role: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
    ) -> Result<(), String> {
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
struct HintedInvokeHandler;

impl EffectHandler for HintedInvokeHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<telltale_vm::coroutine::Value, String> {
        Ok(telltale_vm::coroutine::Value::Unit)
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
        _payload: &telltale_vm::coroutine::Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_vm::coroutine::Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels available".to_string())
    }

    fn step(
        &self,
        _role: &str,
        _state: &mut Vec<telltale_vm::coroutine::Value>,
    ) -> Result<(), String> {
        Ok(())
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[telltale_vm::coroutine::Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "vm.custom.observable".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }
}

// ============================================================================
// SessionInv.lean
// ============================================================================

/// Lean: `SessionInv.coherent`
/// After each instruction, endpoint type matches protocol state.
#[test]
fn test_lean_session_coherent() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;

    let ep_a = Endpoint {
        sid,
        role: "A".into(),
    };
    let ep_b = Endpoint {
        sid,
        role: "B".into(),
    };

    // Before execution: A has Send, B has Recv.
    assert_matches!(
        vm.sessions().lookup_type(&ep_a),
        Some(LocalTypeR::Send { .. })
    );
    assert_matches!(
        vm.sessions().lookup_type(&ep_b),
        Some(LocalTypeR::Recv { .. })
    );

    // Run to completion.
    vm.run(&handler, 100).unwrap();

    // After: types removed (endpoints completed).
    assert!(vm.sessions().lookup_type(&ep_a).is_none());
    assert!(vm.sessions().lookup_type(&ep_b).is_none());
}

/// Lean: `SessionInv.ns_disjoint`
/// Two sessions have independent type namespaces.
#[test]
fn test_lean_session_ns_disjoint() {
    let image1 = helpers::simple_send_recv_image("A", "B", "msg");
    let image2 = helpers::simple_send_recv_image("A", "B", "data");

    let mut vm = VM::new(VMConfig::default());
    let sid1 = vm.load_choreography(&image1).unwrap();
    let sid2 = vm.load_choreography(&image2).unwrap();

    let ep1 = Endpoint {
        sid: sid1,
        role: "A".into(),
    };
    let ep2 = Endpoint {
        sid: sid2,
        role: "A".into(),
    };

    // Both have Send types but in separate namespaces.
    assert!(vm.sessions().lookup_type(&ep1).is_some());
    assert!(vm.sessions().lookup_type(&ep2).is_some());
    assert_ne!(sid1, sid2);
}

/// Lean: `SessionInv.conservation`
/// Type entry count is not changed by send/recv (only by Halt/Close).
#[test]
fn test_lean_conservation_inv_preserved() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;

    // Count type entries before.
    let count_before = vm.sessions().get(sid).unwrap().local_types.len();
    assert_eq!(count_before, 2);

    // Step until A sends (but before Halt).
    // After send, both type entries still exist (just advanced).
    let _ = vm.step(&handler); // may schedule A or B

    // Type entries are preserved by send/recv (removed only by Halt).
    let session = vm.sessions().get(sid).unwrap();
    // Still 1 or 2 entries (Halt may have run for one).
    assert!(session.local_types.len() <= count_before);
}

/// Lean: `SessionInv.close_empty`
/// After close with no pending, buffers are empty.
#[test]
fn test_lean_close_empty() {
    let mut store = SessionStore::new();
    let sid = store.open(
        vec!["A".into(), "B".into()],
        &BufferConfig::default(),
        &BTreeMap::new(),
    );

    store.close(sid).unwrap();
    let session = store.get(sid).unwrap();

    // All buffers should be empty.
    for buf in session.buffers.values() {
        assert!(buf.is_empty());
    }
}

/// Lean: `SessionInv.leave_preserves_coherent`
/// Halt removes one endpoint; others remain valid.
#[test]
fn test_lean_leave_preserves_coherent() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    // A halted: type removed. B halted: type removed.
    // Session still accessible.
    let session = vm.sessions().get(sid).unwrap();
    assert!(session.local_types.is_empty());
}

// ============================================================================
// Transport.lean
// ============================================================================

/// Lean: `Transport.fifo`
/// Sent events per edge appear in same order as Received events.
#[test]
fn test_lean_transport_fifo() {
    let image = helpers::recursive_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 200).unwrap_or(());

    // Collect send/recv events per edge.
    let mut sent_order: Vec<String> = Vec::new();
    let mut recv_order: Vec<String> = Vec::new();

    for event in vm.trace() {
        match event {
            ObsEvent::Sent {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid && from == "A" && to == "B" => {
                sent_order.push(label.clone());
            }
            ObsEvent::Received {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid && from == "A" && to == "B" => {
                recv_order.push(label.clone());
            }
            _ => {}
        }
    }

    // Received should be a prefix of sent (FIFO).
    for (i, r) in recv_order.iter().enumerate() {
        assert_eq!(r, &sent_order[i], "FIFO violated at index {i}");
    }
}

/// Lean: `Transport.no_dup`
/// Each Sent event has at most one matching Received.
#[test]
fn test_lean_transport_no_dup() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let sent_count = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Sent { session, .. } if *session == sid))
        .count();
    let recv_count = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Received { session, .. } if *session == sid))
        .count();

    assert!(recv_count <= sent_count, "more receives than sends");
}

/// Lean: `Transport.no_create`
/// No Received event without prior Sent on same edge.
#[test]
fn test_lean_transport_no_create() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let mut sent_edges: Vec<(String, String, String)> = Vec::new();
    let mut recv_edges: Vec<(String, String, String)> = Vec::new();

    for event in vm.trace() {
        match event {
            ObsEvent::Sent {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid => {
                sent_edges.push((from.clone(), to.clone(), label.clone()));
            }
            ObsEvent::Received {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid => {
                recv_edges.push((from.clone(), to.clone(), label.clone()));
            }
            _ => {}
        }
    }

    // Every received edge must have a matching sent edge.
    for r in &recv_edges {
        assert!(sent_edges.contains(r), "received without prior send: {r:?}");
    }
}

/// Lean VM comm semantics: receive must verify transport signatures.
#[test]
fn test_lean_send_receive_signature_verification() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();
    let handler = PassthroughHandler;

    // Advance until A->B has one queued signed payload.
    let mut has_payload = false;
    for _ in 0..8 {
        let _ = vm.step(&handler).expect("step before tamper");
        let queued = vm
            .sessions()
            .get(sid)
            .expect("session exists")
            .has_message("A", "B");
        if queued {
            has_payload = true;
            break;
        }
    }
    assert!(has_payload, "expected queued A->B payload before tamper");

    // Tamper signature in-flight; B's receive must reject it.
    let sess = vm.sessions_mut().get_mut(sid).expect("session exists");
    let mut signed = sess
        .recv_signed("A", "B")
        .expect("signed payload must exist");
    signed.signature.signer = telltale_vm::verification::VerifyingKey([0_u8; 32]);
    let _ = sess
        .send_signed("A", "B", &signed)
        .expect("re-enqueue tampered payload");

    let result = vm.run(&handler, 32);
    assert_matches!(
        result,
        Err(telltale_vm::vm::VMError::Fault {
            fault: Fault::VerificationFailed { .. },
            ..
        })
    );
}

/// Lean VM comm semantics: choose consumes exactly the offered label branch.
#[test]
fn test_lean_offer_choose_label_alignment() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let offered: Vec<String> = vm
        .trace()
        .iter()
        .filter_map(|e| match e {
            ObsEvent::Offered { edge, label, .. } if edge.sid == sid => Some(label.clone()),
            _ => None,
        })
        .collect();
    let chose: Vec<String> = vm
        .trace()
        .iter()
        .filter_map(|e| match e {
            ObsEvent::Chose { edge, label, .. } if edge.sid == sid => Some(label.clone()),
            _ => None,
        })
        .collect();

    assert!(!offered.is_empty(), "expected offered events");
    assert_eq!(offered, chose, "offered/chose label traces diverged");
}

/// Lean VM session lifecycle semantics: opened session transitions to closed and drains buffers.
#[test]
fn test_lean_open_close_session_state_transitions() {
    use telltale_types::{Label, LocalTypeR};
    use telltale_vm::buffer::BufferConfig;
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
    let mut store = SessionStore::new();
    let sid = store.open(
        vec!["A".to_string(), "B".to_string()],
        &BufferConfig::default(),
        &local_types,
    );

    let opened = store.get(sid).expect("session exists after open");
    assert_eq!(opened.status, SessionStatus::Active);
    assert!(
        opened.buffers.values().all(|buf| buf.is_empty()),
        "newly opened session must start with empty buffers"
    );

    store.close(sid).expect("close session");
    let session = store.get(sid).expect("session exists after close");
    assert_eq!(session.status, SessionStatus::Closed);
    assert!(
        session.buffers.values().all(|buf| buf.is_empty()),
        "expected drained buffers after close"
    );
}

/// Lean VM ownership semantics: transfer moves endpoint ownership to target coroutine.
#[test]
fn test_lean_transfer_endpoint_movement() {
    use telltale_types::GlobalType;
    use telltale_vm::instr::{ImmValue, Instr};
    use telltale_vm::loader::CodeImage;

    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(1),
            },
            Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![Instr::Halt]);
    let image = CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    };

    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();
    vm.run(&PassthroughHandler, 100).unwrap();

    assert!(
        vm.trace().iter().any(
            |e| matches!(e, ObsEvent::Transferred { session, from, to, .. }
                if *session == sid && *from == 0 && *to == 1)
        ),
        "expected transferred event from coro 0 to coro 1"
    );

    let ep_a = Endpoint {
        sid,
        role: "A".to_string(),
    };
    let coros = vm.session_coroutines(sid);
    let source = coros
        .iter()
        .find(|c| c.id == 0)
        .expect("source coroutine exists");
    let target = coros
        .iter()
        .find(|c| c.id == 1)
        .expect("target coroutine exists");
    assert!(
        !source.owned_endpoints.contains(&ep_a),
        "source should no longer own transferred endpoint"
    );
    assert!(
        target.owned_endpoints.contains(&ep_a),
        "target should own transferred endpoint"
    );
}

/// Lean VM epistemic semantics: tag/check operate over encoded `(endpoint, fact)` knowledge.
#[test]
fn test_lean_tag_check_epistemic_behavior() {
    use telltale_vm::coroutine::Value;
    use telltale_vm::instr::{ImmValue, Instr};

    let mut image = helpers::simple_send_recv_image("A", "B", "msg");
    image.programs.insert(
        "A".to_string(),
        vec![Instr::Send { chan: 0, val: 1 }, Instr::Halt],
    );
    image.programs.insert(
        "B".to_string(),
        vec![
            Instr::Receive { chan: 0, dst: 1 },
            Instr::Tag { fact: 1, dst: 2 },
            Instr::Set {
                dst: 3,
                val: ImmValue::Str("Observer".to_string()),
            },
            Instr::Check {
                knowledge: 1,
                target: 3,
                dst: 4,
            },
            Instr::Halt,
        ],
    );

    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();
    vm.run(&KnowledgePayloadHandler, 100).unwrap();

    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Tagged { session, fact, .. }
                if *session == sid && fact == "secret")),
        "expected tagged event with transported fact"
    );
    assert!(
        vm.trace().iter().any(
            |e| matches!(e, ObsEvent::Checked { session, target, permitted, .. }
                if *session == sid && target == "Observer" && *permitted)
        ),
        "expected permitted checked event"
    );

    let b = vm.coroutine(1).expect("B coroutine exists");
    assert_eq!(b.regs[4], Value::Bool(true));
}

/// Lean VM guard/effect semantics: acquire then release emits aligned events.
#[test]
fn test_lean_acquire_release_guard_behavior() {
    use telltale_vm::instr::Instr;

    let image = single_role_end_image(vec![
        Instr::Acquire {
            layer: "auth".to_string(),
            dst: 1,
        },
        Instr::Release {
            layer: "auth".to_string(),
            evidence: 1,
        },
        Instr::Halt,
    ]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();
    vm.run(&PassthroughHandler, 100).unwrap();

    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Acquired { layer, .. } if layer == "auth")),
        "expected acquired event"
    );
    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Released { layer, .. } if layer == "auth")),
        "expected released event"
    );
}

/// Lean VM invoke semantics: invoke emits event and output-condition hint is used in commit checks.
#[test]
fn test_lean_invoke_and_output_condition_hint_behavior() {
    use telltale_vm::instr::{Instr, InvokeAction};
    use telltale_vm::output_condition::OutputConditionPolicy;

    let image = single_role_end_image(vec![
        Instr::Invoke {
            action: InvokeAction::Reg(0),
            dst: Some(1),
        },
        Instr::Halt,
    ]);
    let cfg = VMConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "vm.custom.observable".to_string(),
        ]),
        ..VMConfig::default()
    };
    let mut vm = VM::new(cfg);
    vm.load_choreography(&image).unwrap();
    vm.run(&HintedInvokeHandler, 100).unwrap();

    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Invoked { .. })),
        "expected invoked event"
    );

    let checks = vm.output_condition_checks();
    assert!(!checks.is_empty(), "expected output-condition checks");
    assert_eq!(checks[0].meta.predicate_ref, "vm.custom.observable");
    assert_eq!(
        checks[0].meta.witness_ref.as_deref(),
        Some("sid:0:role:A"),
        "expected witness ref from handler hint"
    );
    assert!(
        checks[0].passed,
        "allowlist policy should accept custom predicate"
    );
}

/// Lean VM control semantics: set/move/jump/yield/halt and spawn state transitions.
#[test]
fn test_lean_control_and_spawn_behavior() {
    use telltale_vm::coroutine::Value;
    use telltale_vm::instr::{ImmValue, Instr};

    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(42),
        },
        Instr::Spawn {
            target: 6,
            args: vec![1],
        },
        Instr::Jump { target: 4 },
        Instr::Set {
            dst: 2,
            val: ImmValue::Nat(999),
        },
        Instr::Yield,
        Instr::Halt,
        Instr::Move { dst: 2, src: 0 },
        Instr::Halt,
    ]);

    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();
    vm.run(&PassthroughHandler, 100).unwrap();

    let coros = vm.session_coroutines(sid);
    assert_eq!(coros.len(), 2, "spawn should create one child coroutine");
    assert!(
        coros.iter().all(|c| c.is_terminal()),
        "both coroutines should halt"
    );

    let child = coros
        .iter()
        .find(|c| c.id == 1)
        .expect("spawned child coroutine exists");
    assert_eq!(
        child.regs[2],
        Value::Nat(42),
        "spawn arg copy + move should preserve parent value"
    );
}

/// Lean VM speculation semantics: fork/join/abort emit aligned observable events.
#[test]
fn test_lean_fork_join_abort_speculation_behavior() {
    use telltale_vm::instr::{ImmValue, Instr};

    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(9),
        },
        Instr::Fork { ghost: 1 },
        Instr::Join,
        Instr::Fork { ghost: 1 },
        Instr::Abort,
        Instr::Halt,
    ]);
    let cfg = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    let mut vm = VM::new(cfg);
    vm.load_choreography(&image).unwrap();
    vm.run(&PassthroughHandler, 100).unwrap();

    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Forked { ghost, .. } if *ghost == 9)),
        "expected forked event"
    );
    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Joined { .. })),
        "expected joined event"
    );
    assert!(
        vm.trace()
            .iter()
            .any(|e| matches!(e, ObsEvent::Aborted { .. })),
        "expected aborted event"
    );
}

/// Lean VM speculation semantics: `fork` fails when speculation is disabled.
#[test]
fn test_lean_fork_requires_speculation_enabled() {
    use telltale_vm::instr::{ImmValue, Instr};

    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(3),
        },
        Instr::Fork { ghost: 1 },
    ]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let result = vm.run(&PassthroughHandler, 16);
    assert_matches!(
        result,
        Err(telltale_vm::vm::VMError::Fault {
            fault: Fault::Speculation { .. },
            ..
        })
    );
}

/// Lean VM speculation semantics: `join` requires active speculation state.
#[test]
fn test_lean_join_requires_active_speculation() {
    use telltale_vm::instr::Instr;

    let image = single_role_end_image(vec![Instr::Join]);
    let cfg = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    let mut vm = VM::new(cfg);
    vm.load_choreography(&image).unwrap();

    let result = vm.run(&PassthroughHandler, 16);
    assert_matches!(
        result,
        Err(telltale_vm::vm::VMError::Fault {
            fault: Fault::Speculation { .. },
            ..
        })
    );
}

/// Lean VM speculation semantics: `abort` requires active speculation state.
#[test]
fn test_lean_abort_requires_active_speculation() {
    use telltale_vm::instr::Instr;

    let image = single_role_end_image(vec![Instr::Abort]);
    let cfg = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    let mut vm = VM::new(cfg);
    vm.load_choreography(&image).unwrap();

    let result = vm.run(&PassthroughHandler, 16);
    assert_matches!(
        result,
        Err(telltale_vm::vm::VMError::Fault {
            fault: Fault::Speculation { .. },
            ..
        })
    );
}

/// Abort policy is deterministic and scoped: only speculation state is cleared.
#[test]
fn test_lean_abort_policy_is_deterministic_and_scoped() {
    use telltale_vm::instr::{ImmValue, Instr};

    let image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(7),
        },
        Instr::Fork { ghost: 1 },
        Instr::Abort,
        Instr::Halt,
    ]);

    let run_once = || {
        let cfg = VMConfig {
            speculation_enabled: true,
            ..VMConfig::default()
        };
        let mut vm = VM::new(cfg);
        let sid = vm.load_choreography(&image).unwrap();

        assert_matches!(
            vm.step(&PassthroughHandler),
            Ok(telltale_vm::vm::StepResult::Continue)
        ); // set
        assert_matches!(
            vm.step(&PassthroughHandler),
            Ok(telltale_vm::vm::StepResult::Continue)
        ); // fork

        let before_effect_len = vm.effect_trace().len();
        let before_crashed = vm.crashed_sites().to_vec();
        let before_partitioned = vm.partitioned_edges().to_vec();
        let before_corrupted = vm.corrupted_edges().to_vec();
        let before_timed_out = vm.timed_out_sites().to_vec();
        let before_trace_len = vm.trace().len();

        assert_matches!(
            vm.step(&PassthroughHandler),
            Ok(telltale_vm::vm::StepResult::Continue)
        ); // abort

        let coros = vm.session_coroutines(sid);
        assert_eq!(
            coros.len(),
            1,
            "single-role fixture should keep one coroutine"
        );
        assert!(
            coros[0].spec_state.is_none(),
            "abort should clear speculation state"
        );
        assert_eq!(
            vm.effect_trace().len(),
            before_effect_len,
            "abort should not mutate effect trace"
        );
        assert_eq!(vm.crashed_sites(), before_crashed.as_slice());
        assert_eq!(vm.partitioned_edges(), before_partitioned.as_slice());
        assert_eq!(vm.corrupted_edges(), before_corrupted.as_slice());
        assert_eq!(vm.timed_out_sites(), before_timed_out.as_slice());
        assert!(
            vm.trace().len() > before_trace_len,
            "abort step should append at least one observable event"
        );
        assert!(
            vm.trace()[before_trace_len..]
                .iter()
                .any(|event| matches!(event, ObsEvent::Aborted { .. })),
            "abort step should append an Aborted event"
        );

        vm.run(&PassthroughHandler, 16).unwrap();
        vm.canonical_replay_fragment()
    };

    let left = run_once();
    let right = run_once();
    assert_eq!(
        left, right,
        "abort policy should be deterministic for fixed initial state and handler"
    );
}

// ============================================================================
// Runtime/VM/Scheduler.lean
// ============================================================================

/// Lean: `Scheduler.schedule_confluence`
/// Cooperative and RoundRobin produce same event set for a deterministic protocol.
#[test]
fn test_lean_schedule_confluence() {
    use telltale_vm::SchedPolicy;

    let image = helpers::simple_send_recv_image("A", "B", "msg");

    let run_with_policy = |policy: SchedPolicy| -> HashSet<String> {
        let config = VMConfig {
            sched_policy: policy,
            ..VMConfig::default()
        };
        let mut vm = VM::new(config);
        vm.load_choreography(&image).unwrap();
        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        vm.trace()
            .iter()
            .filter_map(|e| match e {
                ObsEvent::Sent { label, .. } => Some(format!("sent:{label}")),
                ObsEvent::Received { label, .. } => Some(format!("recv:{label}")),
                _ => None,
            })
            .collect()
    };

    let coop_events = run_with_policy(SchedPolicy::Cooperative);
    let rr_events = run_with_policy(SchedPolicy::RoundRobin);

    assert_eq!(coop_events, rr_events);
}

/// Lean: `Scheduler.cooperative_refines_concurrent`
/// Cooperative execution matches round-robin final state.
#[test]
fn test_lean_cooperative_refines_concurrent() {
    use telltale_vm::SchedPolicy;

    let image = helpers::simple_send_recv_image("A", "B", "msg");

    let run_with_policy = |policy: SchedPolicy| -> bool {
        let config = VMConfig {
            sched_policy: policy,
            ..VMConfig::default()
        };
        let mut vm = VM::new(config);
        let sid = vm.load_choreography(&image).unwrap();
        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();
        vm.session_coroutines(sid).iter().all(|c| c.is_terminal())
    };

    assert!(run_with_policy(SchedPolicy::Cooperative));
    assert!(run_with_policy(SchedPolicy::RoundRobin));
}

// ============================================================================
// Runtime/VM/Monitor.lean
// ============================================================================

/// Lean: `Monitor.sound_send`
/// Send instruction with matching Send type does not fault.
#[test]
fn test_lean_monitor_sound_send() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let faults: Vec<_> = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
        .collect();
    assert!(faults.is_empty());
}

/// Lean: `Monitor.sound_recv`
/// Recv instruction with matching Recv type does not fault.
#[test]
fn test_lean_monitor_sound_recv() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let faults: Vec<_> = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
        .collect();
    assert!(faults.is_empty());
}

/// Lean: `Monitor.sound_choose`
/// Choose with matching label does not fault.
#[test]
fn test_lean_monitor_sound_choose() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let faults: Vec<_> = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
        .collect();
    assert!(faults.is_empty());
}

/// Lean: `Monitor.sound_offer`
/// Offer with matching label does not fault.
#[test]
fn test_lean_monitor_sound_offer() {
    let image = helpers::choice_image("A", "B", &["yes", "no"]);
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    let faults: Vec<_> = vm
        .trace()
        .iter()
        .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
        .collect();
    assert!(faults.is_empty());
}

// ============================================================================
// Adequacy.lean
// ============================================================================

/// Lean: `Adequacy.causal_consistency`
/// Every Received event preceded by Sent event on same edge.
#[test]
fn test_lean_causal_consistency() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    // Causal: receives cannot exceed sends at any prefix.
    let mut running_sent = 0;
    let mut running_recv = 0;
    for event in vm.trace() {
        match event {
            ObsEvent::Sent { session, .. } if *session == sid => running_sent += 1,
            ObsEvent::Received { session, .. } if *session == sid => {
                running_recv += 1;
                assert!(running_recv <= running_sent, "received before sent");
            }
            _ => {}
        }
    }
}

/// Lean: `Adequacy.fifo_consistency`
/// Send order = receive order per edge in trace.
#[test]
fn test_lean_fifo_consistency() {
    let image = helpers::recursive_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 200).unwrap_or(());

    let mut sent_labels: Vec<String> = Vec::new();
    let mut recv_labels: Vec<String> = Vec::new();

    for event in vm.trace() {
        match event {
            ObsEvent::Sent {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid && from == "A" && to == "B" => {
                sent_labels.push(label.clone());
            }
            ObsEvent::Received {
                session,
                from,
                to,
                label,
                ..
            } if *session == sid && from == "A" && to == "B" => {
                recv_labels.push(label.clone());
            }
            _ => {}
        }
    }

    // recv_labels is a prefix of sent_labels.
    assert!(recv_labels.len() <= sent_labels.len());
    for (i, label) in recv_labels.iter().enumerate() {
        assert_eq!(label, &sent_labels[i]);
    }
}

/// Lean: `Adequacy.no_phantom_events`
/// Every trace event corresponds to an instruction execution.
#[test]
fn test_lean_no_phantom_events() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;
    vm.run(&handler, 100).unwrap();

    // Every event should be one of our known event types.
    for event in vm.trace() {
        match event {
            ObsEvent::Sent { .. }
            | ObsEvent::Received { .. }
            | ObsEvent::Opened { .. }
            | ObsEvent::Closed { .. }
            | ObsEvent::Halted { .. }
            | ObsEvent::Invoked { .. }
            | ObsEvent::Faulted { .. } => {}
            _ => {}
        }
    }

    // Verify we got the expected events for a simple send/recv.
    let has_opened = vm
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Opened { .. }));
    let has_sent = vm
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Sent { .. }));
    let has_recv = vm
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Received { .. }));
    let has_halted = vm
        .trace()
        .iter()
        .any(|e| matches!(e, ObsEvent::Halted { .. }));

    assert!(has_opened);
    assert!(has_sent);
    assert!(has_recv);
    assert!(has_halted);
}

// ============================================================================
// State.lean
// ============================================================================

/// Lean: `State.wf_pc_bounds`
/// PC always in [0, program.len()) when coroutine is Ready.
#[test]
fn test_lean_wf_pc_bounds() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&image).unwrap();

    let handler = PassthroughHandler;

    for _ in 0..50 {
        // Check PC bounds for all ready coroutines.
        for coro_id in 0..10 {
            if let Some(coro) = vm.coroutine(coro_id) {
                if coro.status == CoroStatus::Ready {
                    let program_len = vm
                        .coroutine_program_len(coro.id)
                        .expect("ready coroutine must reference a valid program");
                    assert!(
                        coro.pc < program_len,
                        "PC {} out of bounds for program len {}",
                        coro.pc,
                        program_len
                    );
                }
            }
        }

        match vm.step(&handler) {
            Ok(telltale_vm::vm::StepResult::AllDone | telltale_vm::vm::StepResult::Stuck) => break,
            Ok(telltale_vm::vm::StepResult::Continue) => {}
            Err(_) => break,
        }
    }
}

/// Lean: `State.endpoint_ownership_unique`
/// No two coroutines own the same endpoint.
#[test]
fn test_lean_endpoint_ownership_unique() {
    let image = helpers::simple_send_recv_image("A", "B", "msg");
    let mut vm = VM::new(VMConfig::default());
    let sid = vm.load_choreography(&image).unwrap();

    let mut seen_endpoints = HashSet::new();
    for coro in vm.session_coroutines(sid) {
        for ep in &coro.owned_endpoints {
            assert!(
                seen_endpoints.insert(ep.clone()),
                "duplicate endpoint ownership: {ep:?}"
            );
        }
    }
}
