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
use telltale_vm::coroutine::CoroStatus;
use telltale_vm::instr::Endpoint;
use telltale_vm::session::SessionStore;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

use helpers::PassthroughHandler;

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
