#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Actual resident enqueue and authority rejection on both machine backends.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeSet;
use std::error::Error;
use telltale_machine::buffer::{BackpressurePolicy, EnqueueResult};
use telltale_machine::coroutine::Value;
use telltale_machine::instr::Endpoint;
use telltale_machine::model::state::SessionState;
use telltale_machine::owned::{OwnedSessionEnqueueError, OwnedSessionMachine};
use telltale_machine::verification::{verify_signed_value, verifying_key_for_endpoint};
use telltale_machine::{
    OwnedSession, OwnershipError, OwnershipScope, ProtocolMachine, ProtocolMachineConfig,
};
use test_support::simple_send_recv_image;

type Enqueue = Result<EnqueueResult, OwnedSessionEnqueueError>;

fn enqueue(machine: &mut impl OwnedSessionMachine, owner: &OwnedSession, sequence: u64) -> Enqueue {
    owner.inject_message_with_sequence(machine, "A", "B", Value::Nat(sequence), sequence)
}

fn assert_enqueued(actual: &Enqueue) {
    assert!(matches!(actual, Ok(EnqueueResult::Ok)));
}

fn assert_signed_frame(snapshot: SessionState, sequence: u64) {
    assert_signed_frames(snapshot, &[sequence]);
}

fn assert_signed_frames(mut snapshot: SessionState, sequences: &[u64]) {
    for sequence in sequences {
        let frame = snapshot
            .recv_signed("A", "B")
            .expect("actual resident frame");
        assert_eq!(frame.sequence_no, *sequence);
        assert_eq!(frame.payload, Value::Nat(*sequence));
        let key = verifying_key_for_endpoint(&Endpoint {
            sid: snapshot.sid,
            role: "A".into(),
        });
        assert!(verify_signed_value(&frame.payload, &frame.signature, &key));
    }
    assert!(snapshot.recv_signed("A", "B").is_none());
}

fn exercise_transfer(
    machine: &mut impl OwnedSessionMachine,
    original: &OwnedSession,
) -> (Enqueue, Enqueue, Enqueue) {
    let receipt = original
        .begin_transfer(machine, "next", OwnershipScope::Session)
        .unwrap();
    original.rollback_transfer(machine, &receipt).unwrap();
    // Actually use the SAME original owner after rollback, before any next transfer.
    let rolled_back = enqueue(machine, original, 40);
    let receipt = original
        .begin_transfer(machine, "next", OwnershipScope::Session)
        .unwrap();
    let next = original.commit_transfer(machine, &receipt).unwrap();
    let stale = original.inject_message_with_sequence(machine, "A", "B", Value::Nat(999), 999);
    let committed = enqueue(machine, &next, 42);
    (rolled_back, stale, committed)
}

fn assert_transfer((rolled_back, stale, committed): (Enqueue, Enqueue, Enqueue)) {
    assert_enqueued(&rolled_back);
    let error = stale.expect_err("original generation actually became stale");
    assert!(matches!(
        &error,
        OwnedSessionEnqueueError::Ownership(OwnershipError::StaleCapability { .. })
    ));
    assert!(error
        .source()
        .unwrap()
        .downcast_ref::<OwnershipError>()
        .is_some());
    assert_enqueued(&committed);
}

fn exercise_scope_and_terminal(
    machine: &mut impl OwnedSessionMachine,
    original: &OwnedSession,
) -> (Enqueue, Enqueue) {
    let fragments = original
        .attenuate_scope(
            machine,
            OwnershipScope::Fragments(BTreeSet::from(["A".into()])),
        )
        .unwrap();
    let scoped = fragments.inject_message_with_sequence(machine, "A", "B", Value::Nat(1), 1);
    fragments.mark_owner_died(machine).unwrap();
    let terminal = fragments.inject_message_with_sequence(machine, "A", "B", Value::Nat(2), 2);
    (scoped, terminal)
}

fn assert_scope_and_terminal((scoped, terminal): (Enqueue, Enqueue)) {
    assert!(matches!(
        scoped,
        Err(OwnedSessionEnqueueError::Ownership(
            OwnershipError::ScopeViolation { .. }
        ))
    ));
    assert!(matches!(
        terminal,
        Err(OwnedSessionEnqueueError::Ownership(
            OwnershipError::Terminal { .. }
        ))
    ));
}

fn exercise_bad_edge(
    machine: &mut impl OwnedSessionMachine,
    owner: &OwnedSession,
) -> (Enqueue, Enqueue) {
    let refused = owner.inject_message_with_sequence(machine, "foreign", "B", Value::Nat(999), 999);
    (refused, enqueue(machine, owner, 43))
}

fn assert_bad_edge((refused, accepted): (Enqueue, Enqueue)) {
    assert!(
        matches!(refused, Err(OwnedSessionEnqueueError::Enqueue { message }) if message == "no buffer for edge foreign → B")
    );
    assert_enqueued(&accepted);
}

fn exercise_released_owner(
    machine: &mut impl OwnedSessionMachine,
    owner: &OwnedSession,
) -> Enqueue {
    owner.release(machine).unwrap();
    owner.inject_message_with_sequence(machine, "A", "B", Value::Nat(999), 999)
}

fn assert_released_owner(actual: &Enqueue) {
    assert!(matches!(
        actual,
        Err(OwnedSessionEnqueueError::Ownership(
            OwnershipError::Unclaimed { .. }
        ))
    ));
}

fn disposed_owner_result(machine: &mut impl OwnedSessionMachine, owner: &OwnedSession) -> Enqueue {
    owner.inject_message_with_sequence(machine, "A", "B", Value::Nat(999), 999)
}

fn assert_disposed_owner_rejected(actual: &Enqueue) {
    assert!(matches!(
        actual,
        Err(OwnedSessionEnqueueError::Ownership(
            OwnershipError::SessionNotFound { .. }
        ))
    ));
}

fn exercise_backpressure(
    machine: &mut impl OwnedSessionMachine,
    owner: &OwnedSession,
) -> (Enqueue, Enqueue) {
    let original = enqueue(machine, owner, 44);
    (
        original,
        owner.inject_message_with_sequence(machine, "A", "B", Value::Nat(999), 999),
    )
}

fn assert_backpressure((original, actual): (Enqueue, Enqueue), policy: BackpressurePolicy) {
    assert_enqueued(&original);
    assert!(matches!(
        (policy, actual),
        (BackpressurePolicy::Block, Ok(EnqueueResult::WouldBlock))
            | (BackpressurePolicy::Drop, Ok(EnqueueResult::Dropped))
            | (BackpressurePolicy::Error, Ok(EnqueueResult::Full))
    ));
}

fn assert_ingress_scope_audit(
    records: &[telltale_machine::ProtocolCriticalCapabilityLifecycleRecord],
    sid: usize,
) {
    use telltale_machine::{
        ProtocolCriticalCapabilityArtifact as Artifact,
        ProtocolCriticalCapabilityLifecycleState as Lifecycle,
    };
    let scope = OwnershipScope::Fragments(BTreeSet::from(["A".into()]));
    let reason = OwnershipError::ScopeViolation {
        session_id: sid,
        owner_id: "original".into(),
        required: OwnershipScope::Session,
        actual: scope.clone(),
    }
    .to_string();
    let rejected: Vec<_> = records
        .iter()
        .filter(|record| {
            matches!(&record.artifact,
                Artifact::OwnershipCapability(capability)
                if capability.session_id == sid && capability.owner_id == "original"
                    && capability.generation == 1 && capability.scope == scope
                    && record.lifecycle == Lifecycle::Rejected
                    && record.reason.as_deref() == Some(reason.as_str())
            )
        })
        .collect();
    assert_eq!(rejected.len(), 1);
    assert_eq!(rejected[0].tick, Some(0));
}

fn single_frame_config(policy: BackpressurePolicy) -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        buffer_config: telltale_machine::buffer::BufferConfig {
            initial_capacity: 1,
            policy,
            ..Default::default()
        },
        ..Default::default()
    }
}

#[test]
fn cooperative_owned_enqueue_preserves_actual_backpressure() {
    for policy in [
        BackpressurePolicy::Block,
        BackpressurePolicy::Drop,
        BackpressurePolicy::Error,
    ] {
        let mut machine = ProtocolMachine::new(single_frame_config(policy));
        let owner = machine
            .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
            .unwrap();
        assert_backpressure(exercise_backpressure(&mut machine, &owner), policy);
        assert_signed_frame(
            machine.sessions().get(owner.session_id()).unwrap().clone(),
            44,
        );
    }
}

#[test]
fn cooperative_owned_enqueue_preserves_signed_sequence() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
        .unwrap();
    assert_enqueued(&enqueue(&mut machine, &owner, 41));
    assert_signed_frame(
        machine.sessions().get(owner.session_id()).unwrap().clone(),
        41,
    );
}

#[test]
fn cooperative_owned_enqueue_rejects_stale_transfer_without_inserting_frame() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
        .unwrap();
    assert_transfer(exercise_transfer(&mut machine, &owner));
    assert_signed_frames(
        machine.sessions().get(owner.session_id()).unwrap().clone(),
        &[40, 42],
    );
}

#[test]
fn cooperative_owned_enqueue_rejects_fragment_and_terminal_owners() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
        .unwrap();
    assert_scope_and_terminal(exercise_scope_and_terminal(&mut machine, &owner));
    assert_ingress_scope_audit(
        &machine.capability_lifecycle_audit_log(),
        owner.session_id(),
    );
    assert!(machine
        .sessions()
        .get(owner.session_id())
        .unwrap()
        .buffers
        .values()
        .all(|buffer| buffer.is_empty()));
}

#[test]
fn cooperative_owned_enqueue_retains_bad_edge_refusal_and_remains_usable() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
        .unwrap();
    assert_bad_edge(exercise_bad_edge(&mut machine, &owner));
    assert_signed_frame(
        machine.sessions().get(owner.session_id()).unwrap().clone(),
        43,
    );
}

#[test]
fn cooperative_owned_enqueue_rejects_released_and_disposed_owner() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = machine
        .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
        .unwrap();
    assert_released_owner(&exercise_released_owner(&mut machine, &owner));
    assert!(machine
        .sessions()
        .get(owner.session_id())
        .unwrap()
        .buffers
        .values()
        .all(|buffer| buffer.is_empty()));
    machine.close_and_reap_session(owner.session_id()).unwrap();
    assert_disposed_owner_rejected(&disposed_owner_result(&mut machine, &owner));
}

#[cfg(feature = "multi-thread")]
mod threaded {
    use super::*;
    use telltale_machine::ThreadedProtocolMachine;

    fn shutdown(machine: ThreadedProtocolMachine) -> usize {
        machine
            .shutdown_worker_pool()
            .expect("same actual original worker pool joined")
            .joined_workers()
    }
    fn snapshot(machine: &ThreadedProtocolMachine, owner: &OwnedSession) -> SessionState {
        machine
            .session_snapshots()
            .remove(&owner.session_id())
            .unwrap()
    }
    fn machine(config: ProtocolMachineConfig) -> (ThreadedProtocolMachine, OwnedSession) {
        let mut machine = ThreadedProtocolMachine::with_workers(config, 2);
        let owner = machine
            .load_choreography_owned(&simple_send_recv_image("A", "B", "msg"), "original")
            .unwrap();
        (machine, owner)
    }
    #[test]
    fn threaded_owned_enqueue_preserves_actual_backpressure() {
        for policy in [
            BackpressurePolicy::Block,
            BackpressurePolicy::Drop,
            BackpressurePolicy::Error,
        ] {
            let (mut machine, owner) = machine(single_frame_config(policy));
            let observed = exercise_backpressure(&mut machine, &owner);
            let frames = snapshot(&machine, &owner);
            let joined = shutdown(machine);
            assert_eq!(joined, 2);
            assert_backpressure(observed, policy);
            assert_signed_frame(frames, 44);
        }
    }
    #[test]
    fn threaded_owned_enqueue_rejects_released_and_disposed_owner() {
        let (mut machine, owner) = machine(ProtocolMachineConfig::default());
        let released = exercise_released_owner(&mut machine, &owner);
        let frames = snapshot(&machine, &owner);
        machine.close_and_reap_session(owner.session_id()).unwrap();
        let disposed = disposed_owner_result(&mut machine, &owner);
        let joined = shutdown(machine);
        assert_eq!(joined, 2);
        assert_released_owner(&released);
        assert!(frames.buffers.values().all(|buffer| buffer.is_empty()));
        assert_disposed_owner_rejected(&disposed);
    }
    #[test]
    fn threaded_owned_enqueue_preserves_signed_sequence() {
        let (mut machine, owner) = machine(ProtocolMachineConfig::default());
        let observed = enqueue(&mut machine, &owner, 41);
        let frames = snapshot(&machine, &owner);
        let joined = shutdown(machine);
        assert_eq!(joined, 2);
        assert_enqueued(&observed);
        assert_signed_frame(frames, 41);
    }
    #[test]
    fn threaded_owned_enqueue_rejects_stale_transfer_without_inserting_frame() {
        let (mut machine, owner) = machine(ProtocolMachineConfig::default());
        let observed = exercise_transfer(&mut machine, &owner);
        let frames = snapshot(&machine, &owner);
        let joined = shutdown(machine);
        assert_eq!(joined, 2);
        assert_transfer(observed);
        assert_signed_frames(frames, &[40, 42]);
    }
    #[test]
    fn threaded_owned_enqueue_rejects_fragment_and_terminal_owners() {
        let (mut machine, owner) = machine(ProtocolMachineConfig::default());
        let observed = exercise_scope_and_terminal(&mut machine, &owner);
        let frames = snapshot(&machine, &owner);
        let audit = machine.capability_lifecycle_audit_log();
        let joined = shutdown(machine);
        assert_eq!(joined, 2);
        assert_scope_and_terminal(observed);
        assert_ingress_scope_audit(&audit, owner.session_id());
        assert!(frames.buffers.values().all(|buffer| buffer.is_empty()));
    }
    #[test]
    fn threaded_owned_enqueue_retains_bad_edge_refusal_and_remains_usable() {
        let (mut machine, owner) = machine(ProtocolMachineConfig::default());
        let observed = exercise_bad_edge(&mut machine, &owner);
        let frames = snapshot(&machine, &owner);
        let joined = shutdown(machine);
        assert_eq!(joined, 2);
        assert_bad_edge(observed);
        assert_signed_frame(frames, 43);
    }
}
