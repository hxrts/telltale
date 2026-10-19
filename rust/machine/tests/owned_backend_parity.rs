#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Exercise real resident ownership transitions through the same public API.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeSet;
use std::error::Error;
use telltale_machine::owned::OwnedSessionMachine;
use telltale_machine::{
    OwnedSession, OwnershipError, OwnershipScope, ProtocolCriticalCapabilityArtifact,
    ProtocolCriticalCapabilityLifecycleRecord, ProtocolCriticalCapabilityLifecycleState,
    ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError, SessionHostMutation,
};
use test_support::simple_send_recv_image;

fn mutation() -> SessionHostMutation {
    SessionHostMutation::SetDefaultHandler {
        handler: "owned-handler".into(),
    }
}

fn exercise_witnesses_and_edge_scope(
    machine: &mut impl OwnedSessionMachine,
    original: &OwnedSession,
    unrelated: &OwnedSession,
) {
    original.apply_host_mutation(machine, mutation()).unwrap();
    unrelated.apply_host_mutation(machine, mutation()).unwrap();
    assert!(matches!(
        original.apply_host_mutation(
            machine,
            SessionHostMutation::UpdateTrace {
                edge: telltale_machine::Edge::new(unrelated.session_id(), "A", "B"),
                trace: vec![],
            }
        ),
        Err(OwnershipError::SessionMismatch { .. })
    ));
    let witness = original.issue_readiness_witness(machine, "ready").unwrap();
    let mut forged = witness.clone();
    forged.predicate_ref = "not-issued".into();
    assert!(matches!(
        original.consume_readiness_witness(machine, &forged),
        Err(OwnershipError::InvalidWitness { .. })
    ));
    original
        .consume_readiness_witness(machine, &witness)
        .unwrap();
    assert!(matches!(
        original.consume_readiness_witness(machine, &witness),
        Err(OwnershipError::WitnessConsumed { .. })
    ));
}

fn exercise_foreign_receipt_refusal(
    machine: &mut impl OwnedSessionMachine,
    original: &OwnedSession,
    unrelated: &OwnedSession,
) {
    let other_receipt = unrelated
        .begin_transfer(machine, "other-next", OwnershipScope::Session)
        .unwrap();
    assert!(matches!(
        original.commit_transfer(machine, &other_receipt),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    assert!(matches!(
        original.rollback_transfer(machine, &other_receipt),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    unrelated
        .rollback_transfer(machine, &other_receipt)
        .unwrap();
    unrelated.apply_host_mutation(machine, mutation()).unwrap();
}

fn exercise_transaction(
    machine: &mut impl OwnedSessionMachine,
    original: &OwnedSession,
    unrelated: &OwnedSession,
) {
    exercise_witnesses_and_edge_scope(machine, original, unrelated);
    exercise_foreign_receipt_refusal(machine, original, unrelated);

    let receipt = original
        .begin_transfer(machine, "worker", OwnershipScope::Session)
        .unwrap();
    assert!(matches!(
        original.begin_transfer(machine, "competitor", OwnershipScope::Session),
        Err(OwnershipError::TransferPending { .. })
    ));
    let mut wrong = receipt.clone();
    wrong.to_owner_id = "forged".into();
    assert!(matches!(
        original.commit_transfer(machine, &wrong),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    assert!(matches!(
        original.rollback_transfer(machine, &wrong),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    original.rollback_transfer(machine, &receipt).unwrap();
    assert!(matches!(
        original.commit_transfer(machine, &receipt),
        Err(OwnershipError::TransferNotPending { .. })
    ));
    original.apply_host_mutation(machine, mutation()).unwrap();

    let stale_witness = original
        .issue_readiness_witness(machine, "before-transfer")
        .unwrap();
    let next_receipt = original
        .begin_transfer(machine, "worker", OwnershipScope::Session)
        .unwrap();
    assert_ne!(next_receipt.claim_id, receipt.claim_id);
    let next = original.commit_transfer(machine, &next_receipt).unwrap();
    assert!(matches!(
        original.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::StaleCapability { .. })
    ));
    assert!(matches!(
        next.consume_readiness_witness(machine, &stale_witness),
        Err(OwnershipError::InvalidWitness { .. })
    ));
    next.apply_host_mutation(machine, mutation()).unwrap();
    let narrow = next
        .attenuate_scope(
            machine,
            OwnershipScope::Fragments(BTreeSet::from(["A".into()])),
        )
        .unwrap();
    assert!(matches!(
        next.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::StaleCapability { .. })
    ));
    assert!(matches!(
        narrow.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::ScopeViolation { .. })
    ));
    assert!(matches!(
        narrow.attenuate_scope(machine, OwnershipScope::Session),
        Err(OwnershipError::ScopeViolation { .. })
    ));
    assert!(matches!(
        narrow.begin_transfer(machine, "escalated", OwnershipScope::Session),
        Err(OwnershipError::ScopeViolation { .. })
    ));
    unrelated.apply_host_mutation(machine, mutation()).unwrap();
}

fn assert_audit(records: &[ProtocolCriticalCapabilityLifecycleRecord]) {
    for (record, owner) in records
        .iter()
        .take(3)
        .zip(["original", "unrelated", "trailing"])
    {
        assert!(matches!(&record.artifact,
            ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability)
            if capability.owner_id == owner && capability.generation == 0));
        assert_eq!(
            record.lifecycle,
            ProtocolCriticalCapabilityLifecycleState::Issued
        );
        assert_eq!(record.tick, Some(0));
    }
    for state in [
        ProtocolCriticalCapabilityLifecycleState::Issued,
        ProtocolCriticalCapabilityLifecycleState::Consumed,
        ProtocolCriticalCapabilityLifecycleState::Rejected,
        ProtocolCriticalCapabilityLifecycleState::RolledBack,
        ProtocolCriticalCapabilityLifecycleState::Committed,
        ProtocolCriticalCapabilityLifecycleState::Invalidated,
    ] {
        assert!(
            records.iter().any(|record| record.lifecycle == state),
            "missing {state:?}"
        );
    }
    assert!(records.iter().any(|record| matches!(
        &record.artifact,
        ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability)
        if capability.owner_id == "original" && capability.generation == 0
    )));
    assert!(records.iter().any(|record| matches!(
        (&record.artifact, record.lifecycle),
        (ProtocolCriticalCapabilityArtifact::OwnershipCapability(capability), ProtocolCriticalCapabilityLifecycleState::Rejected)
        if capability.owner_id == "original" && capability.generation == 0
    )));
}

#[test]
fn cooperative_owned_transactions_retain_real_audit_after_disposal() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = simple_send_recv_image("A", "B", "m");
    let original = machine.load_choreography_owned(&image, "original").unwrap();
    let unrelated = machine
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    let trailing = machine.load_choreography_owned(&image, "trailing").unwrap();
    exercise_transaction(&mut machine, &original, &unrelated);
    let before = machine.capability_lifecycle_audit_log();
    assert_audit(&before);
    machine
        .close_and_reap_session(trailing.session_id())
        .unwrap();
    assert_eq!(before, machine.capability_lifecycle_audit_log());
    machine
        .close_and_reap_session(original.session_id())
        .unwrap();
    assert_eq!(before, machine.capability_lifecycle_audit_log());
    machine
        .close_and_reap_session(original.session_id())
        .unwrap();
    assert_eq!(before, machine.capability_lifecycle_audit_log());
    unrelated
        .apply_host_mutation(&mut machine, mutation())
        .unwrap();
    let mut snapshot = Vec::new();
    ciborium::into_writer(&machine, &mut snapshot).unwrap();
    let restored: ProtocolMachine = ciborium::from_reader(snapshot.as_slice()).unwrap();
    assert_eq!(before, restored.capability_lifecycle_audit_log());
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_owned_transactions_match_cooperative_evidence() {
    use telltale_machine::ThreadedProtocolMachine;
    let image = simple_send_recv_image("A", "B", "m");
    let mut cooperative = ProtocolMachine::new(ProtocolMachineConfig::default());
    let coop_owner = cooperative
        .load_choreography_owned(&image, "original")
        .unwrap();
    let coop_other = cooperative
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    let coop_trailing = cooperative
        .load_choreography_owned(&image, "trailing")
        .unwrap();
    exercise_transaction(&mut cooperative, &coop_owner, &coop_other);
    let expected = cooperative.capability_lifecycle_audit_log();
    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let owner = threaded
        .load_choreography_owned(&image, "original")
        .unwrap();
    let other = threaded
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    let trailing = threaded
        .load_choreography_owned(&image, "trailing")
        .unwrap();
    exercise_transaction(&mut threaded, &owner, &other);
    assert_audit(&threaded.capability_lifecycle_audit_log());
    assert_eq!(expected, threaded.capability_lifecycle_audit_log());
    assert_eq!(
        cooperative.semantic_audit_log(),
        threaded.semantic_audit_log()
    );
    assert_eq!(cooperative.semantic_objects(), threaded.semantic_objects());
    threaded
        .close_and_reap_session(trailing.session_id())
        .unwrap();
    cooperative
        .close_and_reap_session(coop_trailing.session_id())
        .unwrap();
    assert_eq!(expected, threaded.capability_lifecycle_audit_log());
    assert_eq!(expected, cooperative.capability_lifecycle_audit_log());
    threaded.close_and_reap_session(owner.session_id()).unwrap();
    assert_eq!(expected, threaded.capability_lifecycle_audit_log());
    threaded.close_and_reap_session(owner.session_id()).unwrap();
    assert_eq!(expected, threaded.capability_lifecycle_audit_log());
    other
        .apply_host_mutation(&mut threaded, mutation())
        .unwrap();
}

#[test]
fn ownership_contract_error_retains_the_actual_typed_cause() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = simple_send_recv_image("A", "B", "m");
    let owner = machine.load_choreography_owned(&image, "original").unwrap();
    machine.close_and_reap_session(owner.session_id()).unwrap();
    let cause = owner
        .apply_host_mutation(&mut machine, mutation())
        .unwrap_err();
    let error = ProtocolMachineError::OwnershipContract(cause);
    assert!(
        matches!(error.source().unwrap().downcast_ref::<OwnershipError>(), Some(OwnershipError::SessionNotFound { session_id }) if *session_id == owner.session_id())
    );
}

fn exercise_terminal_boundaries(
    machine: &mut impl OwnedSessionMachine,
    owner: &OwnedSession,
    other: &OwnedSession,
) {
    let other_transfer = other
        .begin_transfer(machine, "other-next", OwnershipScope::Session)
        .unwrap();
    assert!(matches!(
        owner.cancel_abandoned_transfer(machine, &other_transfer),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    other.rollback_transfer(machine, &other_transfer).unwrap();
    let receipt = owner
        .begin_transfer(machine, "next", OwnershipScope::Session)
        .unwrap();
    let next = owner.commit_transfer(machine, &receipt).unwrap();
    assert!(matches!(
        owner.mark_owner_died(machine),
        Err(OwnershipError::StaleCapability { .. })
    ));
    let abandoned = next
        .begin_transfer(machine, "abandoned", OwnershipScope::Session)
        .unwrap();
    next.cancel_abandoned_transfer(machine, &abandoned).unwrap();
    assert!(matches!(
        next.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::Terminal { .. })
    ));
    other.mark_owner_died(machine).unwrap();
    assert!(matches!(
        other.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::Terminal { .. })
    ));
}

#[test]
fn cooperative_terminal_ownership_checks_current_handle_and_receipt() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = simple_send_recv_image("A", "B", "m");
    let owner = machine.load_choreography_owned(&image, "original").unwrap();
    let other = machine
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_terminal_boundaries(&mut machine, &owner, &other);
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_terminal_ownership_matches_cooperative_ordering() {
    use telltale_machine::ThreadedProtocolMachine;
    let image = simple_send_recv_image("A", "B", "m");
    let mut cooperative = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = cooperative
        .load_choreography_owned(&image, "original")
        .unwrap();
    let other = cooperative
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_terminal_boundaries(&mut cooperative, &owner, &other);
    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let owner = threaded
        .load_choreography_owned(&image, "original")
        .unwrap();
    let other = threaded
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_terminal_boundaries(&mut threaded, &owner, &other);
    assert_eq!(
        cooperative.capability_lifecycle_audit_log(),
        threaded.capability_lifecycle_audit_log()
    );
    assert_eq!(cooperative.trace(), threaded.trace());
}

fn exercise_failed_commit(
    machine: &mut impl OwnedSessionMachine,
    owner: &OwnedSession,
    other: &OwnedSession,
) {
    let receipt = owner
        .begin_transfer(machine, "next", OwnershipScope::Session)
        .unwrap();
    assert!(matches!(
        other.fault_failed_transfer_commit(machine, &receipt, "foreign"),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    let mut wrong = receipt.clone();
    wrong.claim_id += 1;
    assert!(matches!(
        owner.fault_failed_transfer_commit(machine, &wrong, "mismatched"),
        Err(OwnershipError::ReceiptMismatch { .. })
    ));
    owner.apply_host_mutation(machine, mutation()).unwrap();
    owner
        .fault_failed_transfer_commit(machine, &receipt, "original commit failed")
        .unwrap();
    assert!(matches!(
        owner.apply_host_mutation(machine, mutation()),
        Err(OwnershipError::Terminal { .. })
    ));
    other.apply_host_mutation(machine, mutation()).unwrap();
}

#[test]
fn cooperative_failed_commit_preserves_unrelated_owner() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let image = simple_send_recv_image("A", "B", "m");
    let owner = machine.load_choreography_owned(&image, "original").unwrap();
    let other = machine
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_failed_commit(&mut machine, &owner, &other);
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_failed_commit_matches_cooperative_terminal_evidence() {
    use telltale_machine::ThreadedProtocolMachine;
    let image = simple_send_recv_image("A", "B", "m");
    let mut cooperative = ProtocolMachine::new(ProtocolMachineConfig::default());
    let owner = cooperative
        .load_choreography_owned(&image, "original")
        .unwrap();
    let other = cooperative
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_failed_commit(&mut cooperative, &owner, &other);
    let mut threaded = ThreadedProtocolMachine::with_workers(ProtocolMachineConfig::default(), 2);
    let owner = threaded
        .load_choreography_owned(&image, "original")
        .unwrap();
    let other = threaded
        .load_choreography_owned(&image, "unrelated")
        .unwrap();
    exercise_failed_commit(&mut threaded, &owner, &other);
    assert_eq!(
        cooperative.capability_lifecycle_audit_log(),
        threaded.capability_lifecycle_audit_log()
    );
    assert_eq!(cooperative.trace(), threaded.trace());
}
