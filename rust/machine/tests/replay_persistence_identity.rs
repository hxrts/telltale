#![cfg(not(target_arch = "wasm32"))]
//! Replay fragment persistence and semantic-object identity tests.
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use telltale_bridge::{semantic_objects_from_json, semantic_objects_to_json};
use telltale_machine::model::effects::{
    EffectOutcome, EffectResponse, EffectTraceEntry, RecordingEffectHandler, SendDecision,
};
use telltale_machine::{
    OwnershipScope, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineSemanticObjects,
    SemanticAuditRecord,
};

use test_support::{simple_send_recv_image, PassthroughHandler};

#[derive(Debug)]
struct RunView {
    fragment: telltale_machine::CanonicalReplayFragmentV1,
    semantic_objects: ProtocolMachineSemanticObjects,
    bridge_roundtrip_objects: ProtocolMachineSemanticObjects,
    effect_semantics: Vec<(String, serde_json::Value, serde_json::Value, u64)>,
}

fn normalize_semantic_objects(
    mut objects: ProtocolMachineSemanticObjects,
) -> ProtocolMachineSemanticObjects {
    fn sort_by_json<T: serde::Serialize>(values: &mut [T]) {
        values.sort_by_key(|value| serde_json::to_string(value).expect("serialize sortable value"));
    }

    for operation in &mut objects.operation_instances {
        if operation.handler_identity.is_some() {
            operation.handler_identity = Some("<normalized-handler>".to_string());
        }
    }
    for effect in &mut objects.outstanding_effects {
        effect.handler_identity = "<normalized-handler>".to_string();
    }
    for read in &mut objects.observed_reads {
        read.handler_identity = "<normalized-handler>".to_string();
    }

    sort_by_json(&mut objects.operation_instances);
    sort_by_json(&mut objects.outstanding_effects);
    sort_by_json(&mut objects.semantic_handoffs);
    sort_by_json(&mut objects.transformation_obligations);
    sort_by_json(&mut objects.authoritative_reads);
    sort_by_json(&mut objects.observed_reads);
    sort_by_json(&mut objects.materialization_proofs);
    sort_by_json(&mut objects.canonical_handles);
    sort_by_json(&mut objects.publication_events);
    sort_by_json(&mut objects.prestate_bindings);
    sort_by_json(&mut objects.agreement_profiles);
    sort_by_json(&mut objects.agreement_contracts);
    sort_by_json(&mut objects.agreement_evidence);
    sort_by_json(&mut objects.agreement_states);
    sort_by_json(&mut objects.regions);
    sort_by_json(&mut objects.progress_contracts);
    sort_by_json(&mut objects.progress_transitions);
    objects
}

fn effect_semantics(
    machine: &ProtocolMachine,
) -> Vec<(String, serde_json::Value, serde_json::Value, u64)> {
    machine
        .effect_trace()
        .iter()
        .map(|entry| {
            (
                entry.effect_kind.clone(),
                entry.inputs.clone(),
                entry.outputs.clone(),
                entry.ordering_key,
            )
        })
        .collect()
}

fn normalize_semantic_audit_log(records: &[SemanticAuditRecord]) -> Vec<SemanticAuditRecord> {
    records
        .iter()
        .cloned()
        .map(|record| match record {
            SemanticAuditRecord::EffectObservation {
                effect_id,
                ordering_key,
                session,
                effect_kind,
                effect_interface,
                effect_operation,
                inputs,
                outputs,
                ..
            } => SemanticAuditRecord::EffectObservation {
                effect_id,
                ordering_key,
                session,
                effect_kind,
                effect_interface,
                effect_operation,
                handler_identity: "<normalized-handler>".to_string(),
                inputs,
                outputs,
            },
            other => other,
        })
        .collect()
}

fn capture_run_view(machine: &ProtocolMachine) -> RunView {
    let fragment = machine.canonical_replay_fragment();
    let semantic_objects = normalize_semantic_objects(machine.semantic_objects());
    let bridge_roundtrip_objects = normalize_semantic_objects(
        semantic_objects_from_json(
            semantic_objects_to_json(&machine.semantic_objects()).expect("encode semantic objects"),
        )
        .expect("bridge roundtrip semantic objects"),
    );
    RunView {
        fragment,
        semantic_objects,
        bridge_roundtrip_objects,
        effect_semantics: effect_semantics(machine),
    }
}

fn run_baseline_and_record(max_steps: usize) -> (String, Vec<EffectTraceEntry>, RunView) {
    let image = simple_send_recv_image("A", "B", "m");
    let handler = PassthroughHandler;
    let recording = RecordingEffectHandler::new(&handler);

    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&image)
        .expect("load baseline machine");
    let snapshot = serde_yaml::to_string(&machine).expect("serialize baseline snapshot");
    machine
        .run(&recording, max_steps)
        .expect("run baseline machine");

    (
        snapshot,
        recording.effect_trace(),
        capture_run_view(&machine),
    )
}

#[test]
fn replay_and_persistence_histories_preserve_semantic_identity() {
    let (snapshot, recorded_effects, baseline) = run_baseline_and_record(64);
    let handler = PassthroughHandler;

    let mut restored_run: ProtocolMachine =
        serde_yaml::from_str(&snapshot).expect("restore machine from snapshot");
    restored_run
        .run(&handler, 64)
        .expect("run restored machine");
    let restored = capture_run_view(&restored_run);

    let mut replay_run: ProtocolMachine =
        serde_yaml::from_str(&snapshot).expect("restore machine for replay");
    replay_run
        .run_replay(&handler, &recorded_effects, 64)
        .expect("run replay machine");
    let replay = capture_run_view(&replay_run);

    let fragment_roundtrip: telltale_machine::CanonicalReplayFragmentV1 = serde_json::from_str(
        &serde_json::to_string(&baseline.fragment).expect("serialize replay fragment"),
    )
    .expect("deserialize replay fragment");

    assert_eq!(
        baseline.fragment.obs_trace, restored.fragment.obs_trace,
        "snapshot/restore run must preserve observable replay fragment"
    );
    assert_eq!(
        baseline.fragment.obs_trace, replay.fragment.obs_trace,
        "record/replay must preserve observable replay fragment"
    );
    assert_eq!(
        baseline.fragment.semantic_audit_log, restored.fragment.semantic_audit_log,
        "snapshot/restore run must preserve semantic audit log"
    );
    assert_eq!(
        normalize_semantic_audit_log(&baseline.fragment.semantic_audit_log),
        normalize_semantic_audit_log(&replay.fragment.semantic_audit_log),
        "record/replay must preserve semantic audit semantics apart from replay handler provenance"
    );
    assert_ne!(
        baseline.fragment.semantic_audit_log, replay.fragment.semantic_audit_log,
        "replay should remain distinguishable from baseline at the raw audit-provenance layer"
    );
    assert_eq!(
        baseline.semantic_objects, restored.semantic_objects,
        "snapshot/restore run must preserve semantic objects"
    );
    assert_eq!(
        baseline.semantic_objects, replay.semantic_objects,
        "record/replay must preserve semantic objects"
    );
    assert_eq!(
        baseline.bridge_roundtrip_objects, baseline.semantic_objects,
        "bridge semantic-object roundtrip must preserve the canonical semantic view"
    );
    assert_eq!(
        restored.bridge_roundtrip_objects, restored.semantic_objects,
        "bridge semantic-object roundtrip must preserve the restored semantic view"
    );
    assert_eq!(
        replay.bridge_roundtrip_objects, replay.semantic_objects,
        "bridge semantic-object roundtrip must preserve the replayed semantic view"
    );
    assert_eq!(
        baseline.effect_semantics, restored.effect_semantics,
        "snapshot/restore run must preserve effect semantics"
    );
    assert_eq!(
        baseline.effect_semantics, replay.effect_semantics,
        "record/replay must preserve effect semantics"
    );
    assert_eq!(
        fragment_roundtrip.semantic_objects, baseline.fragment.semantic_objects,
        "replay-fragment JSON roundtrip must preserve semantic objects"
    );
    assert_eq!(
        fragment_roundtrip.semantic_audit_log, baseline.fragment.semantic_audit_log,
        "replay-fragment JSON roundtrip must preserve semantic audit log"
    );
}

#[test]
fn tampered_recorded_effects_are_detected_by_semantic_identity_harness() {
    let (snapshot, recorded_effects, baseline) = run_baseline_and_record(64);
    let handler = PassthroughHandler;

    let mut tampered_effects = recorded_effects.clone();
    let first = tampered_effects
        .iter_mut()
        .find(|entry| entry.effect_kind == "send_decision")
        .expect("baseline run should record a send_decision effect");
    assert_eq!(
        first.effect_kind, "send_decision",
        "baseline corpus expects a replayed send_decision effect to control delivery"
    );
    first.outputs = serde_json::to_value(EffectOutcome::success(EffectResponse::SendDecision {
        decision: SendDecision::Drop,
    }))
    .expect("serialize tampered drop outcome");

    let mut tampered_replay: ProtocolMachine =
        serde_yaml::from_str(&snapshot).expect("restore machine for tampered replay");
    let error = tampered_replay
        .run_replay(&handler, &tampered_effects, 64)
        .expect_err("tampered replay must fail closed once replay semantics diverge");

    assert!(
        matches!(
            error,
            telltale_machine::ProtocolMachineError::HandlerError(telltale_machine::EffectFailure {
                kind: telltale_machine::EffectFailureKind::Determinism,
                ..
            })
        ),
        "tampered replay should surface a determinism fault instead of silently diverging"
    );
    assert_ne!(
        baseline.effect_semantics, effect_semantics(&tampered_replay),
        "tampered replay should have consumed a meaningfully different effect history before failing"
    );
}

#[test]
fn ownership_transfer_witness_invalidation_survives_snapshot_restore() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let sid = machine
        .load_choreography(&image)
        .expect("load choreography");
    let owner = machine
        .sessions_mut()
        .claim_ownership(sid, "owner/a", OwnershipScope::Session)
        .expect("claim initial ownership");
    let witness = machine
        .sessions_mut()
        .issue_readiness_witness(&owner, "session.ready")
        .expect("issue readiness witness");
    let receipt = machine
        .sessions_mut()
        .begin_ownership_transfer(&owner, "owner/b", OwnershipScope::Session)
        .expect("begin ownership transfer");
    let next_owner = machine
        .sessions_mut()
        .commit_ownership_transfer(&receipt)
        .expect("commit ownership transfer");

    let snapshot = serde_yaml::to_string(&machine).expect("serialize post-transfer machine");
    let mut restored: ProtocolMachine =
        serde_yaml::from_str(&snapshot).expect("restore post-transfer machine");

    let stale_err = restored
        .sessions_mut()
        .consume_readiness_witness(&owner, &witness)
        .expect_err("pre-transfer witness must stay stale after restore");
    assert!(
        matches!(
            stale_err,
            telltale_machine::OwnershipError::StaleCapability { .. }
        ),
        "restored machine should preserve stale-capability rejection"
    );

    let invalid_err = restored
        .sessions_mut()
        .consume_readiness_witness(&next_owner, &witness)
        .expect_err(
            "pre-transfer witness must stay invalid under the committed owner after restore",
        );
    assert!(
        matches!(
            invalid_err,
            telltale_machine::OwnershipError::InvalidWitness { .. }
        ),
        "restored machine should preserve witness invalidation semantics"
    );
}
