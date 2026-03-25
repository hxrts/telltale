//! Protocol-machine semantic object export helpers for Lean bridge payloads.

use serde::{Deserialize, Serialize};
use serde_json::Value as Json;

pub use telltale_machine::model::semantic_objects::{
    AuthoritativeRead, AuthoritativeReadKind, AuthoritativeReadLifecycle, CanonicalHandle,
    CanonicalHandleKind, DelegationStatus, MaterializationProof, ObservedRead, OperationInstance,
    OperationPhase, OutstandingEffect, OutstandingEffectStatus, OwnershipScope, ProgressContract,
    ProgressState, ProgressTransition, ProtocolMachineSemanticObjects, PublicationEvent,
    PublicationObserverClass, PublicationStatus, SemanticHandoff, TransformationObligation,
    SEMANTIC_OBJECTS_SCHEMA_VERSION,
};

/// Schema version for protocol-machine semantic-object payloads.
#[must_use]
pub fn canonical_semantic_objects_schema_version() -> String {
    SEMANTIC_OBJECTS_SCHEMA_VERSION.to_string()
}

/// One observation annotated with the scheduler tick at which it occurred.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(bound(deserialize = "E: Deserialize<'de>"))]
pub struct TickedObsEvent<E> {
    pub tick: u64,
    pub event: E,
}

/// Convert a semantic-object payload to canonical JSON.
pub fn semantic_objects_to_json(
    payload: &ProtocolMachineSemanticObjects,
) -> Result<Json, serde_json::Error> {
    serde_json::to_value(payload)
}

/// Decode a semantic-object payload from JSON.
pub fn semantic_objects_from_json(
    value: Json,
) -> Result<ProtocolMachineSemanticObjects, serde_json::Error> {
    serde_json::from_value(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_object_payload_roundtrip_via_json_helpers() {
        let payload = ProtocolMachineSemanticObjects {
            schema_version: canonical_semantic_objects_schema_version(),
            operation_instances: vec![OperationInstance {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                owner_id: None,
                kind: "readChannel".to_string(),
                phase: OperationPhase::Succeeded,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: vec![1],
                dependent_operation_ids: Vec::new(),
                terminal_publication: Some("effect.succeeded".to_string()),
                budget_ticks: Some(1),
                requires_proof: false,
            }],
            outstanding_effects: vec![OutstandingEffect {
                effect_id: 1,
                operation_id: "effect:1".to_string(),
                session: Some(1),
                owner_id: Some("runtime/owner".to_string()),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("readChannel".to_string()),
                effect_kind: "invoke_step".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Succeeded,
                ordering_key: 1,
                budget_ticks: Some(1),
                retry_policy: "forbid_late_results".to_string(),
                invalidation_token: "effect:1:live".to_string(),
                completed_at_tick: Some(1),
                inputs: serde_json::json!({"session": 1}),
                outputs: serde_json::json!({"status": "success"}),
            }],
            semantic_handoffs: vec![SemanticHandoff {
                handoff_id: 7,
                session: 1,
                from_coro: 0,
                to_coro: 1,
                revoked_owner_id: "coro:0".to_string(),
                activated_owner_id: "coro:1".to_string(),
                scope: OwnershipScope::Fragments(vec!["A".to_string()]),
                status: DelegationStatus::Committed,
                tick: 9,
                reason: None,
            }],
            transformation_obligations: vec![TransformationObligation {
                obligation_id: "handoff:7".to_string(),
                handoff_id: 7,
                session: 1,
                transformed_fragments: vec!["A".to_string()],
                affected_operation_ids: vec!["effect:1".to_string()],
                affected_effect_ids: vec![1],
                transported_effect_ids: vec![1],
                invalidated_effect_ids: Vec::new(),
                witness_policy: "transport_pending_invalidate_blocked".to_string(),
                publication_revoked_from: "coro:0".to_string(),
                publication_activated_to: "coro:1".to_string(),
                scope: OwnershipScope::Fragments(vec!["A".to_string()]),
                status: DelegationStatus::Committed,
                tick: 9,
                reason: None,
            }],
            authoritative_reads: vec![AuthoritativeRead {
                read_id: "readiness:1:Issued".to_string(),
                session: Some(1),
                owner_id: Some("runtime/owner".to_string()),
                kind: AuthoritativeReadKind::Readiness,
                lifecycle: AuthoritativeReadLifecycle::Issued,
                predicate_ref: Some("session.ready".to_string()),
                witness_id: Some(1),
                generation: Some(0),
                reason: None,
            }],
            observed_reads: vec![ObservedRead {
                read_id: "effect:1".to_string(),
                session: Some(1),
                effect_id: 1,
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("readChannel".to_string()),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Succeeded,
            }],
            materialization_proofs: vec![MaterializationProof {
                proof_id: "session.ready:digest".to_string(),
                session: None,
                predicate_ref: "session.ready".to_string(),
                witness_ref: Some("witness".to_string()),
                output_digest: "digest".to_string(),
                passed: true,
            }],
            canonical_handles: vec![CanonicalHandle {
                handle_id: "materialization:digest".to_string(),
                session: None,
                owner_id: None,
                kind: CanonicalHandleKind::Materialization,
                proof_ref: Some("session.ready:digest".to_string()),
            }],
            publication_events: vec![PublicationEvent {
                publication_id: "materialization:session.ready:digest:materialization.succeeded"
                    .to_string(),
                session: None,
                operation_id: "materialization:session.ready:digest".to_string(),
                owner_id: None,
                publication: "materialization.succeeded".to_string(),
                observer_class: PublicationObserverClass::Audit,
                status: PublicationStatus::Published,
                proof_ref: Some("session.ready:digest".to_string()),
                handle_ref: Some("materialization:digest".to_string()),
                reason: None,
            }],
            progress_contracts: vec![ProgressContract {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                state: ProgressState::Succeeded,
                last_ordering_key: Some(1),
                bounded: true,
                budget_ticks: Some(1),
                last_progress_tick: Some(1),
                escalated_at_tick: None,
                reason: None,
            }],
            progress_transitions: vec![ProgressTransition {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                from_state: ProgressState::Pending,
                to_state: ProgressState::Succeeded,
                tick: 1,
                reason: None,
            }],
        };

        let encoded = semantic_objects_to_json(&payload).expect("encode semantic objects");
        let decoded = semantic_objects_from_json(encoded).expect("decode semantic objects");
        assert_eq!(decoded.schema_version, SEMANTIC_OBJECTS_SCHEMA_VERSION);
        assert_eq!(decoded, payload);
    }
}
