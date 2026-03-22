//! Protocol-machine semantic object export helpers for Lean bridge payloads.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use serde_json::Value as Json;

/// Schema version for protocol-machine semantic-object payloads.
pub const SEMANTIC_OBJECTS_SCHEMA_VERSION: &str = "protocol_machine.semantic_objects.v1";

#[must_use]
pub fn default_semantic_objects_schema_version() -> String {
    SEMANTIC_OBJECTS_SCHEMA_VERSION.to_string()
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OperationPhase {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    TimedOut,
    HandedOff,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OutstandingEffectStatus {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    Invalidated,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AuthoritativeReadKind {
    Readiness,
    Cancellation,
    Timeout,
    OutputCondition,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AuthoritativeReadLifecycle {
    Issued,
    Consumed,
    Rejected,
    Verified,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CanonicalHandleKind {
    Materialization,
    Handoff,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ProgressState {
    Pending,
    Blocked,
    Succeeded,
    Failed,
    Cancelled,
    TimedOut,
    HandedOff,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum OwnershipScope {
    Session,
    Fragments(BTreeSet<String>),
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum DelegationStatus {
    Committed,
    RolledBack,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct OperationInstance {
    pub operation_id: String,
    pub session: Option<u64>,
    pub owner_id: Option<String>,
    pub kind: String,
    pub phase: OperationPhase,
    pub handler_identity: Option<String>,
    pub effect_ids: Vec<u64>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct OutstandingEffect {
    pub effect_id: u64,
    pub operation_id: String,
    pub session: Option<u64>,
    pub effect_interface: Option<String>,
    pub effect_operation: Option<String>,
    pub effect_kind: String,
    pub handler_identity: String,
    pub status: OutstandingEffectStatus,
    pub ordering_key: u64,
    pub inputs: Json,
    pub outputs: Json,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct SemanticHandoff {
    pub handoff_id: u64,
    pub session: u64,
    pub from_coro: u64,
    pub to_coro: u64,
    pub scope: OwnershipScope,
    pub status: DelegationStatus,
    pub tick: u64,
    pub reason: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct AuthoritativeRead {
    pub read_id: String,
    pub session: Option<u64>,
    pub owner_id: Option<String>,
    pub kind: AuthoritativeReadKind,
    pub lifecycle: AuthoritativeReadLifecycle,
    pub predicate_ref: Option<String>,
    pub witness_id: Option<u64>,
    pub generation: Option<u64>,
    pub reason: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ObservedRead {
    pub read_id: String,
    pub session: Option<u64>,
    pub effect_id: u64,
    pub effect_interface: Option<String>,
    pub effect_operation: Option<String>,
    pub handler_identity: String,
    pub status: OutstandingEffectStatus,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct MaterializationProof {
    pub proof_id: String,
    pub session: Option<u64>,
    pub predicate_ref: String,
    pub witness_ref: Option<String>,
    pub output_digest: String,
    pub passed: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct CanonicalHandle {
    pub handle_id: String,
    pub session: Option<u64>,
    pub owner_id: Option<String>,
    pub kind: CanonicalHandleKind,
    pub proof_ref: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProgressContract {
    pub operation_id: String,
    pub session: Option<u64>,
    pub state: ProgressState,
    pub last_ordering_key: Option<u64>,
    pub bounded: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(bound(deserialize = "E: Deserialize<'de>"))]
pub struct TickedObsEvent<E> {
    pub tick: u64,
    pub event: E,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct ProtocolMachineSemanticObjects {
    #[serde(default = "default_semantic_objects_schema_version")]
    pub schema_version: String,
    pub operation_instances: Vec<OperationInstance>,
    pub outstanding_effects: Vec<OutstandingEffect>,
    pub semantic_handoffs: Vec<SemanticHandoff>,
    pub authoritative_reads: Vec<AuthoritativeRead>,
    pub observed_reads: Vec<ObservedRead>,
    pub materialization_proofs: Vec<MaterializationProof>,
    pub canonical_handles: Vec<CanonicalHandle>,
    pub progress_contracts: Vec<ProgressContract>,
}

impl Default for ProtocolMachineSemanticObjects {
    fn default() -> Self {
        Self {
            schema_version: default_semantic_objects_schema_version(),
            operation_instances: Vec::new(),
            outstanding_effects: Vec::new(),
            semantic_handoffs: Vec::new(),
            authoritative_reads: Vec::new(),
            observed_reads: Vec::new(),
            materialization_proofs: Vec::new(),
            canonical_handles: Vec::new(),
            progress_contracts: Vec::new(),
        }
    }
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
            schema_version: default_semantic_objects_schema_version(),
            operation_instances: vec![OperationInstance {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                owner_id: None,
                kind: "readChannel".to_string(),
                phase: OperationPhase::Succeeded,
                handler_identity: Some("host/runtime".to_string()),
                effect_ids: vec![1],
            }],
            outstanding_effects: vec![OutstandingEffect {
                effect_id: 1,
                operation_id: "effect:1".to_string(),
                session: Some(1),
                effect_interface: Some("Runtime".to_string()),
                effect_operation: Some("readChannel".to_string()),
                effect_kind: "invoke_step".to_string(),
                handler_identity: "host/runtime".to_string(),
                status: OutstandingEffectStatus::Succeeded,
                ordering_key: 1,
                inputs: serde_json::json!({"session": 1}),
                outputs: serde_json::json!({"status": "success"}),
            }],
            semantic_handoffs: vec![SemanticHandoff {
                handoff_id: 7,
                session: 1,
                from_coro: 0,
                to_coro: 1,
                scope: OwnershipScope::Fragments(BTreeSet::from(["A".to_string()])),
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
            progress_contracts: vec![ProgressContract {
                operation_id: "effect:1".to_string(),
                session: Some(1),
                state: ProgressState::Succeeded,
                last_ordering_key: Some(1),
                bounded: true,
            }],
        };

        let encoded = semantic_objects_to_json(&payload).expect("encode semantic objects");
        let decoded = semantic_objects_from_json(encoded).expect("decode semantic objects");
        assert_eq!(decoded.schema_version, SEMANTIC_OBJECTS_SCHEMA_VERSION);
        assert_eq!(decoded, payload);
    }
}
