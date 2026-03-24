use serde_json::json;
use std::collections::BTreeMap;
use telltale_lean_bridge::{
    ensure_supported_schema_version, export_protocol_bundle, ChoreographyJson, InvariantClaims,
    ProtocolBundle, ProtocolMachineReplayBundle, ProtocolMachineRunInput, ProtocolMachineRunOutput,
    ProtocolMachineSemanticObjects, LEAN_BRIDGE_SCHEMA_VERSION, PROTOCOL_BUNDLE_SCHEMA_VERSION,
    SEMANTIC_OBJECTS_SCHEMA_VERSION,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[test]
fn vm_run_output_missing_schema_version_is_rejected() {
    let legacy = json!({
        "trace": [{
            "kind": "sent",
            "tick": 1,
            "sender": "A",
            "receiver": "B",
            "label": "msg"
        }],
        "sessions": [{
            "sid": 0,
            "terminal": true
        }],
        "steps_executed": 2,
        "concurrency": 1,
        "status": "ok"
    });

    let err = serde_json::from_value::<ProtocolMachineRunOutput>(legacy)
        .expect_err("ProtocolMachineRunOutput without schema_version should be rejected");
    assert!(err.to_string().contains("missing field `schema_version`"));
}

#[test]
fn vm_run_input_roundtrip_preserves_schema_version() {
    let input = ProtocolMachineRunInput {
        schema_version: LEAN_BRIDGE_SCHEMA_VERSION.to_string(),
        choreographies: vec![ChoreographyJson {
            schema_version: LEAN_BRIDGE_SCHEMA_VERSION.to_string(),
            global_type: json!({"kind":"end"}),
            roles: vec!["A".to_string()],
        }],
        concurrency: 1,
        max_steps: 5,
    };

    let encoded = serde_json::to_value(&input).expect("serialize ProtocolMachineRunInput");
    assert_eq!(encoded["schema_version"], LEAN_BRIDGE_SCHEMA_VERSION);

    let decoded: ProtocolMachineRunInput =
        serde_json::from_value(encoded).expect("deserialize ProtocolMachineRunInput");
    assert_eq!(decoded.schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
    assert_eq!(
        decoded.choreographies[0].schema_version,
        LEAN_BRIDGE_SCHEMA_VERSION
    );
}

#[test]
fn replay_trace_bundle_missing_schema_version_is_rejected() {
    let legacy = json!({
        "semantic_audit": [{
            "kind": "sent",
            "session_index": 0,
            "sender": "A",
            "receiver": "B",
            "label": "msg"
        }],
        "effect_trace": [],
        "output_condition_trace": []
    });

    let err = serde_json::from_value::<ProtocolMachineReplayBundle>(legacy)
        .expect_err("ProtocolMachineReplayBundle without schema_version should be rejected");
    assert!(err.to_string().contains("missing field `schema_version`"));
}

#[test]
fn schema_validator_accepts_current_and_rejects_unknown() {
    assert!(
        ensure_supported_schema_version(LEAN_BRIDGE_SCHEMA_VERSION, "ProtocolMachineRunInput")
            .is_ok()
    );
    assert!(ensure_supported_schema_version("legacy.v0", "ProtocolMachineRunInput").is_err());
}

#[test]
fn protocol_bundle_roundtrip_preserves_schema_version() {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End),
    );

    let bundle = export_protocol_bundle(&global, &locals, InvariantClaims::default());
    let encoded = serde_json::to_value(&bundle).expect("serialize ProtocolBundle");
    assert_eq!(encoded["schema_version"], PROTOCOL_BUNDLE_SCHEMA_VERSION);

    let decoded: ProtocolBundle =
        serde_json::from_value(encoded).expect("deserialize ProtocolBundle");
    assert_eq!(decoded.schema_version, PROTOCOL_BUNDLE_SCHEMA_VERSION);
}

#[test]
fn protocol_bundle_missing_schema_version_is_rejected() {
    let legacy = json!({
        "global_type": { "kind": "end" },
        "local_types": {},
        "claims": {
            "schema_version": LEAN_BRIDGE_SCHEMA_VERSION,
            "liveness": null,
            "distributed": {},
            "classical": {}
        }
    });
    let err = serde_json::from_value::<ProtocolBundle>(legacy)
        .expect_err("ProtocolBundle without schema_version should be rejected");
    assert!(err.to_string().contains("missing field `schema_version`"));
}

#[test]
fn semantic_objects_missing_schema_version_is_rejected() {
    let payload = json!({
        "operation_instances": [],
        "outstanding_effects": [],
        "semantic_handoffs": [],
        "authoritative_reads": [],
        "observed_reads": [],
        "materialization_proofs": [],
        "canonical_handles": [],
        "progress_contracts": []
    });

    let err = serde_json::from_value::<ProtocolMachineSemanticObjects>(payload)
        .expect_err("ProtocolMachineSemanticObjects without schema_version should be rejected");
    assert!(err.to_string().contains("missing field `schema_version`"));
}

#[test]
fn semantic_objects_roundtrip_preserves_schema_version() {
    let payload = json!({
        "schema_version": SEMANTIC_OBJECTS_SCHEMA_VERSION,
        "operation_instances": [{
            "operation_id": "effect:1",
            "session": 1,
            "owner_id": null,
            "kind": "readChannel",
            "phase": "succeeded",
            "handler_identity": "host/runtime",
            "effect_ids": [1],
            "dependent_operation_ids": [],
            "terminal_publication": "effect.succeeded",
            "budget_ticks": 1,
            "requires_proof": false
        }],
        "outstanding_effects": [{
            "effect_id": 1,
            "operation_id": "effect:1",
            "session": 1,
            "owner_id": "runtime/owner",
            "effect_interface": "Runtime",
            "effect_operation": "readChannel",
            "effect_kind": "invoke_step",
            "handler_identity": "host/runtime",
            "status": "succeeded",
            "ordering_key": 1,
            "budget_ticks": 1,
            "retry_policy": "forbid_late_results",
            "invalidation_token": "effect:1:live",
            "completed_at_tick": 1,
            "inputs": {"session": 1},
            "outputs": {"status": "success"}
        }],
        "semantic_handoffs": [{
            "handoff_id": 3,
            "session": 1,
            "from_coro": 0,
            "to_coro": 1,
            "revoked_owner_id": "coro:0",
            "activated_owner_id": "coro:1",
            "scope": { "Fragments": ["A"] },
            "status": "Committed",
            "tick": 7,
            "reason": null
        }],
        "transformation_obligations": [{
            "obligation_id": "handoff:3",
            "handoff_id": 3,
            "session": 1,
            "transformed_fragments": ["A"],
            "affected_operation_ids": ["effect:1"],
            "affected_effect_ids": [1],
            "transported_effect_ids": [1],
            "invalidated_effect_ids": [],
            "witness_policy": "transport_pending_invalidate_blocked",
            "publication_revoked_from": "coro:0",
            "publication_activated_to": "coro:1",
            "scope": { "Fragments": ["A"] },
            "status": "Committed",
            "tick": 7,
            "reason": null
        }],
        "authoritative_reads": [{
            "read_id": "readiness:1:Issued",
            "session": 1,
            "owner_id": "runtime/owner",
            "kind": "readiness",
            "lifecycle": "issued",
            "predicate_ref": "session.ready",
            "witness_id": 1,
            "generation": 0,
            "reason": null
        }],
        "observed_reads": [{
            "read_id": "effect:1",
            "session": 1,
            "effect_id": 1,
            "effect_interface": "Runtime",
            "effect_operation": "readChannel",
            "handler_identity": "host/runtime",
            "status": "succeeded"
        }],
        "materialization_proofs": [{
            "proof_id": "session.ready:digest",
            "session": null,
            "predicate_ref": "session.ready",
            "witness_ref": "w1",
            "output_digest": "digest",
            "passed": true
        }],
        "canonical_handles": [{
            "handle_id": "materialization:digest",
            "session": null,
            "owner_id": null,
            "kind": "materialization",
            "proof_ref": "session.ready:digest"
        }],
        "publication_events": [{
            "publication_id": "materialization:session.ready:digest:materialization.succeeded",
            "session": null,
            "operation_id": "materialization:session.ready:digest",
            "owner_id": null,
            "publication": "materialization.succeeded",
            "observer_class": "audit",
            "status": "published",
            "proof_ref": "session.ready:digest",
            "handle_ref": "materialization:digest",
            "reason": null
        }],
        "progress_contracts": [{
            "operation_id": "effect:1",
            "session": 1,
            "state": "succeeded",
            "last_ordering_key": 1,
            "bounded": true
        }]
    });

    let decoded: ProtocolMachineSemanticObjects =
        serde_json::from_value(payload.clone()).expect("decode semantic objects");
    assert_eq!(decoded.schema_version, SEMANTIC_OBJECTS_SCHEMA_VERSION);

    let encoded = serde_json::to_value(decoded).expect("encode semantic objects");
    assert_eq!(encoded["schema_version"], SEMANTIC_OBJECTS_SCHEMA_VERSION);
}

#[test]
fn vm_run_output_roundtrip_preserves_semantic_objects() {
    let payload = json!({
        "schema_version": LEAN_BRIDGE_SCHEMA_VERSION,
        "trace": [],
        "sessions": [],
        "steps_executed": 0,
        "concurrency": 1,
        "status": "ok",
        "effect_exchanges": [{
            "effect_id": 9,
            "handler_identity": "host/runtime",
            "ordering_key": 3,
            "request": {
                "effect_id": 9,
                "tick": 3,
                "session": 2,
                "operation_id": "effect:9",
                "metadata": {
                    "interface_name": "Transport",
                    "operation_name": "sendDecision",
                    "authority_class": "command",
                    "admissibility": "declared_use_only",
                    "totality": "immediate",
                    "timeout_policy": "none",
                    "reentrancy_policy": "allow",
                    "handler_domain": "external"
                },
                "body": {
                    "kind": "send_decision",
                    "role": "A",
                    "partner": "B",
                    "label": "msg",
                    "state": [],
                    "payload": null
                }
            },
            "outcome": {
                "status": {
                    "status": "blocked"
                },
                "response": null
            }
        }],
        "semantic_objects": {
            "schema_version": SEMANTIC_OBJECTS_SCHEMA_VERSION,
            "operation_instances": [{
                "operation_id": "effect:9",
                "session": 2,
                "owner_id": "owner/a",
                "kind": "sendDecision",
                "phase": "blocked",
                "handler_identity": "host/runtime",
                "effect_ids": [9],
                "dependent_operation_ids": [],
                "terminal_publication": "effect.blocked",
                "budget_ticks": 1,
                "requires_proof": false
            }],
            "outstanding_effects": [{
                "effect_id": 9,
                "operation_id": "effect:9",
                "session": 2,
                "owner_id": "owner/a",
                "effect_interface": "Transport",
                "effect_operation": "sendDecision",
                "effect_kind": "send_decision",
                "handler_identity": "host/runtime",
                "status": "blocked",
                "ordering_key": 3,
                "budget_ticks": 1,
                "retry_policy": "forbid_late_results",
                "invalidation_token": "effect:9:live",
                "completed_at_tick": 3,
                "inputs": { "session": 2 },
                "outputs": { "status": "blocked" }
            }],
            "semantic_handoffs": [],
            "transformation_obligations": [],
            "authoritative_reads": [],
            "observed_reads": [],
            "materialization_proofs": [],
            "canonical_handles": [],
            "publication_events": [{
                "publication_id": "effect:9:effect.blocked",
                "session": 2,
                "operation_id": "effect:9",
                "owner_id": "owner/a",
                "publication": "effect.blocked",
                "observer_class": "canonical",
                "status": "published",
                "proof_ref": null,
                "handle_ref": null,
                "reason": null
            }],
            "progress_contracts": []
        }
    });

    let decoded: ProtocolMachineRunOutput =
        serde_json::from_value(payload).expect("decode runner output");
    assert_eq!(decoded.effect_exchanges.len(), 1);
    assert_eq!(decoded.semantic_objects.outstanding_effects.len(), 1);
    assert_eq!(decoded.semantic_objects.publication_events.len(), 1);
    assert!(decoded
        .semantic_objects
        .transformation_obligations
        .is_empty());
    assert_eq!(
        decoded.semantic_objects.operation_instances[0]
            .terminal_publication
            .as_deref(),
        Some("effect.blocked")
    );
}

#[test]
fn semantic_objects_roundtrip_preserves_handoff_obligations() {
    let payload = json!({
        "schema_version": SEMANTIC_OBJECTS_SCHEMA_VERSION,
        "operation_instances": [],
        "outstanding_effects": [],
        "semantic_handoffs": [{
            "handoff_id": 4,
            "session": 2,
            "from_coro": 0,
            "to_coro": 1,
            "revoked_owner_id": "coro:0",
            "activated_owner_id": "coro:1",
            "scope": { "Fragments": ["A"] },
            "status": "Committed",
            "tick": 9,
            "reason": null
        }],
        "transformation_obligations": [{
            "obligation_id": "handoff:4",
            "handoff_id": 4,
            "session": 2,
            "transformed_fragments": ["A"],
            "affected_operation_ids": ["effect:10"],
            "affected_effect_ids": [10],
            "transported_effect_ids": [10],
            "invalidated_effect_ids": [11],
            "witness_policy": "transport_pending_invalidate_blocked",
            "publication_revoked_from": "coro:0",
            "publication_activated_to": "coro:1",
            "scope": { "Fragments": ["A"] },
            "status": "Committed",
            "tick": 9,
            "reason": null
        }],
        "authoritative_reads": [],
        "observed_reads": [],
        "materialization_proofs": [],
        "canonical_handles": [],
        "publication_events": [{
            "publication_id": "handoff:4:handoff.committed",
            "session": 2,
            "operation_id": "handoff:4",
            "owner_id": null,
            "publication": "handoff.committed",
            "observer_class": "audit",
            "status": "published",
            "proof_ref": "handoff:4",
            "handle_ref": "handoff:4",
            "reason": null
        }],
        "progress_contracts": []
    });

    let decoded: ProtocolMachineSemanticObjects =
        serde_json::from_value(payload).expect("decode semantic objects");
    assert_eq!(decoded.semantic_handoffs[0].revoked_owner_id, "coro:0");
    assert_eq!(
        decoded.transformation_obligations[0].invalidated_effect_ids,
        vec![11]
    );
    assert_eq!(
        decoded.publication_events[0].publication.as_str(),
        "handoff.committed"
    );
}

#[test]
fn semantic_objects_decode_requires_canonical_shape() {
    let legacy = json!({
        "schema_version": "protocol_machine.semantic_objects.v1",
        "clock": 1
    });

    let decoded = serde_json::from_value::<ProtocolMachineSemanticObjects>(legacy);
    assert!(
        decoded.is_err(),
        "legacy VM-state payloads must no longer decode"
    );
}
