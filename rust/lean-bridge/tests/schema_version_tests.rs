use serde_json::json;
use std::collections::BTreeMap;
use telltale_lean_bridge::{
    ensure_supported_schema_version, export_protocol_bundle, ChoreographyJson, InvariantClaims,
    ProtocolBundle, ReplayTraceBundle, VMState, VmRunInput, VmRunOutput,
    LEAN_BRIDGE_SCHEMA_VERSION, PROTOCOL_BUNDLE_SCHEMA_VERSION, VM_STATE_SCHEMA_VERSION,
};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[test]
fn vm_run_output_legacy_decode_defaults_schema_version() {
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

    let out: VmRunOutput = serde_json::from_value(legacy).expect("decode legacy VmRunOutput");
    assert_eq!(out.schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
    assert_eq!(out.trace[0].schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
    assert_eq!(out.sessions[0].schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
}

#[test]
fn vm_run_input_roundtrip_preserves_schema_version() {
    let input = VmRunInput {
        schema_version: LEAN_BRIDGE_SCHEMA_VERSION.to_string(),
        choreographies: vec![ChoreographyJson {
            schema_version: LEAN_BRIDGE_SCHEMA_VERSION.to_string(),
            global_type: json!({"kind":"end"}),
            roles: vec!["A".to_string()],
        }],
        concurrency: 1,
        max_steps: 5,
    };

    let encoded = serde_json::to_value(&input).expect("serialize VmRunInput");
    assert_eq!(encoded["schema_version"], LEAN_BRIDGE_SCHEMA_VERSION);

    let decoded: VmRunInput = serde_json::from_value(encoded).expect("deserialize VmRunInput");
    assert_eq!(decoded.schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
    assert_eq!(
        decoded.choreographies[0].schema_version,
        LEAN_BRIDGE_SCHEMA_VERSION
    );
}

#[test]
fn replay_trace_bundle_legacy_decode_defaults_schema_version() {
    let legacy = json!({
        "vm_trace": [{
            "kind": "sent",
            "session_index": 0,
            "sender": "A",
            "receiver": "B",
            "label": "msg"
        }],
        "effect_trace": [],
        "output_condition_trace": []
    });

    let bundle: ReplayTraceBundle =
        serde_json::from_value(legacy).expect("decode legacy ReplayTraceBundle");
    assert_eq!(bundle.schema_version, LEAN_BRIDGE_SCHEMA_VERSION);
}

#[test]
fn schema_validator_accepts_current_and_rejects_unknown() {
    assert!(ensure_supported_schema_version(LEAN_BRIDGE_SCHEMA_VERSION, "VmRunInput").is_ok());
    assert!(ensure_supported_schema_version("legacy.v0", "VmRunInput").is_err());
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
fn protocol_bundle_legacy_decode_defaults_schema_version() {
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
    let decoded: ProtocolBundle =
        serde_json::from_value(legacy).expect("decode legacy ProtocolBundle");
    assert_eq!(decoded.schema_version, PROTOCOL_BUNDLE_SCHEMA_VERSION);
}

#[test]
fn vm_state_roundtrip_preserves_vm_state_schema_version() {
    let state = json!({
        "schema_version": VM_STATE_SCHEMA_VERSION,
        "compatibility": {
            "family": "vm_state",
            "version": VM_STATE_SCHEMA_VERSION,
            "backward_compatible_from": ["vm_state.v0"]
        },
        "clock": 3,
        "nextCoroId": 2,
        "nextSessionId": 1,
        "coroutines": [{
            "id": 0,
            "programId": 11,
            "pc": 7,
            "status": {"kind": "ready"},
            "ownedEndpoints": [{"sid": 0, "role": "A"}],
            "costBudget": 100,
            "effectCtx": null
        }],
        "sessions": [{
            "sid": 0,
            "roles": ["A", "B"],
            "status": "active",
            "epoch": 0
        }],
        "obsTrace": [{
            "tick": 0,
            "event": {"kind": "sent"}
        }]
    });

    let decoded: VMState<serde_json::Value, serde_json::Value> =
        serde_json::from_value(state.clone()).expect("decode vm_state.v1");
    assert_eq!(decoded.schema_version, VM_STATE_SCHEMA_VERSION);

    let encoded = serde_json::to_value(decoded).expect("encode vm_state.v1");
    assert_eq!(encoded["schema_version"], VM_STATE_SCHEMA_VERSION);
}

#[test]
fn vm_state_legacy_decode_accepts_v0_shape_aliases() {
    let legacy = json!({
        "schema_version": "vm_state.v0",
        "clock": 1,
        "next_coro_id": 4,
        "next_session_id": 5,
        "coroutines": [{
            "id": 1,
            "program_id": 9,
            "pc": 0,
            "status": {"kind": "blocked"},
            "owned_endpoints": [{"sid": 0, "role": "A"}],
            "cost_budget": 50,
            "effect_ctx": null
        }],
        "sessions": [{
            "sid": 0,
            "roles": ["A"],
            "status": "active",
            "epoch": 0
        }],
        "obs_trace": [{
            "tick": 0,
            "event": {"kind": "opened"}
        }]
    });

    let decoded: VMState<serde_json::Value, serde_json::Value> =
        serde_json::from_value(legacy).expect("decode vm_state.v0 aliases");
    assert_eq!(decoded.schema_version, "vm_state.v0");
    assert_eq!(decoded.next_coro_id, 4);
    assert_eq!(decoded.next_session_id, 5);
    assert_eq!(decoded.coroutines[0].program_id, 9);
}
