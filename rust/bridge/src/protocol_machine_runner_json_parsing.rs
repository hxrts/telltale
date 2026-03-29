use super::*;
use crate::bridge_normalization::{SchemaVersionBackfillPath, SCHEMA_VERSION_BACKFILL_PATHS};
use std::collections::BTreeSet;

const RUN_OUTPUT_ALLOWED_KEYS: &[&str] = &[
    "schema_version",
    "trace",
    "sessions",
    "steps_executed",
    "concurrency",
    "status",
    "effect_trace",
    "effect_exchanges",
    "output_condition_trace",
    "step_states",
    "semantic_objects",
];

fn inject_field_if_missing(object: &mut serde_json::Map<String, Value>, key: &str, value: Value) {
    object.entry(key.to_string()).or_insert(value);
}

/// Schema-compatibility backfill for runner JSON payloads.
///
/// This is intentionally not semantic normalization. It exists only so older
/// Lean runner payloads that omitted nested `schema_version` fields can still be
/// deserialized into the current bridge types. No non-schema fields are
/// synthesized here.
fn backfill_protocol_machine_run_output_schema_versions(mut value: Value) -> Value {
    let bridge_schema = Value::String(crate::schema::canonical_schema_version());
    let semantic_objects_schema =
        Value::String(crate::semantic_objects::canonical_semantic_objects_schema_version());

    let Some(root) = value.as_object_mut() else {
        return value;
    };

    for path in SCHEMA_VERSION_BACKFILL_PATHS {
        match path {
            SchemaVersionBackfillPath::Root => {
                inject_field_if_missing(root, "schema_version", bridge_schema.clone());
            }
            SchemaVersionBackfillPath::TraceEvent => {
                if let Some(Value::Array(trace)) = root.get_mut("trace") {
                    for event in trace.iter_mut() {
                        if let Some(obj) = event.as_object_mut() {
                            inject_field_if_missing(obj, "schema_version", bridge_schema.clone());
                        }
                    }
                }
            }
            SchemaVersionBackfillPath::SessionStatus => {
                if let Some(Value::Array(sessions)) = root.get_mut("sessions") {
                    for session in sessions.iter_mut() {
                        if let Some(obj) = session.as_object_mut() {
                            inject_field_if_missing(obj, "schema_version", bridge_schema.clone());
                        }
                    }
                }
            }
            SchemaVersionBackfillPath::StepEvent => {
                if let Some(Value::Array(step_states)) = root.get_mut("step_states") {
                    for step in step_states.iter_mut() {
                        if let Some(step_obj) = step.as_object_mut() {
                            if let Some(event) = step_obj.get_mut("event") {
                                if let Some(event_obj) = event.as_object_mut() {
                                    inject_field_if_missing(
                                        event_obj,
                                        "schema_version",
                                        bridge_schema.clone(),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            SchemaVersionBackfillPath::SemanticObjects => {
                if let Some(semantic_objects) = root.get_mut("semantic_objects") {
                    if let Some(obj) = semantic_objects.as_object_mut() {
                        inject_field_if_missing(
                            obj,
                            "schema_version",
                            semantic_objects_schema.clone(),
                        );
                    }
                }
            }
        }
    }

    value
}

pub(super) fn parse_protocol_machine_run_output(
    value: Value,
) -> Result<ProtocolMachineRunOutput, ProtocolMachineRunnerError> {
    reject_unknown_protocol_machine_run_output_fields(&value)?;
    let normalized = backfill_protocol_machine_run_output_schema_versions(value);
    let output: ProtocolMachineRunOutput = serde_json::from_value(normalized)
        .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
    crate::schema::ensure_supported_schema_version(
        &output.schema_version,
        "ProtocolMachineRunOutput",
    )
    .map_err(ProtocolMachineRunnerError::ParseError)?;
    Ok(output)
}

fn reject_unknown_protocol_machine_run_output_fields(
    value: &Value,
) -> Result<(), ProtocolMachineRunnerError> {
    let Some(root) = value.as_object() else {
        return Ok(());
    };

    let allowed: BTreeSet<&str> = RUN_OUTPUT_ALLOWED_KEYS.iter().copied().collect();
    if let Some(unknown) = root.keys().find(|key| !allowed.contains(key.as_str())) {
        return Err(ProtocolMachineRunnerError::ParseError(format!(
            "unknown field `{unknown}` in ProtocolMachineRunOutput"
        )));
    }

    Ok(())
}

pub(super) fn parse_sim_run_output(
    value: Value,
) -> Result<SimRunOutput, ProtocolMachineRunnerError> {
    let output: SimRunOutput = serde_json::from_value(value)
        .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
    crate::schema::ensure_supported_schema_version(&output.schema_version, "SimRunOutput")
        .map_err(ProtocolMachineRunnerError::ParseError)?;
    Ok(output)
}

pub(super) fn parse_required_valid(
    response: &Value,
    operation: &str,
) -> Result<bool, ProtocolMachineRunnerError> {
    response
        .get("valid")
        .and_then(Value::as_bool)
        .ok_or_else(|| {
            ProtocolMachineRunnerError::ParseError(format!(
                "missing boolean field 'valid' in {operation} response"
            ))
        })
}

pub(super) fn parse_sim_trace_validation(
    response: &Value,
) -> Result<SimTraceValidation, ProtocolMachineRunnerError> {
    Ok(SimTraceValidation {
        valid: parse_required_valid(response, "validateSimulationTrace")?,
        errors: parse_simulation_errors(response),
        artifacts: response.get("artifacts").cloned().unwrap_or(Value::Null),
    })
}

pub(super) fn simulation_trace_payload(
    input: &SimRunInput,
    trace: &[ProtocolMachineTraceEvent],
) -> Value {
    serde_json::json!({
        "input": input,
        "trace": trace,
    })
}

pub(super) fn parse_simulation_errors(response: &Value) -> Vec<SimulationStructuredError> {
    let Some(errors) = response.get("errors") else {
        return Vec::new();
    };
    match errors {
        Value::Array(items) => items
            .iter()
            .map(|item| {
                if let Some(obj) = item.as_object() {
                    SimulationStructuredError {
                        code: obj
                            .get("code")
                            .and_then(Value::as_str)
                            .unwrap_or("simulation.error")
                            .to_string(),
                        path: obj
                            .get("path")
                            .and_then(Value::as_str)
                            .map(ToString::to_string),
                        message: obj
                            .get("message")
                            .and_then(Value::as_str)
                            .unwrap_or("unspecified simulation error")
                            .to_string(),
                    }
                } else {
                    SimulationStructuredError {
                        code: "simulation.error".to_string(),
                        path: None,
                        message: item.to_string(),
                    }
                }
            })
            .collect(),
        Value::String(msg) => vec![SimulationStructuredError {
            code: "simulation.error".to_string(),
            path: None,
            message: msg.clone(),
        }],
        other => vec![SimulationStructuredError {
            code: "simulation.error".to_string(),
            path: None,
            message: other.to_string(),
        }],
    }
}

pub(super) fn parse_structured_errors(response: &Value) -> Vec<LeanStructuredError> {
    let Some(errors) = response.get("errors") else {
        return Vec::new();
    };

    match errors {
        Value::Array(items) => items
            .iter()
            .map(|item| {
                if let Some(obj) = item.as_object() {
                    LeanStructuredError {
                        code: obj
                            .get("code")
                            .and_then(Value::as_str)
                            .unwrap_or("lean.error")
                            .to_string(),
                        path: obj
                            .get("path")
                            .and_then(Value::as_str)
                            .map(ToString::to_string),
                        message: obj
                            .get("message")
                            .and_then(Value::as_str)
                            .unwrap_or("unspecified Lean validation error")
                            .to_string(),
                    }
                } else {
                    LeanStructuredError {
                        code: "lean.error".to_string(),
                        path: None,
                        message: item.to_string(),
                    }
                }
            })
            .collect(),
        Value::String(msg) => vec![LeanStructuredError {
            code: "lean.error".to_string(),
            path: None,
            message: msg.clone(),
        }],
        other => vec![LeanStructuredError {
            code: "lean.error".to_string(),
            path: None,
            message: other.to_string(),
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn minimal_run_output_json() -> Value {
        let mut semantic_objects = serde_json::to_value(ProtocolMachineSemanticObjects::default())
            .expect("serialize default semantic objects");
        semantic_objects
            .as_object_mut()
            .expect("semantic objects object")
            .remove("schema_version");
        let refinement_slice = json!({
            "coroutines": [
                {
                    "coro_id": 0,
                    "session_id": 0,
                    "pc": 0,
                    "status": "ready",
                    "owned_endpoints": 1,
                    "progress_tokens": 0
                }
            ],
            "sessions": [
                {
                    "sid": 0,
                    "role_count": 2,
                    "local_type_entries": 1,
                    "buffer_edges": 0,
                    "buffered_messages": 0,
                    "status": "active",
                    "epoch": 0
                }
            ],
            "scheduler": {
                "ready_queue": [0],
                "blocked": {},
                "step_count": 1
            }
        });

        json!({
            "trace": [
                {
                    "kind": "opened",
                    "tick": 0,
                    "session": 0,
                    "role": "A,B"
                }
            ],
            "sessions": [
                {
                    "sid": 0,
                    "terminal": false
                }
            ],
            "steps_executed": 1,
            "concurrency": 1,
            "status": "ok",
            "step_states": [
                {
                    "step_index": 0,
                    "pre_state": refinement_slice.clone(),
                    "post_state": refinement_slice,
                    "selected_coro": 0,
                    "selected_pc": 0,
                    "exec_status": "continue",
                    "session_type_counts": {"0": 1},
                    "event": {
                        "kind": "opened",
                        "tick": 0,
                        "session": 0,
                        "role": "A,B"
                    }
                }
            ],
            "semantic_objects": semantic_objects
        })
    }

    #[test]
    fn schema_backfill_injects_only_schema_version_fields() {
        let input = minimal_run_output_json();
        let backfilled = backfill_protocol_machine_run_output_schema_versions(input.clone());

        assert_eq!(
            backfilled["schema_version"],
            Value::String(crate::schema::canonical_schema_version())
        );
        assert_eq!(
            backfilled["trace"][0]["schema_version"],
            Value::String(crate::schema::canonical_schema_version())
        );
        assert_eq!(
            backfilled["sessions"][0]["schema_version"],
            Value::String(crate::schema::canonical_schema_version())
        );
        assert_eq!(
            backfilled["step_states"][0]["event"]["schema_version"],
            Value::String(crate::schema::canonical_schema_version())
        );
        assert_eq!(
            backfilled["semantic_objects"]["schema_version"],
            Value::String(crate::semantic_objects::canonical_semantic_objects_schema_version())
        );

        assert_eq!(backfilled["trace"][0]["kind"], input["trace"][0]["kind"]);
        assert!(backfilled["sessions"][0].get("terminal").is_some());
    }

    #[test]
    fn schema_backfill_paths_are_canonical_and_narrow() {
        assert_eq!(
            SCHEMA_VERSION_BACKFILL_PATHS,
            &[
                SchemaVersionBackfillPath::Root,
                SchemaVersionBackfillPath::TraceEvent,
                SchemaVersionBackfillPath::SessionStatus,
                SchemaVersionBackfillPath::StepEvent,
                SchemaVersionBackfillPath::SemanticObjects,
            ]
        );
    }

    #[test]
    fn parse_protocol_machine_run_output_accepts_schema_backfilled_payloads() {
        let parsed = parse_protocol_machine_run_output(minimal_run_output_json())
            .expect("schema backfill should make legacy payload parseable");
        assert_eq!(parsed.trace.len(), 1);
        assert_eq!(parsed.sessions.len(), 1);
        assert_eq!(parsed.step_states.len(), 1);
        assert!(parsed.step_states[0].pre_state.is_some());
        assert!(parsed.step_states[0].post_state.is_some());
        assert_eq!(
            parsed.semantic_objects.schema_version,
            crate::semantic_objects::canonical_semantic_objects_schema_version()
        );
    }

    #[test]
    fn parse_protocol_machine_run_output_rejects_missing_required_non_schema_fields() {
        let mut payload = minimal_run_output_json();
        payload
            .as_object_mut()
            .expect("root object")
            .remove("trace");

        let err =
            parse_protocol_machine_run_output(payload).expect_err("missing trace must not parse");
        assert!(matches!(err, ProtocolMachineRunnerError::ParseError(_)));
    }

    #[test]
    fn parse_protocol_machine_run_output_rejects_unsupported_schema_versions() {
        let mut payload = minimal_run_output_json();
        payload["schema_version"] = Value::String("0.0.0".to_string());

        let err = parse_protocol_machine_run_output(payload)
            .expect_err("unsupported schema version must fail closed");
        assert!(matches!(err, ProtocolMachineRunnerError::ParseError(_)));
    }

    #[test]
    fn parse_protocol_machine_run_output_rejects_unknown_top_level_fields() {
        let mut payload = minimal_run_output_json();
        payload
            .as_object_mut()
            .expect("root object")
            .insert("phase16_mutation".to_string(), json!(true));

        let err = parse_protocol_machine_run_output(payload)
            .expect_err("unknown top-level fields must fail closed");
        assert!(
            err.to_string()
                .contains("unknown field `phase16_mutation` in ProtocolMachineRunOutput"),
            "unexpected error: {err}"
        );
    }
}
