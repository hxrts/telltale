use super::*;

fn inject_field_if_missing(object: &mut serde_json::Map<String, Value>, key: &str, value: Value) {
    object.entry(key.to_string()).or_insert(value);
}

fn normalize_protocol_machine_run_output_value(mut value: Value) -> Value {
    let bridge_schema = Value::String(crate::schema::canonical_schema_version());
    let semantic_objects_schema =
        Value::String(crate::semantic_objects::canonical_semantic_objects_schema_version());

    let Some(root) = value.as_object_mut() else {
        return value;
    };

    inject_field_if_missing(root, "schema_version", bridge_schema.clone());

    if let Some(Value::Array(trace)) = root.get_mut("trace") {
        for event in trace.iter_mut() {
            if let Some(obj) = event.as_object_mut() {
                inject_field_if_missing(obj, "schema_version", bridge_schema.clone());
            }
        }
    }

    if let Some(Value::Array(sessions)) = root.get_mut("sessions") {
        for session in sessions.iter_mut() {
            if let Some(obj) = session.as_object_mut() {
                inject_field_if_missing(obj, "schema_version", bridge_schema.clone());
            }
        }
    }

    if let Some(Value::Array(step_states)) = root.get_mut("step_states") {
        for step in step_states.iter_mut() {
            if let Some(step_obj) = step.as_object_mut() {
                if let Some(event) = step_obj.get_mut("event") {
                    if let Some(event_obj) = event.as_object_mut() {
                        inject_field_if_missing(event_obj, "schema_version", bridge_schema.clone());
                    }
                }
            }
        }
    }

    if let Some(semantic_objects) = root.get_mut("semantic_objects") {
        if let Some(obj) = semantic_objects.as_object_mut() {
            inject_field_if_missing(obj, "schema_version", semantic_objects_schema);
        }
    }

    value
}

pub(super) fn parse_protocol_machine_run_output(
    value: Value,
) -> Result<ProtocolMachineRunOutput, ProtocolMachineRunnerError> {
    let normalized = normalize_protocol_machine_run_output_value(value);
    let output: ProtocolMachineRunOutput = serde_json::from_value(normalized)
        .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
    crate::schema::ensure_supported_schema_version(
        &output.schema_version,
        "ProtocolMachineRunOutput",
    )
    .map_err(ProtocolMachineRunnerError::ParseError)?;
    Ok(output)
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

pub(super) fn simulation_trace_payload(trace: &[ProtocolMachineTraceEvent]) -> Value {
    serde_json::json!({
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
