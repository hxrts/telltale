use super::*;

pub(super) fn parse_sim_run_output(value: Value) -> Result<SimRunOutput, VmRunnerError> {
    let output: SimRunOutput =
        serde_json::from_value(value).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
    crate::schema::ensure_supported_schema_version(&output.schema_version, "SimRunOutput")
        .map_err(VmRunnerError::ParseError)?;
    Ok(output)
}

pub(super) fn parse_sim_trace_validation(response: &Value) -> SimTraceValidation {
    let valid = response
        .get("valid")
        .and_then(Value::as_bool)
        .unwrap_or_else(|| response.get("errors").is_none());
    SimTraceValidation {
        valid,
        errors: parse_simulation_errors(response),
        artifacts: response.get("artifacts").cloned().unwrap_or(Value::Null),
    }
}

pub(super) fn simulation_trace_payload(trace: &[VmTraceEvent]) -> Value {
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
