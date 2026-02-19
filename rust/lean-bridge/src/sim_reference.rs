//! Lean reference simulator bridge payloads.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;

use crate::vm_runner::VmTraceEvent;

/// Input payload for Lean reference simulation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimRunInput {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Scenario configuration payload.
    pub scenario: Value,
    /// Global type payload.
    pub global_type: Value,
    /// Local type payloads keyed by role.
    pub local_types: BTreeMap<String, Value>,
    /// Initial role state payloads keyed by role.
    #[serde(default)]
    pub initial_states: BTreeMap<String, Vec<Value>>,
}

/// Output payload from Lean reference simulation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimRunOutput {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Observable trace produced by the simulation.
    #[serde(default)]
    pub trace: Vec<VmTraceEvent>,
    /// Property violations emitted by Lean reference checks.
    #[serde(default)]
    pub violations: Vec<Value>,
    /// Optional operation-specific artifacts.
    #[serde(default)]
    pub artifacts: Value,
}

/// Structured simulation validation error.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SimulationStructuredError {
    /// Stable Lean-side error code.
    pub code: String,
    /// Optional path to the failing payload segment.
    #[serde(default)]
    pub path: Option<String>,
    /// Human-readable diagnostic message.
    pub message: String,
}

/// Result payload from `validateSimulationTrace` operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimTraceValidation {
    /// Whether validation succeeded.
    pub valid: bool,
    /// Structured errors when validation fails.
    #[serde(default)]
    pub errors: Vec<SimulationStructuredError>,
    /// Optional validation artifacts from Lean.
    #[serde(default)]
    pub artifacts: Value,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sim_input_legacy_decode_defaults_schema_version() {
        let legacy = serde_json::json!({
            "scenario": {"name": "s"},
            "global_type": {"kind": "end"},
            "local_types": {},
            "initial_states": {}
        });

        let input: SimRunInput = serde_json::from_value(legacy).expect("decode SimRunInput");
        assert_eq!(
            input.schema_version,
            crate::schema::LEAN_BRIDGE_SCHEMA_VERSION
        );
    }

    #[test]
    fn sim_output_legacy_decode_defaults_schema_version() {
        let legacy = serde_json::json!({
            "trace": [],
            "violations": []
        });

        let output: SimRunOutput = serde_json::from_value(legacy).expect("decode SimRunOutput");
        assert_eq!(
            output.schema_version,
            crate::schema::LEAN_BRIDGE_SCHEMA_VERSION
        );
    }

    #[test]
    fn sim_trace_validation_roundtrip() {
        let validation = SimTraceValidation {
            valid: false,
            errors: vec![SimulationStructuredError {
                code: "sim.trace.mismatch".to_string(),
                path: Some("trace[0]".to_string()),
                message: "event mismatch".to_string(),
            }],
            artifacts: serde_json::json!({"kind": "diff"}),
        };

        let encoded = serde_json::to_value(&validation).expect("encode");
        let decoded: SimTraceValidation = serde_json::from_value(encoded).expect("decode");
        assert!(!decoded.valid);
        assert_eq!(decoded.errors.len(), 1);
        assert_eq!(decoded.errors[0].code, "sim.trace.mismatch");
    }
}
