//! Lean VM runner wrapper.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use thiserror::Error;

use crate::runner::ChoreographyJson;
use crate::vm_export::TickedObsEvent;
use crate::vm_trace::{
    normalize_vm_trace, traces_equivalent, EffectTraceEvent, OutputConditionTraceEvent,
};

/// Errors from Lean VM runner operations.
#[derive(Debug, Error)]
pub enum VmRunnerError {
    /// The VM runner binary was not found at the expected path.
    #[error("VM runner binary not found at {0}")]
    BinaryNotFound(PathBuf),
    /// Failed to create a temporary file for JSON exchange.
    #[error("Failed to create temp file: {0}")]
    TempFileError(#[from] std::io::Error),
    /// The Lean process exited with a non-zero status.
    #[error("VM runner failed with exit code {code}: {stderr}")]
    ProcessFailed {
        /// Exit code from the process.
        code: i32,
        /// Standard error output.
        stderr: String,
    },
    /// Failed to parse Lean output or JSON.
    #[error("Failed to parse VM runner output: {0}")]
    ParseError(String),
}

/// Input JSON for the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmRunInput {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Choreographies to load.
    pub choreographies: Vec<ChoreographyJson>,
    /// Concurrency level.
    pub concurrency: u64,
    /// Maximum scheduler rounds.
    pub max_steps: u64,
}

/// One session status entry from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmSessionStatus {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Session id.
    pub sid: u64,
    /// Terminal flag.
    pub terminal: bool,
}

/// One trace event from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct VmTraceEvent {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    pub kind: String,
    pub tick: u64,
    #[serde(default)]
    pub session: Option<u64>,
    #[serde(default)]
    pub sender: Option<String>,
    #[serde(default)]
    pub receiver: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    #[serde(default)]
    pub role: Option<String>,
    #[serde(default)]
    pub target: Option<String>,
    #[serde(default)]
    pub permitted: Option<bool>,
    #[serde(default)]
    pub epoch: Option<u64>,
    #[serde(default)]
    pub ghost: Option<u64>,
    #[serde(default)]
    pub from: Option<u64>,
    #[serde(default)]
    pub to: Option<u64>,
    #[serde(default)]
    pub predicate_ref: Option<String>,
    #[serde(default)]
    pub witness_ref: Option<String>,
    #[serde(default)]
    pub output_digest: Option<String>,
    #[serde(default)]
    pub passed: Option<bool>,
}

/// One scheduler-step state entry from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmStepState {
    /// Step index in execution order.
    #[serde(default)]
    pub step_index: u64,
    /// Coroutine selected for this step, when available.
    #[serde(default)]
    pub selected_coro: Option<u64>,
    /// Execution status tag for the selected step.
    #[serde(default)]
    pub exec_status: Option<String>,
    /// Per-session local-type counts after this step.
    #[serde(default)]
    pub session_type_counts: BTreeMap<u64, u64>,
    /// Optional event emitted by this scheduler step.
    #[serde(default)]
    pub event: Option<VmTraceEvent>,
}

/// Output from the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VmRunOutput {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Observable trace.
    pub trace: Vec<VmTraceEvent>,
    /// Session statuses.
    pub sessions: Vec<VmSessionStatus>,
    /// Steps executed.
    pub steps_executed: u64,
    /// Concurrency level.
    pub concurrency: u64,
    /// Status string.
    pub status: String,
    /// Optional effect trace for replay/determinism checks.
    #[serde(default)]
    pub effect_trace: Vec<EffectTraceEvent>,
    /// Optional output-condition verification records.
    #[serde(default)]
    pub output_condition_trace: Vec<OutputConditionTraceEvent>,
    /// Optional per-step scheduler state snapshots.
    #[serde(default)]
    pub step_states: Vec<VmStepState>,
}

/// Structured Lean-side validation error payload.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LeanStructuredError {
    pub code: String,
    #[serde(default)]
    pub path: Option<String>,
    pub message: String,
}

/// Result from Lean trace-validation entrypoint.
#[derive(Debug, Clone, Serialize)]
pub struct TraceValidation {
    pub valid: bool,
    #[serde(default)]
    pub errors: Vec<LeanStructuredError>,
}

/// Result of comparing Rust and Lean VM executions.
#[derive(Debug, Clone, Serialize)]
pub struct ComparisonResult {
    pub equivalent: bool,
    pub trace_equivalent: bool,
    pub rust_normalized: Vec<TickedObsEvent<VmTraceEvent>>,
    pub lean_normalized: Vec<TickedObsEvent<VmTraceEvent>>,
    #[serde(default)]
    pub diff: Option<Value>,
    pub lean_output: VmRunOutput,
}

/// Result from protocol-bundle invariant verification.
#[derive(Debug, Clone, Serialize)]
pub struct InvariantVerificationResult {
    pub valid: bool,
    #[serde(default)]
    pub errors: Vec<LeanStructuredError>,
    #[serde(default)]
    pub artifacts: Value,
}

/// Runner for invoking the Lean VM runner binary.
pub struct VmRunner {
    binary_path: PathBuf,
}

impl VmRunner {
    /// Default path to the VM runner binary (relative to workspace root).
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/vm_runner";

    fn find_workspace_root() -> Option<PathBuf> {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let mut path = PathBuf::from(manifest_dir);
        for _ in 0..5 {
            if path.join("lean/.lake").is_dir() {
                return Some(path);
            }
            if !path.pop() {
                break;
            }
        }
        None
    }

    fn get_binary_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::DEFAULT_BINARY_PATH))
            .filter(|p| p.exists())
    }

    /// Create a new VM runner with the default binary path.
    ///
    /// # Errors
    ///
    /// Returns [`VmRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn new() -> Result<Self, VmRunnerError> {
        match Self::get_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(VmRunnerError::BinaryNotFound(PathBuf::from(
                Self::DEFAULT_BINARY_PATH,
            ))),
        }
    }

    /// Create a VM runner with a custom binary path.
    ///
    /// # Errors
    ///
    /// Returns [`VmRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn with_binary_path(path: impl AsRef<Path>) -> Result<Self, VmRunnerError> {
        let binary_path = PathBuf::from(path.as_ref());
        if !binary_path.exists() {
            return Err(VmRunnerError::BinaryNotFound(binary_path));
        }
        Ok(Self { binary_path })
    }

    /// Try to create a runner, returning None if the binary is unavailable.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        Self::new().ok()
    }

    /// Run the VM runner and return the parsed output.
    ///
    /// # Errors
    ///
    /// Returns a [`VmRunnerError`] if the process fails or output is invalid.
    pub fn run(&self, input: &VmRunInput) -> Result<VmRunOutput, VmRunnerError> {
        crate::schema::ensure_supported_schema_version(&input.schema_version, "VmRunInput")
            .map_err(VmRunnerError::ParseError)?;

        let payload =
            serde_json::to_vec(input).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;

        let mut cmd = Command::new(&self.binary_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(VmRunnerError::TempFileError)?;

        if let Some(stdin) = cmd.stdin.as_mut() {
            stdin.write_all(&payload)?;
        }

        let output = cmd
            .wait_with_output()
            .map_err(VmRunnerError::TempFileError)?;

        if !output.status.success() {
            return Err(VmRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }

        let out: VmRunOutput = serde_json::from_slice(&output.stdout)
            .map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
        crate::schema::ensure_supported_schema_version(&out.schema_version, "VmRunOutput")
            .map_err(VmRunnerError::ParseError)?;
        Ok(out)
    }

    /// Run the Lean VM execution entrypoint.
    ///
    /// # Errors
    ///
    /// Returns an error if the process fails or output is invalid.
    pub fn run_lean_vm(&self, input: &VmRunInput) -> Result<VmRunOutput, VmRunnerError> {
        self.run(input)
    }

    /// Run a generic Lean VM validation operation.
    ///
    /// # Errors
    ///
    /// Returns an error if the process fails or output is invalid.
    pub fn run_lean_validation(
        &self,
        operation: &str,
        payload: &Value,
    ) -> Result<Value, VmRunnerError> {
        let input = serde_json::json!({
            "schema_version": crate::schema::default_schema_version(),
            "operation": operation,
            "payload": payload,
        });
        let bytes =
            serde_json::to_vec(&input).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;

        let mut cmd = Command::new(&self.binary_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(VmRunnerError::TempFileError)?;

        if let Some(stdin) = cmd.stdin.as_mut() {
            stdin.write_all(&bytes)?;
        }

        let output = cmd
            .wait_with_output()
            .map_err(VmRunnerError::TempFileError)?;
        if !output.status.success() {
            return Err(VmRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
        serde_json::from_slice(&output.stdout).map_err(|e| VmRunnerError::ParseError(e.to_string()))
    }

    /// Validate a trace against Lean-side VM specification checks.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn validate_trace(
        &self,
        rust_trace: &[VmTraceEvent],
    ) -> Result<TraceValidation, VmRunnerError> {
        let payload = serde_json::json!({
            "trace": rust_trace,
        });
        let response = self.run_lean_validation("validateTrace", &payload)?;
        let valid = response
            .get("valid")
            .and_then(Value::as_bool)
            .unwrap_or_else(|| response.get("errors").is_none());
        Ok(TraceValidation {
            valid,
            errors: parse_structured_errors(&response),
        })
    }

    /// Run the same choreography in Lean and compare normalized traces.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn compare_execution(
        &self,
        choreography: &ChoreographyJson,
        rust_output: &VmRunOutput,
    ) -> Result<ComparisonResult, VmRunnerError> {
        let input = VmRunInput {
            schema_version: crate::schema::default_schema_version(),
            choreographies: vec![choreography.clone()],
            concurrency: rust_output.concurrency,
            max_steps: rust_output.steps_executed.max(1),
        };
        let lean_output = self.run_lean_vm(&input)?;

        let rust_ticked: Vec<TickedObsEvent<VmTraceEvent>> = rust_output
            .trace
            .iter()
            .cloned()
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
            .collect();
        let lean_ticked: Vec<TickedObsEvent<VmTraceEvent>> = lean_output
            .trace
            .iter()
            .cloned()
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
            .collect();

        let rust_normalized = normalize_vm_trace(&rust_ticked);
        let lean_normalized = normalize_vm_trace(&lean_ticked);
        let trace_equivalent = traces_equivalent(&rust_ticked, &lean_ticked);
        let diff = compute_trace_diff(&rust_normalized, &lean_normalized);

        Ok(ComparisonResult {
            equivalent: trace_equivalent,
            trace_equivalent,
            rust_normalized,
            lean_normalized,
            diff,
            lean_output,
        })
    }

    /// Verify a typed protocol bundle using Lean-side verification entrypoint.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn verify_invariants(
        &self,
        bundle: &crate::invariants::ProtocolBundle,
    ) -> Result<InvariantVerificationResult, VmRunnerError> {
        let payload =
            serde_json::to_value(bundle).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
        let response = self.run_lean_validation("verifyProtocolBundle", &payload)?;
        let valid = response
            .get("valid")
            .and_then(Value::as_bool)
            .unwrap_or_else(|| response.get("errors").is_none());

        Ok(InvariantVerificationResult {
            valid,
            errors: parse_structured_errors(&response),
            artifacts: response.get("artifacts").cloned().unwrap_or(Value::Null),
        })
    }
}

/// Compute a structured diff for two normalized traces.
#[must_use]
pub fn compute_trace_diff(
    rust_trace: &[TickedObsEvent<VmTraceEvent>],
    lean_trace: &[TickedObsEvent<VmTraceEvent>],
) -> Option<Value> {
    if rust_trace == lean_trace {
        return None;
    }

    let min_len = rust_trace.len().min(lean_trace.len());
    for idx in 0..min_len {
        if rust_trace[idx] != lean_trace[idx] {
            return Some(serde_json::json!({
                "kind": "event_mismatch",
                "index": idx,
                "rust": rust_trace[idx],
                "lean": lean_trace[idx],
                "rust_len": rust_trace.len(),
                "lean_len": lean_trace.len(),
            }));
        }
    }

    Some(serde_json::json!({
        "kind": "length_mismatch",
        "rust_len": rust_trace.len(),
        "lean_len": lean_trace.len(),
    }))
}

fn parse_structured_errors(response: &Value) -> Vec<LeanStructuredError> {
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

/// Helper to build a VM runner input from JSON values.
#[must_use]
pub fn vm_input_from_values(
    choreographies: Vec<Value>,
    concurrency: u64,
    max_steps: u64,
) -> Result<VmRunInput, VmRunnerError> {
    let mut choreos = Vec::new();
    for value in choreographies {
        let choreo: ChoreographyJson =
            serde_json::from_value(value).map_err(|e| VmRunnerError::ParseError(e.to_string()))?;
        choreos.push(choreo);
    }
    Ok(VmRunInput {
        schema_version: crate::schema::default_schema_version(),
        choreographies: choreos,
        concurrency,
        max_steps,
    })
}

/// Serialize a VM runner output to JSON for debugging.
#[must_use]
pub fn output_to_json(output: &VmRunOutput) -> Value {
    serde_json::to_value(output).unwrap_or(Value::Null)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn trace_event(kind: &str, tick: u64, session: Option<u64>) -> VmTraceEvent {
        VmTraceEvent {
            schema_version: crate::schema::default_schema_version(),
            kind: kind.to_string(),
            tick,
            session,
            sender: None,
            receiver: None,
            label: None,
            role: None,
            target: None,
            permitted: None,
            epoch: None,
            ghost: None,
            from: None,
            to: None,
            predicate_ref: None,
            witness_ref: None,
            output_digest: None,
            passed: None,
        }
    }

    #[test]
    fn compute_trace_diff_none_for_equal_traces() {
        let trace = vec![TickedObsEvent {
            tick: 0,
            event: trace_event("sent", 1, Some(0)),
        }];
        assert!(compute_trace_diff(&trace, &trace).is_none());
    }

    #[test]
    fn compute_trace_diff_reports_event_mismatch() {
        let rust_trace = vec![TickedObsEvent {
            tick: 0,
            event: trace_event("sent", 1, Some(0)),
        }];
        let lean_trace = vec![TickedObsEvent {
            tick: 0,
            event: trace_event("received", 1, Some(0)),
        }];
        let diff = compute_trace_diff(&rust_trace, &lean_trace).expect("expected diff");
        assert_eq!(diff["kind"], "event_mismatch");
        assert_eq!(diff["index"], 0);
    }

    #[test]
    fn parse_structured_errors_reads_codes_and_paths() {
        let response = serde_json::json!({
            "errors": [
                { "code": "trace.mismatch", "path": "trace[0]", "message": "mismatch" }
            ]
        });
        let errors = parse_structured_errors(&response);
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, "trace.mismatch");
        assert_eq!(errors[0].path.as_deref(), Some("trace[0]"));
    }
}
