//! Lean protocol-machine runner wrapper.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant};
use thiserror::Error;

use crate::protocol_machine_trace::{
    normalize_semantic_audit, semantic_audits_equivalent, EffectTraceEvent,
    OutputConditionTraceEvent,
};
use crate::runner::ChoreographyJson;
use crate::semantic_objects::{ProtocolMachineSemanticObjects, TickedObsEvent};
use crate::sim_reference::{
    SimRunInput, SimRunOutput, SimTraceValidation, SimulationStructuredError,
};
use telltale_machine::{EffectExchangeRecord, ReconfigurationEvent, ReconfigurationPolicy};

#[path = "protocol_machine_runner_json_parsing.rs"]
mod parsing;
use parsing::{
    parse_protocol_machine_run_output, parse_required_valid, parse_sim_run_output,
    parse_sim_trace_validation, parse_structured_errors, simulation_trace_payload,
};

/// Errors from Lean protocol-machine runner operations.
#[derive(Debug, Error)]
pub enum ProtocolMachineRunnerError {
    /// The protocol-machine runner binary was not found at the expected path.
    #[error("protocol-machine runner binary not found at {0}")]
    BinaryNotFound(PathBuf),
    /// Failed to create a temporary file for JSON exchange.
    #[error("Failed to create temp file: {0}")]
    TempFileError(#[from] std::io::Error),
    /// The Lean process exited with a non-zero status.
    #[error("protocol-machine runner failed with exit code {code}: {stderr}")]
    ProcessFailed {
        /// Exit code from the process.
        code: i32,
        /// Standard error output.
        stderr: String,
    },
    /// Failed to parse Lean output or JSON.
    #[error("Failed to parse protocol-machine runner output: {0}")]
    ParseError(String),
    /// Protocol-machine runner process exceeded the configured timeout.
    #[error("protocol-machine runner operation '{operation}' timed out after {timeout_ms}ms")]
    TimedOut {
        /// Operation name associated with the process invocation.
        operation: String,
        /// Timeout in milliseconds.
        timeout_ms: u64,
    },
}

/// Input JSON for the protocol-machine runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolMachineRunInput {
    /// Schema version for this payload.
    #[serde(deserialize_with = "crate::schema::deserialize_schema_version")]
    pub schema_version: String,
    /// Choreographies to load.
    pub choreographies: Vec<ChoreographyJson>,
    /// Concurrency level.
    pub concurrency: u64,
    /// Maximum scheduler rounds.
    pub max_steps: u64,
}

/// One session status entry from the protocol-machine runner.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProtocolMachineSessionStatus {
    /// Schema version for this payload.
    #[serde(deserialize_with = "crate::schema::deserialize_schema_version")]
    pub schema_version: String,
    /// Session id.
    pub sid: u64,
    /// Terminal flag.
    pub terminal: bool,
}

/// One semantic-audit event from the protocol-machine runner.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ProtocolMachineTraceEvent {
    /// Schema version for this payload.
    #[serde(deserialize_with = "crate::schema::deserialize_schema_version")]
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
    #[serde(default)]
    pub reason: Option<String>,
}

/// One scheduler-step state entry from the protocol-machine runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolMachineStepState {
    /// Step index in execution order.
    #[serde(default)]
    pub step_index: u64,
    /// Coroutine selected for this step, when available.
    #[serde(default)]
    pub selected_coro: Option<u64>,
    /// Program counter selected for this step, when available.
    #[serde(default)]
    pub selected_pc: Option<u64>,
    /// Lean-side selected endpoint local type snapshot for this step.
    #[serde(default)]
    pub selected_type: Option<Value>,
    /// Execution status tag for the selected step.
    #[serde(default)]
    pub exec_status: Option<String>,
    /// Per-session local-type counts after this step.
    #[serde(default)]
    pub session_type_counts: BTreeMap<u64, u64>,
    /// Optional event emitted by this scheduler step.
    #[serde(default)]
    pub event: Option<ProtocolMachineTraceEvent>,
}

/// Output from the protocol-machine runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolMachineRunOutput {
    /// Schema version for this payload.
    #[serde(deserialize_with = "crate::schema::deserialize_schema_version")]
    pub schema_version: String,
    /// Semantic audit emitted by the protocol machine.
    pub trace: Vec<ProtocolMachineTraceEvent>,
    /// Session statuses.
    pub sessions: Vec<ProtocolMachineSessionStatus>,
    /// Steps executed.
    pub steps_executed: u64,
    /// Concurrency level.
    pub concurrency: u64,
    /// Status string.
    pub status: String,
    /// Optional effect trace for replay/determinism checks.
    #[serde(default)]
    pub effect_trace: Vec<EffectTraceEvent>,
    /// Canonical typed effect request/outcome exchanges.
    #[serde(default)]
    pub effect_exchanges: Vec<EffectExchangeRecord>,
    /// Optional output-condition verification records.
    #[serde(default)]
    pub output_condition_trace: Vec<OutputConditionTraceEvent>,
    /// Optional per-step scheduler state snapshots.
    #[serde(default)]
    pub step_states: Vec<ProtocolMachineStepState>,
    /// Canonical semantic object export from the protocol machine runtime.
    #[serde(default)]
    pub semantic_objects: ProtocolMachineSemanticObjects,
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

/// Result of comparing Rust and Lean protocol-machine executions.
#[derive(Debug, Clone, Serialize)]
pub struct ComparisonResult {
    pub equivalent: bool,
    pub semantic_audit_equivalent: bool,
    pub session_statuses_equivalent: bool,
    pub semantic_handoffs_equivalent: bool,
    pub invalidation_artifacts_equivalent: bool,
    pub rust_semantic_audit: Vec<TickedObsEvent<ProtocolMachineTraceEvent>>,
    pub lean_semantic_audit: Vec<TickedObsEvent<ProtocolMachineTraceEvent>>,
    #[serde(default)]
    pub diff: Option<Value>,
    pub lean_output: ProtocolMachineRunOutput,
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

/// Result from Lean reconfiguration-transition validation entrypoint.
#[derive(Debug, Clone, Serialize)]
pub struct ReconfigurationValidationResult {
    pub valid: bool,
    #[serde(default)]
    pub errors: Vec<LeanStructuredError>,
    pub event: Option<ReconfigurationEvent>,
}

/// Runner for invoking the Lean protocol-machine runner binary.
pub struct ProtocolMachineRunner {
    binary_path: PathBuf,
}

impl ProtocolMachineRunner {
    /// Default path to the protocol-machine runner binary (relative to workspace root).
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/protocol_machine_runner";
    /// Default timeout for protocol-machine runner process invocations.
    pub const DEFAULT_TIMEOUT_MS: u64 = 120_000;

    fn process_timeout() -> Duration {
        let ms = std::env::var("TELLTALE_PROTOCOL_MACHINE_TIMEOUT_MS")
            .ok()
            .and_then(|raw| raw.parse::<u64>().ok())
            .unwrap_or(Self::DEFAULT_TIMEOUT_MS);
        Duration::from_millis(ms.max(1))
    }

    fn wait_with_timeout(
        mut child: Child,
        timeout: Duration,
        operation: &str,
    ) -> Result<Output, ProtocolMachineRunnerError> {
        let stdout_handle = child.stdout.take().map(|mut stdout| {
            thread::spawn(move || {
                let mut buf = Vec::new();
                let _ = stdout.read_to_end(&mut buf);
                buf
            })
        });
        let stderr_handle = child.stderr.take().map(|mut stderr| {
            thread::spawn(move || {
                let mut buf = Vec::new();
                let _ = stderr.read_to_end(&mut buf);
                buf
            })
        });
        let start = Instant::now();
        loop {
            // bounded: exits on child completion or timeout
            match child.try_wait()? {
                Some(status) => {
                    let stdout = stdout_handle
                        .map(|handle| handle.join().unwrap_or_default())
                        .unwrap_or_default();
                    let stderr = stderr_handle
                        .map(|handle| handle.join().unwrap_or_default())
                        .unwrap_or_default();
                    return Ok(Output {
                        status,
                        stdout,
                        stderr,
                    });
                }
                None => {
                    if start.elapsed() >= timeout {
                        if let Err(err) = child.kill() {
                            eprintln!(
                                "best-effort child.kill failed during timeout handling: {err}"
                            );
                        }
                        if let Err(err) = child.wait() {
                            eprintln!(
                                "best-effort child.wait failed during timeout handling: {err}"
                            );
                        }
                        if let Some(handle) = stdout_handle {
                            let _ = handle.join();
                        }
                        if let Some(handle) = stderr_handle {
                            let _ = handle.join();
                        }
                        return Err(ProtocolMachineRunnerError::TimedOut {
                            operation: operation.to_string(),
                            timeout_ms: u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX),
                        });
                    }
                    thread::sleep(Duration::from_millis(10));
                }
            }
        }
    }

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

    /// Create a new protocol-machine runner with the default binary path.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolMachineRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn new() -> Result<Self, ProtocolMachineRunnerError> {
        match Self::get_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(ProtocolMachineRunnerError::BinaryNotFound(PathBuf::from(
                Self::DEFAULT_BINARY_PATH,
            ))),
        }
    }

    /// Create a protocol-machine runner with a custom binary path.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolMachineRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn with_binary_path(path: impl AsRef<Path>) -> Result<Self, ProtocolMachineRunnerError> {
        let binary_path = PathBuf::from(path.as_ref());
        if !binary_path.exists() || !binary_path.is_file() {
            return Err(ProtocolMachineRunnerError::BinaryNotFound(binary_path));
        }
        Ok(Self { binary_path })
    }

    /// Try to create a runner, returning None if the binary is unavailable.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        Self::new().ok()
    }

    /// Check if the protocol-machine runner binary is available at the default path.
    #[must_use]
    pub fn is_available() -> bool {
        Self::get_binary_path().is_some()
    }

    /// Require that the protocol-machine runner binary is available.
    ///
    /// # Panics
    ///
    /// Panics if the binary is not available.
    pub fn require_available() {
        if !Self::is_available() {
            panic!(
                "\n\
                ╔══════════════════════════════════════════════════════════════════╗\n\
                ║  LEAN PROTOCOL-MACHINE RUNNER REQUIRED                          ║\n\
                ╠══════════════════════════════════════════════════════════════════╣\n\
                ║  The Lean protocol-machine runner is required but not found.    ║\n\
                ║                                                                  ║\n\
                ║  To build Lean runners:                                          ║\n\
                ║    cd lean && lake build protocol_machine_runner                 ║\n\
                ║                                                                  ║\n\
                ║  Or with Nix:                                                    ║\n\
                ║    nix develop --command bash -c \"cd lean && lake build protocol_machine_runner\" ║\n\
                ║                                                                  ║\n\
                ║  Expected path: {path}          \n\
                ╚══════════════════════════════════════════════════════════════════╝\n",
                path = Self::DEFAULT_BINARY_PATH
            );
        }
    }

    /// Run the protocol-machine runner and return the parsed output.
    ///
    /// # Errors
    ///
    /// Returns a [`ProtocolMachineRunnerError`] if the process fails or output is invalid.
    pub fn run(
        &self,
        input: &ProtocolMachineRunInput,
    ) -> Result<ProtocolMachineRunOutput, ProtocolMachineRunnerError> {
        crate::schema::ensure_supported_schema_version(
            &input.schema_version,
            "ProtocolMachineRunInput",
        )
        .map_err(ProtocolMachineRunnerError::ParseError)?;

        let payload = serde_json::to_vec(input)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;

        let mut cmd = Command::new(&self.binary_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(ProtocolMachineRunnerError::TempFileError)?;

        if let Some(mut stdin) = cmd.stdin.take() {
            stdin.write_all(&payload)?;
        }

        let output = Self::wait_with_timeout(cmd, Self::process_timeout(), "run")?;

        if !output.status.success() {
            return Err(ProtocolMachineRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }

        let out_value: Value = serde_json::from_slice(&output.stdout)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
        parse_protocol_machine_run_output(out_value)
    }

    /// Run the Lean protocol-machine execution entrypoint.
    ///
    /// # Errors
    ///
    /// Returns an error if the process fails or output is invalid.
    pub fn run_protocol_machine(
        &self,
        input: &ProtocolMachineRunInput,
    ) -> Result<ProtocolMachineRunOutput, ProtocolMachineRunnerError> {
        self.run(input)
    }

    /// Run a generic Lean protocol-machine validation operation.
    ///
    /// # Errors
    ///
    /// Returns an error if the process fails or output is invalid.
    pub fn run_validation_operation(
        &self,
        operation: &str,
        payload: &Value,
    ) -> Result<Value, ProtocolMachineRunnerError> {
        let input = serde_json::json!({
            "schema_version": crate::schema::canonical_schema_version(),
            "operation": operation,
            "payload": payload,
        });
        let bytes = serde_json::to_vec(&input)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;

        let mut cmd = Command::new(&self.binary_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(ProtocolMachineRunnerError::TempFileError)?;

        if let Some(mut stdin) = cmd.stdin.take() {
            stdin.write_all(&bytes)?;
        }

        let output = Self::wait_with_timeout(cmd, Self::process_timeout(), operation)?;
        if !output.status.success() {
            return Err(ProtocolMachineRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
        serde_json::from_slice(&output.stdout)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))
    }

    /// Validate a semantic audit against Lean-side protocol-machine checks.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn validate_trace(
        &self,
        choreographies: &[ChoreographyJson],
        rust_trace: &[ProtocolMachineTraceEvent],
    ) -> Result<TraceValidation, ProtocolMachineRunnerError> {
        let payload = serde_json::json!({
            "choreographies": choreographies,
            "trace": rust_trace,
        });
        let response = self.run_validation_operation("validateTrace", &payload)?;
        Ok(TraceValidation {
            valid: parse_required_valid(&response, "validateTrace")?,
            errors: parse_structured_errors(&response),
        })
    }

    /// Run the Lean reference simulator operation.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails or output cannot be decoded.
    pub fn run_reference_simulation(
        &self,
        input: &SimRunInput,
    ) -> Result<SimRunOutput, ProtocolMachineRunnerError> {
        crate::schema::ensure_supported_schema_version(&input.schema_version, "SimRunInput")
            .map_err(ProtocolMachineRunnerError::ParseError)?;
        let payload = serde_json::to_value(input)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
        let response = self.run_validation_operation("runSimulation", &payload)?;
        parse_sim_run_output(response)
    }

    /// Validate simulator trace output against Lean reference rules.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn validate_simulation_trace(
        &self,
        input: &SimRunInput,
        trace: &[ProtocolMachineTraceEvent],
    ) -> Result<SimTraceValidation, ProtocolMachineRunnerError> {
        let payload = simulation_trace_payload(input, trace);
        let response = self.run_validation_operation("validateSimulationTrace", &payload)?;
        parse_sim_trace_validation(&response)
    }

    /// Run the same choreography in Lean and compare normalized semantic audits.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails.
    pub fn compare_execution(
        &self,
        choreography: &ChoreographyJson,
        rust_output: &ProtocolMachineRunOutput,
    ) -> Result<ComparisonResult, ProtocolMachineRunnerError> {
        let input = ProtocolMachineRunInput {
            schema_version: crate::schema::canonical_schema_version(),
            choreographies: vec![choreography.clone()],
            concurrency: rust_output.concurrency,
            max_steps: rust_output.steps_executed.max(1),
        };
        let lean_output = self.run_protocol_machine(&input)?;

        let rust_ticked: Vec<TickedObsEvent<ProtocolMachineTraceEvent>> = rust_output
            .trace
            .iter()
            .cloned()
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
            .collect();
        let lean_ticked: Vec<TickedObsEvent<ProtocolMachineTraceEvent>> = lean_output
            .trace
            .iter()
            .cloned()
            .map(|event| TickedObsEvent {
                tick: event.tick,
                event,
            })
            .collect();

        let rust_normalized = normalize_semantic_audit(&rust_ticked);
        let lean_normalized = normalize_semantic_audit(&lean_ticked);
        let semantic_audit_equivalent = semantic_audits_equivalent(&rust_ticked, &lean_ticked);
        let session_statuses_equivalent = normalized_session_statuses(&rust_output.sessions)
            == normalized_session_statuses(&lean_output.sessions);
        let diff = compute_execution_diff(
            &rust_normalized,
            &lean_normalized,
            &rust_output.sessions,
            &lean_output.sessions,
        );
        let semantic_handoffs_equivalent = rust_output.semantic_objects.semantic_handoffs
            == lean_output.semantic_objects.semantic_handoffs;
        let rust_invalidated_effects: Vec<_> = rust_output
            .semantic_objects
            .outstanding_effects
            .iter()
            .filter(|effect| {
                matches!(
                    effect.status,
                    crate::semantic_objects::OutstandingEffectStatus::Invalidated
                )
            })
            .map(|effect| effect.effect_id)
            .collect();
        let lean_invalidated_effects: Vec<_> = lean_output
            .semantic_objects
            .outstanding_effects
            .iter()
            .filter(|effect| {
                matches!(
                    effect.status,
                    crate::semantic_objects::OutstandingEffectStatus::Invalidated
                )
            })
            .map(|effect| effect.effect_id)
            .collect();
        let invalidation_artifacts_equivalent = rust_invalidated_effects
            == lean_invalidated_effects
            && rust_output.semantic_objects.transformation_obligations
                == lean_output.semantic_objects.transformation_obligations;

        Ok(ComparisonResult {
            equivalent: semantic_audit_equivalent && session_statuses_equivalent,
            semantic_audit_equivalent,
            session_statuses_equivalent,
            semantic_handoffs_equivalent,
            invalidation_artifacts_equivalent,
            rust_semantic_audit: rust_normalized,
            lean_semantic_audit: lean_normalized,
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
    ) -> Result<InvariantVerificationResult, ProtocolMachineRunnerError> {
        let payload = serde_json::to_value(bundle)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
        let response = self.run_validation_operation("verifyProtocolBundle", &payload)?;

        Ok(InvariantVerificationResult {
            valid: parse_required_valid(&response, "verifyProtocolBundle")?,
            errors: parse_structured_errors(&response),
            artifacts: response.get("artifacts").cloned().unwrap_or(Value::Null),
        })
    }

    /// Validate one deterministic reconfiguration transition against the Lean reference hook.
    ///
    /// # Errors
    ///
    /// Returns an error if Lean invocation fails or the returned event cannot be decoded.
    pub fn validate_reconfiguration_transition(
        &self,
        artifact_id: &str,
        policy: &ReconfigurationPolicy,
        starting_epoch: u64,
        previous_members: &[String],
        next_members: &[String],
    ) -> Result<ReconfigurationValidationResult, ProtocolMachineRunnerError> {
        let payload = serde_json::json!({
            "artifact_id": artifact_id,
            "policy": policy,
            "starting_epoch": starting_epoch,
            "previous_members": previous_members,
            "next_members": next_members,
        });
        let response =
            self.run_validation_operation("validateReconfigurationTransition", &payload)?;
        let event = response
            .get("artifacts")
            .and_then(|artifacts| artifacts.get("event"))
            .cloned()
            .map(serde_json::from_value)
            .transpose()
            .map_err(|err| ProtocolMachineRunnerError::ParseError(err.to_string()))?;

        Ok(ReconfigurationValidationResult {
            valid: parse_required_valid(&response, "validateReconfigurationTransition")?,
            errors: parse_structured_errors(&response),
            event,
        })
    }
}

/// Compute a structured diff for two normalized semantic audits.
#[must_use]
pub fn compute_trace_diff(
    rust_trace: &[TickedObsEvent<ProtocolMachineTraceEvent>],
    lean_trace: &[TickedObsEvent<ProtocolMachineTraceEvent>],
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

fn normalized_session_statuses(
    sessions: &[ProtocolMachineSessionStatus],
) -> Vec<ProtocolMachineSessionStatus> {
    let mut normalized = sessions.to_vec();
    normalized.sort_by_key(|session| session.sid);
    normalized
}

fn compute_execution_diff(
    rust_trace: &[TickedObsEvent<ProtocolMachineTraceEvent>],
    lean_trace: &[TickedObsEvent<ProtocolMachineTraceEvent>],
    rust_sessions: &[ProtocolMachineSessionStatus],
    lean_sessions: &[ProtocolMachineSessionStatus],
) -> Option<Value> {
    if let Some(diff) = compute_trace_diff(rust_trace, lean_trace) {
        return Some(diff);
    }

    let rust_sessions = normalized_session_statuses(rust_sessions);
    let lean_sessions = normalized_session_statuses(lean_sessions);
    if rust_sessions != lean_sessions {
        return Some(serde_json::json!({
            "kind": "session_status_mismatch",
            "rust": rust_sessions,
            "lean": lean_sessions,
        }));
    }

    None
}

/// Helper to build a protocol-machine runner input from JSON values.
///
/// # Errors
///
/// Returns an error if any choreography value cannot be parsed.
pub fn protocol_machine_input_from_values(
    choreographies: Vec<Value>,
    concurrency: u64,
    max_steps: u64,
) -> Result<ProtocolMachineRunInput, ProtocolMachineRunnerError> {
    let mut choreos = Vec::new();
    for value in choreographies {
        let choreo: ChoreographyJson = serde_json::from_value(value)
            .map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))?;
        choreos.push(choreo);
    }
    Ok(ProtocolMachineRunInput {
        schema_version: crate::schema::canonical_schema_version(),
        choreographies: choreos,
        concurrency,
        max_steps,
    })
}

/// Serialize a protocol-machine runner output to JSON for debugging.
pub fn output_to_json(
    output: &ProtocolMachineRunOutput,
) -> Result<Value, ProtocolMachineRunnerError> {
    serde_json::to_value(output).map_err(|e| ProtocolMachineRunnerError::ParseError(e.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::time::Duration;

    fn trace_event(kind: &str, tick: u64, session: Option<u64>) -> ProtocolMachineTraceEvent {
        ProtocolMachineTraceEvent {
            schema_version: crate::schema::canonical_schema_version(),
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
            reason: None,
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

    #[test]
    fn parse_sim_trace_validation_reads_errors_and_artifacts() {
        let response = serde_json::json!({
            "valid": false,
            "errors": [
                { "code": "sim.trace.mismatch", "path": "trace[1]", "message": "mismatch" }
            ],
            "artifacts": { "kind": "diff" }
        });
        let parsed = parse_sim_trace_validation(&response).expect("parse simulation validation");
        assert!(!parsed.valid);
        assert_eq!(parsed.errors.len(), 1);
        assert_eq!(parsed.errors[0].code, "sim.trace.mismatch");
        assert_eq!(parsed.errors[0].path.as_deref(), Some("trace[1]"));
        assert_eq!(parsed.artifacts["kind"], "diff");
    }

    #[test]
    fn parse_required_valid_rejects_missing_or_non_boolean() {
        let missing = serde_json::json!({
            "errors": []
        });
        let missing_err =
            parse_required_valid(&missing, "validateTrace").expect_err("missing valid must fail");
        assert!(matches!(
            missing_err,
            ProtocolMachineRunnerError::ParseError(_)
        ));

        let wrong_type = serde_json::json!({
            "valid": "true"
        });
        let wrong_type_err = parse_required_valid(&wrong_type, "validateTrace")
            .expect_err("non-boolean valid must fail");
        assert!(matches!(
            wrong_type_err,
            ProtocolMachineRunnerError::ParseError(_)
        ));
    }

    #[test]
    fn parse_sim_run_output_checks_schema_version() {
        let payload = serde_json::json!({
            "schema_version": crate::schema::canonical_schema_version(),
            "trace": [],
            "violations": [],
            "artifacts": {}
        });
        let parsed = parse_sim_run_output(payload).expect("parse sim run output");
        assert_eq!(
            parsed.schema_version,
            crate::schema::canonical_schema_version()
        );
    }

    #[test]
    fn simulation_trace_payload_has_expected_shape() {
        let input = SimRunInput {
            schema_version: crate::schema::canonical_schema_version(),
            scenario: serde_json::json!({ "kind": "unit-test" }),
            global_type: serde_json::json!({ "tag": "end" }),
            local_types: std::collections::BTreeMap::new(),
            initial_states: std::collections::BTreeMap::new(),
        };
        let trace = vec![trace_event("sent", 1, Some(0))];
        let payload = simulation_trace_payload(&input, &trace);
        assert_eq!(payload["input"]["schema_version"], input.schema_version);
        assert!(payload["trace"].is_array());
        assert_eq!(payload["trace"][0]["kind"], "sent");
    }

    #[test]
    fn wait_with_timeout_returns_timeout_error() {
        let child = Command::new("sh")
            .arg("-c")
            .arg("sleep 1")
            .spawn()
            .expect("spawn sleep");
        let result = ProtocolMachineRunner::wait_with_timeout(
            child,
            Duration::from_millis(10),
            "test_sleep",
        );
        assert!(matches!(
            result,
            Err(ProtocolMachineRunnerError::TimedOut { .. })
        ));
    }
}
