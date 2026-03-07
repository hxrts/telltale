//! Lean Runner - Invokes the Lean validator binary.
//!
//! This module provides the [`LeanRunner`] struct which wraps invocation of
//! the Lean `telltale_validator` binary for validating choreography projections.
//!
//! # Example
//!
//! ```ignore
//! use telltale_lean_bridge::runner::LeanRunner;
//! use serde_json::json;
//!
//! let runner = LeanRunner::new()?;
//! let result = runner.validate(&choreography_json, &program_json)?;
//! assert!(result.success);
//! ```

use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output};
use std::thread;
use std::time::{Duration, Instant};
use tempfile::NamedTempFile;
use thiserror::Error;

#[path = "runner_projection_export.rs"]
mod projection;

/// Errors from Lean runner operations.
#[derive(Debug, Error)]
pub enum LeanRunnerError {
    /// The Lean binary was not found at the expected path.
    #[error("Lean binary not found at {0}")]
    BinaryNotFound(PathBuf),

    /// Failed to create a temporary file for JSON exchange.
    #[error("Failed to create temp file: {0}")]
    TempFileError(#[from] std::io::Error),

    /// The Lean process exited with a non-zero status.
    #[error("Lean process failed with exit code {code}: {stderr}")]
    ProcessFailed {
        /// Exit code from the process.
        code: i32,
        /// Standard error output.
        stderr: String,
    },

    /// Failed to parse Lean output or JSON.
    #[error("Failed to parse Lean output: {0}")]
    ParseError(String),

    /// Validation failed with a specific reason.
    #[error("Validation failed: {0}")]
    ValidationFailed(String),

    /// Lean process exceeded the configured timeout.
    #[error("Lean process '{operation}' timed out after {timeout_ms}ms")]
    TimedOut {
        /// Operation name associated with the process invocation.
        operation: String,
        /// Timeout in milliseconds.
        timeout_ms: u64,
    },
}

/// Choreography input for the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChoreographyJson {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
    /// Global type JSON (Lean-compatible).
    pub global_type: Value,
    /// Role list.
    pub roles: Vec<String>,
}

/// Result of a Lean validation run.
#[derive(Debug, Clone)]
pub struct LeanValidationResult {
    /// Whether validation succeeded.
    pub success: bool,
    /// The role that was validated.
    pub role: String,
    /// Human-readable message describing the result.
    pub message: String,
    /// Raw output from the Lean process.
    pub raw_output: String,
}

/// Runner for invoking the Lean verification binary.
///
/// The runner manages invocation of the `telltale_validator` Lean executable,
/// handling temporary file creation for JSON exchange and parsing results.
pub struct LeanRunner {
    binary_path: PathBuf,
}

impl LeanRunner {
    /// Default path to the Lean binary (relative to workspace root).
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/telltale_validator";
    /// Default timeout for Lean process invocations.
    pub const DEFAULT_TIMEOUT_MS: u64 = 120_000;

    fn process_timeout() -> Duration {
        let ms = std::env::var("TELLTALE_LEAN_TIMEOUT_MS")
            .ok()
            .and_then(|raw| raw.parse::<u64>().ok())
            .unwrap_or(Self::DEFAULT_TIMEOUT_MS);
        Duration::from_millis(ms.max(1))
    }

    fn wait_with_timeout(
        mut child: Child,
        timeout: Duration,
        operation: &str,
    ) -> Result<Output, LeanRunnerError> {
        let start = Instant::now();
        loop {
            // bounded: exits on child completion or timeout
            match child.try_wait()? {
                Some(_) => return child.wait_with_output().map_err(LeanRunnerError::from),
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
                        return Err(LeanRunnerError::TimedOut {
                            operation: operation.to_string(),
                            timeout_ms: u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX),
                        });
                    }
                    thread::sleep(Duration::from_millis(10));
                }
            }
        }
    }

    fn run_command_with_timeout(
        &self,
        mut command: Command,
        operation: &str,
    ) -> Result<Output, LeanRunnerError> {
        let child = command.spawn()?;
        Self::wait_with_timeout(child, Self::process_timeout(), operation)
    }

    /// Get the workspace root path by walking up from the manifest directory.
    fn find_workspace_root() -> Option<PathBuf> {
        // Start from the manifest directory (rust/lean-bridge)
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let mut path = PathBuf::from(manifest_dir);

        // Walk up looking for the lean/.lake/ directory as a workspace root marker.
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

    /// Get the full path to the Lean binary.
    fn get_binary_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::DEFAULT_BINARY_PATH))
            .filter(|p| p.exists())
    }

    /// Create a new LeanRunner with the default binary path.
    ///
    /// # Errors
    ///
    /// Returns [`LeanRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn new() -> Result<Self, LeanRunnerError> {
        match Self::get_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(LeanRunnerError::BinaryNotFound(PathBuf::from(
                Self::DEFAULT_BINARY_PATH,
            ))),
        }
    }

    /// Create a LeanRunner with a custom binary path.
    ///
    /// # Errors
    ///
    /// Returns [`LeanRunnerError::BinaryNotFound`] if the binary doesn't exist.
    pub fn with_binary_path(path: impl AsRef<Path>) -> Result<Self, LeanRunnerError> {
        let binary_path = PathBuf::from(path.as_ref());
        if !binary_path.exists() || !binary_path.is_file() {
            return Err(LeanRunnerError::BinaryNotFound(binary_path));
        }
        Ok(Self { binary_path })
    }

    /// Try to create a runner, returning None if the binary is unavailable.
    ///
    /// This is useful for tests that should skip gracefully when Lean isn't built.
    #[must_use]
    pub fn try_new() -> Option<Self> {
        Self::new().ok()
    }

    /// Create a LeanRunner for projection export (uses the validator binary).
    ///
    /// # Errors
    ///
    /// Returns [`LeanRunnerError::BinaryNotFound`] if the validator binary doesn't exist.
    pub fn for_projection() -> Result<Self, LeanRunnerError> {
        Self::new()
    }

    /// Check if the Lean binary is available at the default path.
    #[must_use]
    pub fn is_available() -> bool {
        Self::get_binary_path().is_some()
    }

    /// Require that the Lean binary is available.
    ///
    /// This function is intended for CI environments where Lean tests should not
    /// be silently skipped. It panics with instructions if the binary is missing.
    ///
    /// # Panics
    ///
    /// Panics if the Lean binary is not available.
    pub fn require_available() {
        if !Self::is_available() {
            panic!(
                "\n\
                ╔══════════════════════════════════════════════════════════════════╗\n\
                ║  LEAN VERIFICATION REQUIRED                                       ║\n\
                ╠══════════════════════════════════════════════════════════════════╣\n\
                ║  The Lean binary is required but not found.                       ║\n\
                ║                                                                   ║\n\
                ║  To build Lean:                                                   ║\n\
                ║    cd lean && lake build telltale_validator                       ║\n\
                ║                                                                   ║\n\
                ║  Or with Nix:                                                     ║\n\
                ║    nix develop --command bash -c \"cd lean && lake build telltale_validator\"         ║\n\
                ║                                                                   ║\n\
                ║  Expected path: {path}           \n\
                ╚══════════════════════════════════════════════════════════════════╝\n",
                path = Self::DEFAULT_BINARY_PATH
            );
        }
    }

    /// Run validation with choreography and program JSON.
    ///
    /// The choreography JSON should be a GlobalType JSON object.
    ///
    /// The program JSON should have the format:
    /// ```json
    /// {
    ///   "role": "A",
    ///   "local_type": { "kind": "send", ... }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Temporary files cannot be created
    /// - JSON serialization fails
    /// - The Lean process fails to execute
    /// - Output parsing fails
    pub fn validate(
        &self,
        choreography_json: &Value,
        program_json: &Value,
    ) -> Result<LeanValidationResult, LeanRunnerError> {
        // Create temp files
        let choreo_file = NamedTempFile::new()?;
        let program_file = NamedTempFile::new()?;
        let json_log = NamedTempFile::new()?;

        // Write JSON to temp files
        std::fs::write(
            choreo_file.path(),
            serde_json::to_string_pretty(choreography_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;
        std::fs::write(
            program_file.path(),
            serde_json::to_string_pretty(program_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        // Invoke Lean runner
        let mut command = Command::new(&self.binary_path);
        command
            .arg("--choreography")
            .arg(choreo_file.path())
            .arg("--program")
            .arg(program_file.path())
            .arg("--json-log")
            .arg(json_log.path());
        let output = self.run_command_with_timeout(command, "validate")?;

        self.parse_output(output, json_log.path())
    }

    /// Parse the output from the Lean runner process.
    fn parse_output(
        &self,
        output: Output,
        json_log_path: &Path,
    ) -> Result<LeanValidationResult, LeanRunnerError> {
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !output.status.success() {
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        if !json_log_path.exists() {
            return Err(LeanRunnerError::ParseError(
                "Lean validator completed but did not emit a JSON log".to_string(),
            ));
        }

        let log_content = std::fs::read_to_string(json_log_path)?;
        if log_content.trim().is_empty() {
            return Err(LeanRunnerError::ParseError(
                "Lean validator emitted an empty JSON log".to_string(),
            ));
        }
        let log_json: Value = serde_json::from_str(&log_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        self.parse_json_log(&log_json, stdout)
    }

    /// Parse the JSON log output from the runner.
    fn parse_json_log(
        &self,
        log: &Value,
        raw_output: String,
    ) -> Result<LeanValidationResult, LeanRunnerError> {
        let role = log
            .get("role")
            .and_then(Value::as_str)
            .ok_or_else(|| LeanRunnerError::ParseError("missing string field: role".to_string()))?
            .to_string();
        let status = log.get("status").and_then(Value::as_str).ok_or_else(|| {
            LeanRunnerError::ParseError("missing string field: status".to_string())
        })?;
        let success = match status {
            "ok" => true,
            "error" => false,
            other => {
                return Err(LeanRunnerError::ParseError(format!(
                    "invalid status value in JSON log: {other}"
                )))
            }
        };
        let message = log
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();

        Ok(LeanValidationResult {
            success,
            role,
            message,
            raw_output,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::time::Duration;

    #[test]
    fn test_is_available_returns_bool() {
        // Just verify it doesn't panic and returns a bool
        let _available = LeanRunner::is_available();
    }

    #[test]
    fn test_try_new_returns_option() {
        // Should return Some if binary exists, None otherwise
        let result = LeanRunner::try_new();
        if LeanRunner::is_available() {
            assert!(result.is_some());
        } else {
            assert!(result.is_none());
        }
    }

    #[test]
    fn test_with_nonexistent_path_fails() {
        let result = LeanRunner::with_binary_path("/nonexistent/path/to/binary");
        assert!(matches!(result, Err(LeanRunnerError::BinaryNotFound(_))));
    }

    fn successful_output() -> std::process::Output {
        Command::new("sh")
            .arg("-c")
            .arg("true")
            .output()
            .expect("invoke shell")
    }

    #[test]
    fn test_parse_output_requires_json_log_file() {
        let runner = LeanRunner {
            binary_path: PathBuf::from("/tmp/fake-validator"),
        };
        let missing = std::env::temp_dir().join("missing-validator-log.json");
        let result = runner.parse_output(successful_output(), &missing);
        assert!(matches!(result, Err(LeanRunnerError::ParseError(_))));
    }

    #[test]
    fn test_parse_output_rejects_empty_json_log() {
        let runner = LeanRunner {
            binary_path: PathBuf::from("/tmp/fake-validator"),
        };
        let empty = NamedTempFile::new().expect("create temp file");
        let result = runner.parse_output(successful_output(), empty.path());
        assert!(matches!(result, Err(LeanRunnerError::ParseError(_))));
    }

    #[test]
    fn test_parse_json_log_rejects_invalid_status() {
        let runner = LeanRunner {
            binary_path: PathBuf::from("/tmp/fake-validator"),
        };
        let log = serde_json::json!({
            "role": "A",
            "status": "maybe",
            "message": "test"
        });
        let result = runner.parse_json_log(&log, String::new());
        assert!(matches!(result, Err(LeanRunnerError::ParseError(_))));
    }

    #[test]
    fn test_parse_json_log_success() {
        let runner = LeanRunner {
            binary_path: PathBuf::from("/tmp/fake-validator"),
        };
        let log = serde_json::json!({
            "role": "A",
            "status": "ok",
            "message": "coherent"
        });
        let result = runner
            .parse_json_log(&log, "stdout".to_string())
            .expect("parse valid log");
        assert!(result.success);
        assert_eq!(result.role, "A");
        assert_eq!(result.message, "coherent");
    }

    #[test]
    fn test_wait_with_timeout_returns_timeout_error() {
        let child = Command::new("sh")
            .arg("-c")
            .arg("sleep 1")
            .spawn()
            .expect("spawn sleep");
        let result = LeanRunner::wait_with_timeout(child, Duration::from_millis(10), "test_sleep");
        assert!(matches!(result, Err(LeanRunnerError::TimedOut { .. })));
    }
}
