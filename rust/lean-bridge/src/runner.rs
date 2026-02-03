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
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use tempfile::NamedTempFile;
use thiserror::Error;

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
}

/// Choreography input for the VM runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChoreographyJson {
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
        if !binary_path.exists() {
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
        let output = Command::new(&self.binary_path)
            .arg("--choreography")
            .arg(choreo_file.path())
            .arg("--program")
            .arg(program_file.path())
            .arg("--json-log")
            .arg(json_log.path())
            .output()?;

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

        // Parse JSON log if available
        if json_log_path.exists() {
            let log_content = std::fs::read_to_string(json_log_path)?;
            if !log_content.trim().is_empty() {
                let log_json: Value = serde_json::from_str(&log_content)
                    .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

                return self.parse_json_log(&log_json, stdout);
            }
        }

        // Fallback: assume success if process exited 0
        Ok(LeanValidationResult {
            success: true,
            role: String::new(),
            message: String::new(),
            raw_output: stdout,
        })
    }

    /// Parse the JSON log output from the runner.
    fn parse_json_log(
        &self,
        log: &Value,
        raw_output: String,
    ) -> Result<LeanValidationResult, LeanRunnerError> {
        let role = log["role"].as_str().unwrap_or("").to_string();
        let success = log["status"].as_str() == Some("ok");
        let message = log["message"].as_str().unwrap_or("").to_string();

        Ok(LeanValidationResult {
            success,
            role,
            message,
            raw_output,
        })
    }

    // ========================================================================
    // Projection Methods (validator export mode)
    // ========================================================================

    /// Default path to the VM runner binary (relative to workspace root).
    pub const VM_RUNNER_BINARY_PATH: &'static str = "lean/.lake/build/bin/vm_runner";

    /// Get the full path to the VM runner binary.
    fn get_vm_runner_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::VM_RUNNER_BINARY_PATH))
            .filter(|p| p.exists())
    }

    /// Check if the validator binary is available for projection export.
    #[must_use]
    pub fn is_projection_available() -> bool {
        Self::is_available()
    }

    /// Project a GlobalType for a list of roles using the Lean validator export mode.
    ///
    /// Writes the GlobalType JSON to a temp file, runs
    /// `telltale_validator --export-all-projections`, and parses the projections.
    ///
    /// # Output format (parsed from output file)
    ///
    /// ```json
    /// {
    ///   "success": true,
    ///   "projections": { "A": { "kind": "send", ... }, "B": { "kind": "recv", ... } }
    /// }
    /// ```
    pub fn project(
        &self,
        global_json: &Value,
        roles: &[String],
    ) -> Result<std::collections::HashMap<String, Value>, LeanRunnerError> {
        let mut input_file = NamedTempFile::new()?;
        serde_json::to_writer(&mut input_file, global_json)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;
        input_file.flush()?;

        let output_file = NamedTempFile::new()?;
        let output_path = output_file.path().to_path_buf();

        let output = Command::new(&self.binary_path)
            .arg("--export-all-projections")
            .arg(input_file.path())
            .arg("--output")
            .arg(&output_path)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let output_contents = std::fs::read_to_string(&output_path)?;
        let payload: Value = serde_json::from_str(&output_contents)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        if let Some(false) = payload.get("success").and_then(|v| v.as_bool()) {
            let err = payload
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("Lean export failed");
            return Err(LeanRunnerError::ParseError(err.to_string()));
        }

        let projections_val = payload
            .get("projections")
            .ok_or_else(|| LeanRunnerError::ParseError("missing projections field".to_string()))?;

        let projections_map = match projections_val {
            Value::Object(map) => map
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect::<std::collections::HashMap<_, _>>(),
            Value::Array(items) => {
                let mut out = std::collections::HashMap::new();
                for item in items {
                    let obj = item.as_object().ok_or_else(|| {
                        LeanRunnerError::ParseError("invalid projection entry".to_string())
                    })?;
                    let role = obj
                        .get("role")
                        .and_then(|v| v.as_str())
                        .ok_or_else(|| {
                            LeanRunnerError::ParseError("missing role in projection".to_string())
                        })?;
                    let local = obj
                        .get("local_type")
                        .or_else(|| obj.get("localType"))
                        .ok_or_else(|| {
                            LeanRunnerError::ParseError(
                                "missing local_type in projection".to_string(),
                            )
                        })?;
                    out.insert(role.to_string(), local.clone());
                }
                out
            }
            _ => {
                return Err(LeanRunnerError::ParseError(
                    "invalid projections format".to_string(),
                ))
            }
        };

        if roles.is_empty() {
            return Ok(projections_map);
        }

        let mut selected = std::collections::HashMap::new();
        for role in roles {
            let projection = projections_map.get(role).ok_or_else(|| {
                LeanRunnerError::ParseError(format!("missing projection for role {role}"))
            })?;
            selected.insert(role.clone(), projection.clone());
        }
        Ok(selected)
    }

    // ========================================================================
    // VM Runner Methods
    // ========================================================================

    /// Run one or more choreographies on the Lean VM at a given concurrency level.
    ///
    /// # Errors
    ///
    /// Returns an error if the VM runner binary is missing, the process fails,
    /// or the output is not valid JSON.
    pub fn run_vm_protocol(
        &self,
        choreographies: &[ChoreographyJson],
        concurrency: usize,
        max_steps: usize,
    ) -> Result<Value, LeanRunnerError> {
        let vm_path = Self::get_vm_runner_path().ok_or_else(|| {
            LeanRunnerError::BinaryNotFound(PathBuf::from(Self::VM_RUNNER_BINARY_PATH))
        })?;

        let input = serde_json::json!({
            "choreographies": choreographies,
            "concurrency": concurrency,
            "max_steps": max_steps
        });
        let input_str = serde_json::to_string(&input)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let mut child = Command::new(&vm_path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;

        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            stdin
                .write_all(input_str.as_bytes())
                .map_err(LeanRunnerError::TempFileError)?;
        }

        let output = child.wait_with_output()?;
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        if !output.status.success() {
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let json: Value = serde_json::from_str(&stdout)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;
        Ok(json)
    }

    // ========================================================================
    // Export Methods (for equivalence testing)
    // ========================================================================

    /// Export Lean's projection for a single role.
    ///
    /// Invokes the Lean runner with `--export-projection` mode and returns
    /// the JSON result containing either the computed LocalTypeR or an error.
    ///
    /// # JSON Output Format
    ///
    /// On success:
    /// ```json
    /// {
    ///   "success": true,
    ///   "projection": { "kind": "send", ... }
    /// }
    /// ```
    ///
    /// On error:
    /// ```json
    /// {
    ///   "success": false,
    ///   "error": "decode failure"
    /// }
    /// ```
    pub fn export_projection(
        &self,
        global_json: &Value,
        role: &str,
    ) -> Result<Value, LeanRunnerError> {
        // Create temp files
        let input_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        // Write GlobalType JSON to input file
        std::fs::write(
            input_file.path(),
            serde_json::to_string_pretty(global_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        // Invoke Lean runner in export-projection mode
        let output = Command::new(&self.binary_path)
            .arg("--export-projection")
            .arg(input_file.path())
            .arg("--role")
            .arg(role)
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        // Read and parse the output file
        let result_content = std::fs::read_to_string(output_file.path())?;
        let result: Value = serde_json::from_str(&result_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        Ok(result)
    }

    /// Export Lean's projection for all roles in a GlobalType.
    ///
    /// Invokes the Lean runner with `--export-all-projections` mode and returns
    /// the JSON result containing projections for all roles.
    ///
    /// # JSON Output Format
    ///
    /// On success:
    /// ```json
    /// {
    ///   "success": true,
    ///   "projections": {
    ///     "Alice": { "kind": "send", ... },
    ///     "Bob": { "kind": "recv", ... }
    ///   }
    /// }
    /// ```
    ///
    /// On error:
    /// ```json
    /// {
    ///   "success": false,
    ///   "error": "decode failure"
    /// }
    /// ```
    pub fn export_all_projections(&self, global_json: &Value) -> Result<Value, LeanRunnerError> {
        // Create temp files
        let input_file = NamedTempFile::new()?;
        let output_file = NamedTempFile::new()?;

        // Write GlobalType JSON to input file
        std::fs::write(
            input_file.path(),
            serde_json::to_string_pretty(global_json)
                .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?,
        )?;

        // Invoke Lean runner in export-all-projections mode
        let output = Command::new(&self.binary_path)
            .arg("--export-all-projections")
            .arg(input_file.path())
            .arg("--output")
            .arg(output_file.path())
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        // Read and parse the output file
        let result_content = std::fs::read_to_string(output_file.path())?;
        let result: Value = serde_json::from_str(&result_content)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    // No log parsing tests yet; validator logs are integration-tested elsewhere.
}
