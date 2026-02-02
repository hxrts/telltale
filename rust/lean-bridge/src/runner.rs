//! Lean Runner - Invokes the Lean verification binary.
//!
//! This module provides the [`LeanRunner`] struct which wraps invocation of
//! the Lean `telltale_runner` binary for validating choreography projections.
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

/// Result of validating a single branch.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BranchResult {
    /// Branch name (or "<default>" for unnamed branches).
    pub name: String,
    /// Whether this branch passed validation.
    pub status: bool,
    /// Human-readable message describing the result.
    pub message: String,
    /// Actions exported by the program.
    pub exported: Vec<String>,
    /// Actions from the projected local type.
    pub projected: Vec<String>,
}

/// Result of a Lean validation run.
#[derive(Debug, Clone)]
pub struct LeanValidationResult {
    /// Whether all branches passed validation.
    pub success: bool,
    /// The role that was validated.
    pub role: String,
    /// Per-branch validation results.
    pub branches: Vec<BranchResult>,
    /// Raw output from the Lean process.
    pub raw_output: String,
}

/// Runner for invoking the Lean verification binary.
///
/// The runner manages invocation of the `telltale_runner` Lean executable,
/// handling temporary file creation for JSON exchange and parsing results.
pub struct LeanRunner {
    binary_path: PathBuf,
}

impl LeanRunner {
    /// Default path to the Lean binary (relative to workspace root).
    pub const DEFAULT_BINARY_PATH: &'static str = "lean/.lake/build/bin/telltale_runner";

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

    /// Create a LeanRunner for projection only (does not require the validation binary).
    ///
    /// # Errors
    ///
    /// Returns [`LeanRunnerError::BinaryNotFound`] if the projection binary doesn't exist.
    pub fn for_projection() -> Result<Self, LeanRunnerError> {
        match Self::get_projection_binary_path() {
            Some(path) => Ok(Self { binary_path: path }),
            None => Err(LeanRunnerError::BinaryNotFound(PathBuf::from(
                Self::PROJECTION_BINARY_PATH,
            ))),
        }
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
                ║    cd lean && lake build                                          ║\n\
                ║                                                                   ║\n\
                ║  Or with Nix:                                                     ║\n\
                ║    nix develop --command bash -c \"cd lean && lake build\"         ║\n\
                ║                                                                   ║\n\
                ║  Expected path: {path}           \n\
                ╚══════════════════════════════════════════════════════════════════╝\n",
                path = Self::DEFAULT_BINARY_PATH
            );
        }
    }

    /// Run validation with choreography and program JSON.
    ///
    /// The choreography JSON should have the format:
    /// ```json
    /// {
    ///   "roles": ["A", "B"],
    ///   "actions": [{"from": "A", "to": "B", "label": "msg"}]
    /// }
    /// ```
    ///
    /// The program JSON should have the format:
    /// ```json
    /// {
    ///   "role": "A",
    ///   "programs": [{
    ///     "branch": null,
    ///     "effects": [{"kind": "send", "partner": "B", "label": "msg"}]
    ///   }]
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
            branches: vec![],
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
        let branches_arr = log["branches"].as_array();

        let branches: Vec<BranchResult> = branches_arr
            .map(|arr| {
                arr.iter()
                    .map(|b| BranchResult {
                        name: b["branch"].as_str().unwrap_or("<default>").to_string(),
                        status: b["status"].as_str() == Some("ok"),
                        message: b["message"].as_str().unwrap_or("").to_string(),
                        exported: Self::parse_action_array(&b["exported"]),
                        projected: Self::parse_action_array(&b["projected"]),
                    })
                    .collect()
            })
            .unwrap_or_default();

        let success = branches.iter().all(|b| b.status);

        Ok(LeanValidationResult {
            success,
            role,
            branches,
            raw_output,
        })
    }

    /// Parse an array of action strings from JSON.
    fn parse_action_array(arr: &Value) -> Vec<String> {
        arr.as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default()
    }

    // ========================================================================
    // Projection Methods (for physical pipeline)
    // ========================================================================

    /// Default path to the projection runner binary (relative to workspace root).
    pub const PROJECTION_BINARY_PATH: &'static str =
        "lean/.lake/build/bin/projection_runner";

    /// Get the full path to the projection runner binary.
    fn get_projection_binary_path() -> Option<PathBuf> {
        Self::find_workspace_root()
            .map(|root| root.join(Self::PROJECTION_BINARY_PATH))
            .filter(|p| p.exists())
    }

    /// Check if the projection runner binary is available.
    #[must_use]
    pub fn is_projection_available() -> bool {
        Self::get_projection_binary_path().is_some()
    }

    /// Project a GlobalType for a list of roles using the Lean projection runner.
    ///
    /// Sends the GlobalType and role list as JSON to the projection_runner binary
    /// via stdin and parses the projected LocalTypeR results from stdout.
    ///
    /// # Input format (sent to stdin)
    ///
    /// ```json
    /// {
    ///   "global_type": { "kind": "comm", ... },
    ///   "roles": ["A", "B"]
    /// }
    /// ```
    ///
    /// # Output format (parsed from stdout)
    ///
    /// ```json
    /// {
    ///   "projections": {
    ///     "A": { "kind": "send", ... },
    ///     "B": { "kind": "recv", ... }
    ///   }
    /// }
    /// ```
    pub fn project(
        &self,
        global_json: &Value,
        roles: &[String],
    ) -> Result<std::collections::HashMap<String, Value>, LeanRunnerError> {
        let projection_path = Self::get_projection_binary_path().ok_or_else(|| {
            LeanRunnerError::BinaryNotFound(PathBuf::from(Self::PROJECTION_BINARY_PATH))
        })?;

        let input = serde_json::json!({
            "global_type": global_json,
            "roles": roles
        });
        let input_str = serde_json::to_string(&input)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let mut child = Command::new(&projection_path)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;

        // Write input to stdin
        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            stdin
                .write_all(input_str.as_bytes())
                .map_err(LeanRunnerError::TempFileError)?;
        }

        let output = child.wait_with_output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            return Err(LeanRunnerError::ProcessFailed {
                code: output.status.code().unwrap_or(-1),
                stderr,
            });
        }

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let result: Value = serde_json::from_str(&stdout)
            .map_err(|e| LeanRunnerError::ParseError(e.to_string()))?;

        let projections = result
            .get("projections")
            .and_then(|v| v.as_object())
            .ok_or_else(|| {
                LeanRunnerError::ParseError("missing projections field".to_string())
            })?;

        Ok(projections
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect())
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
    ///   "result": { "kind": "send", ... }
    /// }
    /// ```
    ///
    /// On error:
    /// ```json
    /// {
    ///   "success": false,
    ///   "error": { "error": "merge_failed", ... }
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
    ///   "projections": [
    ///     { "role": "Alice", "localType": { "kind": "send", ... } },
    ///     { "role": "Bob", "localType": { "kind": "recv", ... } }
    ///   ]
    /// }
    /// ```
    ///
    /// On error:
    /// ```json
    /// {
    ///   "success": false,
    ///   "error": { "error": "merge_failed", ... }
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

    #[test]
    fn test_parse_action_array_empty() {
        let arr = serde_json::json!([]);
        let result = LeanRunner::parse_action_array(&arr);
        assert!(result.is_empty());
    }

    #[test]
    fn test_parse_action_array_with_values() {
        let arr = serde_json::json!(["send-B-msg", "recv-A-response"]);
        let result = LeanRunner::parse_action_array(&arr);
        assert_eq!(result, vec!["send-B-msg", "recv-A-response"]);
    }

    #[test]
    fn test_parse_action_array_null() {
        let arr = serde_json::json!(null);
        let result = LeanRunner::parse_action_array(&arr);
        assert!(result.is_empty());
    }
}
