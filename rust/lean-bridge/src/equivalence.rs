//! Equivalence Checking for Rust ↔ Lean Session Type Algorithms
//!
//! This module provides infrastructure for true equivalence testing between
//! Rust and Lean implementations. Unlike conformance testing (which only verifies
//! "Lean accepts Rust output"), equivalence testing verifies "Rust produces
//! the same output as Lean".
//!
//! # Architecture
//!
//! The module supports two modes:
//!
//! 1. **Golden File Mode** - Fast comparison against pre-computed Lean outputs.
//!    No Lean runtime required. Used for regular CI.
//!
//! 2. **Live Lean Mode** - Direct comparison against Lean runner output.
//!    Requires built Lean binary. Used for verification and golden regeneration.
//!
//! # Example
//!
//! ```ignore
//! use rumpsteak_lean_bridge::equivalence::{EquivalenceChecker, GoldenDir};
//!
//! // Fast golden file testing
//! let checker = EquivalenceChecker::with_golden_dir("golden/projection");
//! let result = checker.check_projection_against_golden(&global, "Alice")?;
//! assert!(result.equivalent);
//!
//! // Live Lean testing (when available)
//! if let Some(checker) = EquivalenceChecker::try_with_lean() {
//!     let result = checker.check_projection_against_lean(&global, "Alice")?;
//!     assert!(result.equivalent);
//! }
//! ```

use crate::export::{global_to_json, local_to_json};
use crate::import::ImportError;
use crate::runner::{LeanRunner, LeanRunnerError};
use rumpsteak_theory::projection::{project, ProjectionError};
use rumpsteak_types::GlobalType;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Errors from equivalence checking operations.
#[derive(Debug, Error)]
pub enum EquivalenceError {
    /// Failed to read golden file.
    #[error("Golden file not found: {0}")]
    GoldenNotFound(PathBuf),

    /// Failed to parse golden file.
    #[error("Failed to parse golden file: {0}")]
    ParseError(String),

    /// Lean runner error.
    #[error("Lean runner error: {0}")]
    LeanError(#[from] LeanRunnerError),

    /// Import error.
    #[error("Import error: {0}")]
    ImportError(#[from] ImportError),

    /// Projection error.
    #[error("Projection error: {0}")]
    ProjectionError(#[from] ProjectionError),

    /// IO error.
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// JSON error.
    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),

    /// The Lean runner is not available.
    #[error("Lean runner not available - build with: cd lean && lake build")]
    LeanNotAvailable,

    /// Golden file mismatch detected.
    #[error("Golden file drift detected: {path}")]
    GoldenDrift { path: PathBuf },
}

/// Result of an equivalence check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EquivalenceResult {
    /// Whether the Rust output matches the expected output.
    pub equivalent: bool,

    /// The Rust-computed local type (serialized).
    pub rust_output: Value,

    /// The expected local type (from golden file or Lean).
    pub expected_output: Value,

    /// Human-readable diff if not equivalent.
    pub diff: Option<String>,

    /// The role this check was performed for.
    pub role: String,
}

impl EquivalenceResult {
    /// Create a successful (equivalent) result.
    pub fn success(role: impl Into<String>, output: Value) -> Self {
        Self {
            equivalent: true,
            rust_output: output.clone(),
            expected_output: output,
            diff: None,
            role: role.into(),
        }
    }

    /// Create a failed (non-equivalent) result with diff.
    pub fn failure(
        role: impl Into<String>,
        rust_output: Value,
        expected_output: Value,
        diff: String,
    ) -> Self {
        Self {
            equivalent: false,
            rust_output,
            expected_output,
            diff: Some(diff),
            role: role.into(),
        }
    }
}

/// A bundle of golden files for a single test case.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GoldenBundle {
    /// The input GlobalType.
    pub input: Value,

    /// Map of role name to expected LocalTypeR.
    pub projections: HashMap<String, Value>,

    /// Optional coherence check result.
    pub coherence: Option<CoherenceBundle>,
}

/// Coherence check results from Lean.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoherenceBundle {
    pub linear: bool,
    pub size: bool,
    pub action: bool,
    pub uniq_labels: bool,
    pub projectable: bool,
    pub good: bool,
    pub is_coherent: bool,
}

/// Configuration for the equivalence checker.
#[derive(Debug, Clone)]
pub struct EquivalenceConfig {
    /// Path to the golden files directory.
    pub golden_dir: PathBuf,

    /// Whether to use strict comparison (exact JSON match vs structural).
    pub strict: bool,
}

impl Default for EquivalenceConfig {
    fn default() -> Self {
        Self {
            golden_dir: PathBuf::from("golden"),
            strict: false,
        }
    }
}

/// Equivalence checker for comparing Rust and Lean outputs.
pub struct EquivalenceChecker {
    config: EquivalenceConfig,
    runner: Option<LeanRunner>,
}

impl EquivalenceChecker {
    /// Create a checker with golden files only (no Lean runner).
    pub fn with_golden_dir(dir: impl AsRef<Path>) -> Self {
        Self {
            config: EquivalenceConfig {
                golden_dir: dir.as_ref().to_path_buf(),
                ..Default::default()
            },
            runner: None,
        }
    }

    /// Create a checker with both golden files and live Lean.
    ///
    /// Returns an error if the Lean runner is not available.
    pub fn with_lean(golden_dir: impl AsRef<Path>) -> Result<Self, EquivalenceError> {
        let runner = LeanRunner::new()?;
        Ok(Self {
            config: EquivalenceConfig {
                golden_dir: golden_dir.as_ref().to_path_buf(),
                ..Default::default()
            },
            runner: Some(runner),
        })
    }

    /// Try to create a checker with live Lean, returning None if unavailable.
    pub fn try_with_lean(golden_dir: impl AsRef<Path>) -> Option<Self> {
        Self::with_lean(golden_dir).ok()
    }

    /// Check if the Lean runner is available.
    pub fn has_lean(&self) -> bool {
        self.runner.is_some()
    }

    /// Get the golden directory path.
    pub fn golden_dir(&self) -> &Path {
        &self.config.golden_dir
    }

    // ========================================================================
    // Golden File Comparison
    // ========================================================================

    /// Check a Rust projection against a golden file.
    ///
    /// This is the fast path - no Lean required.
    pub fn check_projection_against_golden(
        &self,
        test_name: &str,
        global: &GlobalType,
        role: &str,
    ) -> Result<EquivalenceResult, EquivalenceError> {
        // Load the golden file
        let golden_path = self
            .config
            .golden_dir
            .join("projection")
            .join(test_name)
            .join(format!("{}.expected.json", role));

        let golden_content = std::fs::read_to_string(&golden_path)
            .map_err(|_| EquivalenceError::GoldenNotFound(golden_path.clone()))?;

        let expected: Value = serde_json::from_str(&golden_content)?;

        // Compute Rust projection
        let rust_local = project(global, role)?;
        let rust_output = local_to_json(&rust_local);

        // Compare
        self.compare_local_types(role, &rust_output, &expected)
    }

    /// Load a golden bundle for a test case.
    pub fn load_golden_bundle(&self, test_name: &str) -> Result<GoldenBundle, EquivalenceError> {
        let test_dir = self.config.golden_dir.join("projection").join(test_name);

        // Load input
        let input_path = test_dir.join("input.json");
        let input: Value = serde_json::from_str(
            &std::fs::read_to_string(&input_path)
                .map_err(|_| EquivalenceError::GoldenNotFound(input_path))?,
        )?;

        // Load projections
        let mut projections = HashMap::new();
        for entry in std::fs::read_dir(&test_dir)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_string();
            if name.ends_with(".expected.json") {
                let role = name.trim_end_matches(".expected.json").to_string();
                let content = std::fs::read_to_string(entry.path())?;
                let value: Value = serde_json::from_str(&content)?;
                projections.insert(role, value);
            }
        }

        Ok(GoldenBundle {
            input,
            projections,
            coherence: None,
        })
    }

    /// Check all projections in a golden bundle.
    pub fn check_all_projections_against_golden(
        &self,
        test_name: &str,
        global: &GlobalType,
    ) -> Result<Vec<EquivalenceResult>, EquivalenceError> {
        let bundle = self.load_golden_bundle(test_name)?;
        let mut results = Vec::new();

        for (role, expected) in &bundle.projections {
            let rust_local = project(global, role)?;
            let rust_output = local_to_json(&rust_local);
            let result = self.compare_local_types(role, &rust_output, expected)?;
            results.push(result);
        }

        Ok(results)
    }

    // ========================================================================
    // Live Lean Comparison
    // ========================================================================

    /// Check a Rust projection against live Lean output.
    ///
    /// Requires the Lean runner to be available.
    pub fn check_projection_against_lean(
        &self,
        global: &GlobalType,
        role: &str,
    ) -> Result<EquivalenceResult, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        // Export GlobalType to JSON
        let global_json = global_to_json(global);

        // Invoke Lean to get projection
        let lean_output = runner.export_projection(&global_json, role)?;

        // Check if projection succeeded
        if lean_output["success"].as_bool() != Some(true) {
            let err = lean_output["error"].to_string();
            return Err(EquivalenceError::ParseError(format!(
                "Lean projection failed: {}",
                err
            )));
        }

        let expected = lean_output["result"].clone();

        // Compute Rust projection
        let rust_local = project(global, role)?;
        let rust_output = local_to_json(&rust_local);

        // Compare
        self.compare_local_types(role, &rust_output, &expected)
    }

    /// Check all Rust projections against live Lean outputs.
    pub fn check_all_projections_against_lean(
        &self,
        global: &GlobalType,
    ) -> Result<Vec<EquivalenceResult>, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        // Export GlobalType to JSON
        let global_json = global_to_json(global);

        // Invoke Lean to get all projections
        let lean_output = runner.export_all_projections(&global_json)?;

        // Check if projection succeeded
        if lean_output["success"].as_bool() != Some(true) {
            let err = lean_output["error"].to_string();
            return Err(EquivalenceError::ParseError(format!(
                "Lean projections failed: {}",
                err
            )));
        }

        let projections = lean_output["projections"]
            .as_array()
            .ok_or_else(|| EquivalenceError::ParseError("Expected projections array".into()))?;

        let mut results = Vec::new();

        for proj in projections {
            let role = proj["role"]
                .as_str()
                .ok_or_else(|| EquivalenceError::ParseError("Expected role string".into()))?;
            let expected = proj["localType"].clone();

            // Compute Rust projection
            let rust_local = project(global, role)?;
            let rust_output = local_to_json(&rust_local);

            let result = self.compare_local_types(role, &rust_output, &expected)?;
            results.push(result);
        }

        Ok(results)
    }

    // ========================================================================
    // Golden File Generation
    // ========================================================================

    /// Generate golden files from live Lean for a GlobalType.
    ///
    /// Returns the bundle that would be written.
    pub fn generate_golden_bundle(
        &self,
        global: &GlobalType,
    ) -> Result<GoldenBundle, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        let global_json = global_to_json(global);

        // Get all projections from Lean
        let lean_output = runner.export_all_projections(&global_json)?;

        if lean_output["success"].as_bool() != Some(true) {
            let err = lean_output["error"].to_string();
            return Err(EquivalenceError::ParseError(format!(
                "Lean projections failed: {}",
                err
            )));
        }

        let projections_arr = lean_output["projections"]
            .as_array()
            .ok_or_else(|| EquivalenceError::ParseError("Expected projections array".into()))?;

        let mut projections = HashMap::new();
        for proj in projections_arr {
            let role = proj["role"]
                .as_str()
                .ok_or_else(|| EquivalenceError::ParseError("Expected role string".into()))?
                .to_string();
            let local_type = proj["localType"].clone();
            projections.insert(role, local_type);
        }

        Ok(GoldenBundle {
            input: global_json,
            projections,
            coherence: None,
        })
    }

    /// Write a golden bundle to disk.
    pub fn write_golden_bundle(
        &self,
        test_name: &str,
        bundle: &GoldenBundle,
    ) -> Result<(), EquivalenceError> {
        let test_dir = self.config.golden_dir.join("projection").join(test_name);
        std::fs::create_dir_all(&test_dir)?;

        // Write input
        let input_path = test_dir.join("input.json");
        std::fs::write(input_path, serde_json::to_string_pretty(&bundle.input)?)?;

        // Write projections
        for (role, local_type) in &bundle.projections {
            let path = test_dir.join(format!("{}.expected.json", role));
            std::fs::write(path, serde_json::to_string_pretty(local_type)?)?;
        }

        Ok(())
    }

    // ========================================================================
    // Golden Drift Detection
    // ========================================================================

    /// Check if golden files are up-to-date with current Lean.
    ///
    /// Returns a list of test cases with drift.
    pub fn check_golden_drift(&self) -> Result<Vec<String>, EquivalenceError> {
        let runner = self
            .runner
            .as_ref()
            .ok_or(EquivalenceError::LeanNotAvailable)?;

        let projection_dir = self.config.golden_dir.join("projection");
        if !projection_dir.exists() {
            return Ok(vec![]);
        }

        let mut drifted = Vec::new();

        for entry in std::fs::read_dir(&projection_dir)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                let test_name = entry.file_name().to_string_lossy().to_string();

                // Load input
                let input_path = entry.path().join("input.json");
                if !input_path.exists() {
                    continue;
                }

                let input: Value = serde_json::from_str(&std::fs::read_to_string(&input_path)?)?;

                // Get fresh Lean output
                let lean_output = runner.export_all_projections(&input)?;

                if lean_output["success"].as_bool() != Some(true) {
                    continue; // Skip failed projections
                }

                let projections_arr = lean_output["projections"].as_array();
                if projections_arr.is_none() {
                    continue;
                }

                for proj in projections_arr.unwrap() {
                    let role = match proj["role"].as_str() {
                        Some(r) => r,
                        None => continue,
                    };

                    let golden_path = entry.path().join(format!("{}.expected.json", role));
                    if !golden_path.exists() {
                        drifted.push(format!("{}:{} (missing)", test_name, role));
                        continue;
                    }

                    let golden: Value =
                        serde_json::from_str(&std::fs::read_to_string(&golden_path)?)?;
                    let fresh = proj["localType"].clone();

                    if !self.json_structurally_equal(&golden, &fresh) {
                        drifted.push(format!("{}:{}", test_name, role));
                    }
                }
            }
        }

        Ok(drifted)
    }

    // ========================================================================
    // Internal Helpers
    // ========================================================================

    /// Compare two local type JSON values.
    fn compare_local_types(
        &self,
        role: &str,
        rust_output: &Value,
        expected: &Value,
    ) -> Result<EquivalenceResult, EquivalenceError> {
        if self.json_structurally_equal(rust_output, expected) {
            Ok(EquivalenceResult::success(role, rust_output.clone()))
        } else {
            let diff = self.compute_diff(rust_output, expected);
            Ok(EquivalenceResult::failure(
                role,
                rust_output.clone(),
                expected.clone(),
                diff,
            ))
        }
    }

    /// Check if two JSON values are structurally equal (ignoring formatting).
    fn json_structurally_equal(&self, a: &Value, b: &Value) -> bool {
        match (a, b) {
            (Value::Null, Value::Null) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Number(a), Value::Number(b)) => a == b,
            (Value::String(a), Value::String(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| self.json_structurally_equal(x, y))
            }
            (Value::Object(a), Value::Object(b)) => {
                a.len() == b.len()
                    && a.iter().all(|(k, v)| {
                        b.get(k)
                            .map(|bv| self.json_structurally_equal(v, bv))
                            .unwrap_or(false)
                    })
            }
            _ => false,
        }
    }

    /// Compute a human-readable diff between two JSON values.
    fn compute_diff(&self, rust: &Value, expected: &Value) -> String {
        format!(
            "Rust:\n{}\n\nExpected (Lean):\n{}",
            serde_json::to_string_pretty(rust).unwrap_or_default(),
            serde_json::to_string_pretty(expected).unwrap_or_default()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_equivalence_result_success() {
        let result = EquivalenceResult::success("Alice", serde_json::json!({"kind": "end"}));
        assert!(result.equivalent);
        assert!(result.diff.is_none());
        assert_eq!(result.role, "Alice");
    }

    #[test]
    fn test_equivalence_result_failure() {
        let result = EquivalenceResult::failure(
            "Bob",
            serde_json::json!({"kind": "end"}),
            serde_json::json!({"kind": "send"}),
            "Mismatch".to_string(),
        );
        assert!(!result.equivalent);
        assert!(result.diff.is_some());
    }

    #[test]
    fn test_json_structural_equality() {
        let checker = EquivalenceChecker::with_golden_dir("golden");

        // Equal objects
        let a = serde_json::json!({"kind": "end"});
        let b = serde_json::json!({"kind": "end"});
        assert!(checker.json_structurally_equal(&a, &b));

        // Different objects
        let c = serde_json::json!({"kind": "send"});
        assert!(!checker.json_structurally_equal(&a, &c));

        // Nested objects
        let d = serde_json::json!({
            "kind": "comm",
            "branches": [{"label": "msg"}]
        });
        let e = serde_json::json!({
            "kind": "comm",
            "branches": [{"label": "msg"}]
        });
        assert!(checker.json_structurally_equal(&d, &e));
    }

    #[test]
    fn test_checker_has_lean() {
        let checker = EquivalenceChecker::with_golden_dir("golden");
        assert!(!checker.has_lean());

        // Try to create with Lean - may or may not succeed depending on environment
        if LeanRunner::is_available() {
            let with_lean = EquivalenceChecker::with_lean("golden").unwrap();
            assert!(with_lean.has_lean());
        }
    }
}
