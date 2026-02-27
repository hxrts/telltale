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
//! use telltale_lean_bridge::equivalence::{EquivalenceChecker, GoldenDir};
//!
//! // Fast golden file testing
//! let checker = EquivalenceChecker::with_golden_dir("golden");
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
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use telltale_theory::projection::{project, ProjectionError};
use telltale_types::GlobalType;
use thiserror::Error;

#[path = "equivalence_golden_cases.rs"]
mod golden;

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
    #[error("Lean runner not available - build with: cd lean && lake build telltale_validator")]
    LeanNotAvailable,

    /// Golden file mismatch detected.
    #[error("Golden file drift detected: {path}")]
    GoldenDrift { path: PathBuf },
}

/// Result of an equivalence check.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EquivalenceResult {
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
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
            schema_version: crate::schema::default_schema_version(),
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
            schema_version: crate::schema::default_schema_version(),
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
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
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
    /// Schema version for this payload.
    #[serde(default = "crate::schema::default_schema_version")]
    pub schema_version: String,
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

/// Strictness selection for equivalence comparisons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Strictness {
    /// Exact JSON/trace matching.
    Strict,
    /// Structural matching with tolerated non-semantic differences.
    Lenient,
}

impl Strictness {
    const fn is_strict(self) -> bool {
        matches!(self, Self::Strict)
    }
}

impl From<bool> for Strictness {
    fn from(value: bool) -> Self {
        if value {
            Self::Strict
        } else {
            Self::Lenient
        }
    }
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

    /// Create a checker with golden files only and explicit strictness mode.
    pub fn with_golden_dir_strict(
        dir: impl AsRef<Path>,
        strictness: impl Into<Strictness>,
    ) -> Self {
        Self {
            config: EquivalenceConfig {
                golden_dir: dir.as_ref().to_path_buf(),
                strict: strictness.into().is_strict(),
            },
            runner: None,
        }
    }

    /// Return a checker with strict mode enabled or disabled.
    pub fn with_strict_mode(mut self, strictness: impl Into<Strictness>) -> Self {
        self.config.strict = strictness.into().is_strict();
        self
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

    fn parse_projections_map(
        lean_output: &Value,
    ) -> Result<HashMap<String, Value>, EquivalenceError> {
        crate::projection_payload::parse_projections_field(lean_output)
            .map_err(EquivalenceError::ParseError)
    }

    fn ensure_projection_roles(
        expected_roles: &[String],
        projections: &HashMap<String, Value>,
    ) -> Result<(), EquivalenceError> {
        let expected: BTreeSet<String> = expected_roles.iter().cloned().collect();
        let actual: BTreeSet<String> = projections.keys().cloned().collect();

        let missing: Vec<String> = expected.difference(&actual).cloned().collect();
        let unexpected: Vec<String> = actual.difference(&expected).cloned().collect();

        if missing.is_empty() && unexpected.is_empty() {
            return Ok(());
        }

        Err(EquivalenceError::ParseError(format!(
            "projection role-set mismatch: missing={missing:?}, unexpected={unexpected:?}"
        )))
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

        let expected = lean_output
            .get("projection")
            .or_else(|| lean_output.get("result"))
            .ok_or_else(|| {
                EquivalenceError::ParseError("Missing projection in Lean output".into())
            })?
            .clone();

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

        let mut results = Vec::new();
        let projections = Self::parse_projections_map(&lean_output)?;
        Self::ensure_projection_roles(&global.roles(), &projections)?;

        for (role, expected) in projections {
            // Compute Rust projection
            let rust_local = project(global, &role)?;
            let rust_output = local_to_json(&rust_local);

            let result = self.compare_local_types(&role, &rust_output, &expected)?;
            results.push(result);
        }

        Ok(results)
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
        let equivalent = if self.config.strict {
            serde_json::to_string(rust_output).ok() == serde_json::to_string(expected).ok()
        } else {
            self.json_structurally_equal(rust_output, expected)
        };
        if equivalent {
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
    #[allow(clippy::only_used_in_recursion)]
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

    #[test]
    fn test_strict_mode_is_wired_into_comparison() {
        let non_strict = EquivalenceChecker::with_golden_dir_strict("golden", false);
        let strict = EquivalenceChecker::with_golden_dir_strict("golden", true);

        let left: Value = serde_json::from_str(r#"{"a":1,"b":2}"#).expect("left json");
        let right: Value = serde_json::from_str(r#"{"a":1,"b":2}"#).expect("right json");
        let mismatch: Value = serde_json::from_str(r#"{"a":1,"b":3}"#).expect("mismatch json");

        let strict_result = strict
            .compare_local_types("A", &left, &right)
            .expect("strict comparison result");
        let strict_mismatch = strict
            .compare_local_types("A", &left, &mismatch)
            .expect("strict mismatch comparison");
        let non_strict_result = non_strict
            .compare_local_types("A", &left, &right)
            .expect("non-strict comparison result");
        let non_strict_mismatch = non_strict
            .compare_local_types("A", &left, &mismatch)
            .expect("non-strict mismatch comparison");

        assert!(strict_result.equivalent);
        assert!(non_strict_result.equivalent);
        assert!(!strict_mismatch.equivalent);
        assert!(!non_strict_mismatch.equivalent);
    }

    #[test]
    fn test_projection_role_set_check_rejects_missing_roles() {
        let expected = vec!["A".to_string(), "B".to_string()];
        let mut projections = HashMap::new();
        projections.insert("A".to_string(), serde_json::json!({"kind": "end"}));

        let err = EquivalenceChecker::ensure_projection_roles(&expected, &projections)
            .expect_err("must reject missing role");
        assert!(matches!(err, EquivalenceError::ParseError(_)));
    }

    #[test]
    fn test_projection_role_set_check_rejects_unexpected_roles() {
        let expected = vec!["A".to_string()];
        let mut projections = HashMap::new();
        projections.insert("A".to_string(), serde_json::json!({"kind": "end"}));
        projections.insert("B".to_string(), serde_json::json!({"kind": "end"}));

        let err = EquivalenceChecker::ensure_projection_roles(&expected, &projections)
            .expect_err("must reject unexpected role");
        assert!(matches!(err, EquivalenceError::ParseError(_)));
    }

    #[test]
    fn test_projection_role_set_check_accepts_exact_match() {
        let expected = vec!["A".to_string(), "B".to_string()];
        let mut projections = HashMap::new();
        projections.insert("A".to_string(), serde_json::json!({"kind": "end"}));
        projections.insert("B".to_string(), serde_json::json!({"kind": "end"}));

        EquivalenceChecker::ensure_projection_roles(&expected, &projections)
            .expect("must accept exact role set");
    }
}
