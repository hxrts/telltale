//! Cross-validation between Rust and Lean implementations.
//!
//! This module provides utilities to validate that Rust implementations
//! produce the same results as the verified Lean definitions.

use crate::export::{global_to_json, local_to_json};
use crate::import::{json_to_global, json_to_local, ImportError};
use crate::runner::LeanRunner;
use serde_json::Value;
use telltale_types::{GlobalType, LocalTypeR};
use thiserror::Error;

/// Result of a validation operation.
#[derive(Debug, Clone)]
pub enum ValidationResult {
    /// Validation passed
    Valid,
    /// Validation failed with a reason
    Invalid(String),
    /// Validation could not be performed
    Error(String),
}

impl ValidationResult {
    /// Returns true if validation passed.
    pub fn is_valid(&self) -> bool {
        matches!(self, ValidationResult::Valid)
    }

    /// Returns true if validation failed.
    pub fn is_invalid(&self) -> bool {
        matches!(self, ValidationResult::Invalid(_))
    }
}

/// Errors during validation.
#[derive(Debug, Error)]
pub enum ValidateError {
    #[error("Import error: {0}")]
    Import(#[from] ImportError),

    #[error("Structure mismatch: {0}")]
    StructureMismatch(String),

    #[error("Lean execution failed: {0}")]
    LeanExecutionFailed(String),
}

/// Validator for cross-checking Rust and Lean results.
pub struct Validator {
    /// Path to Lean executable (if available)
    lean_path: Option<String>,
}

impl Default for Validator {
    fn default() -> Self {
        Self::new()
    }
}

impl Validator {
    /// Create a new validator.
    pub fn new() -> Self {
        Self { lean_path: None }
    }

    /// Set the path to the Lean executable.
    pub fn with_lean_path(mut self, path: impl Into<String>) -> Self {
        self.lean_path = Some(path.into());
        self
    }

    /// Validate that a GlobalType round-trips through JSON correctly.
    pub fn validate_global_roundtrip(&self, g: &GlobalType) -> ValidationResult {
        let json = global_to_json(g);
        match json_to_global(&json) {
            Ok(parsed) => {
                if global_types_equal(g, &parsed) {
                    ValidationResult::Valid
                } else {
                    ValidationResult::Invalid("Round-trip produced different structure".to_string())
                }
            }
            Err(e) => ValidationResult::Error(format!("Parse error: {}", e)),
        }
    }

    /// Validate that a LocalTypeR round-trips through JSON correctly.
    pub fn validate_local_roundtrip(&self, lt: &LocalTypeR) -> ValidationResult {
        let json = local_to_json(lt);
        match json_to_local(&json) {
            Ok(parsed) => {
                if local_types_equal(lt, &parsed) {
                    ValidationResult::Valid
                } else {
                    ValidationResult::Invalid("Round-trip produced different structure".to_string())
                }
            }
            Err(e) => ValidationResult::Error(format!("Parse error: {}", e)),
        }
    }

    /// Compare Rust projection result with Lean JSON output.
    pub fn compare_projection(
        &self,
        rust_result: &LocalTypeR,
        lean_json: &Value,
    ) -> Result<ValidationResult, ValidateError> {
        let lean_result = json_to_local(lean_json)?;

        if local_types_equal(rust_result, &lean_result) {
            Ok(ValidationResult::Valid)
        } else {
            Ok(ValidationResult::Invalid(format!(
                "Projection mismatch:\n  Rust: {:?}\n  Lean: {:?}",
                rust_result, lean_result
            )))
        }
    }

    /// Compare Rust subtyping result with Lean result.
    pub fn compare_subtyping(&self, rust_result: bool, lean_result: bool) -> ValidationResult {
        if rust_result == lean_result {
            ValidationResult::Valid
        } else {
            ValidationResult::Invalid(format!(
                "Subtyping mismatch: Rust={}, Lean={}",
                rust_result, lean_result
            ))
        }
    }

    /// Validate a program against a choreography using the Lean runner.
    ///
    /// This invokes the actual Lean verification binary to check that
    /// the exported program matches the projected local type.
    ///
    /// # Arguments
    ///
    /// * `choreography_json` - The choreography in Lean-compatible JSON format
    /// * `program_json` - The program export in Lean-compatible JSON format
    ///
    /// # Errors
    ///
    /// Returns an error if the Lean runner is unavailable or fails.
    pub fn validate_projection_with_lean(
        &self,
        choreography_json: &Value,
        program_json: &Value,
    ) -> Result<ValidationResult, ValidateError> {
        let runner = match &self.lean_path {
            Some(path) => LeanRunner::with_binary_path(path)
                .map_err(|e| ValidateError::LeanExecutionFailed(e.to_string()))?,
            None => {
                LeanRunner::new().map_err(|e| ValidateError::LeanExecutionFailed(e.to_string()))?
            }
        };

        match runner.validate(choreography_json, program_json) {
            Ok(result) => {
                if result.success {
                    Ok(ValidationResult::Valid)
                } else {
                    let msgs: Vec<String> = result
                        .branches
                        .iter()
                        .filter(|b| !b.status)
                        .map(|b| format!("{}: {}", b.name, b.message))
                        .collect();
                    Ok(ValidationResult::Invalid(msgs.join("; ")))
                }
            }
            Err(e) => Err(ValidateError::LeanExecutionFailed(e.to_string())),
        }
    }

    /// Check if the Lean runner is available.
    ///
    /// Returns true if the Lean binary exists at the expected path.
    #[must_use]
    pub fn lean_available(&self) -> bool {
        match &self.lean_path {
            Some(path) => std::path::Path::new(path).exists(),
            None => LeanRunner::is_available(),
        }
    }
}

/// Check if two GlobalTypes are structurally equal.
fn global_types_equal(g1: &GlobalType, g2: &GlobalType) -> bool {
    match (g1, g2) {
        (GlobalType::End, GlobalType::End) => true,

        (
            GlobalType::Comm {
                sender: s1,
                receiver: r1,
                branches: b1,
            },
            GlobalType::Comm {
                sender: s2,
                receiver: r2,
                branches: b2,
            },
        ) => {
            s1 == s2
                && r1 == r2
                && b1.len() == b2.len()
                && b1
                    .iter()
                    .zip(b2.iter())
                    .all(|((l1, c1), (l2, c2))| labels_equal(l1, l2) && global_types_equal(c1, c2))
        }

        (GlobalType::Mu { var: v1, body: b1 }, GlobalType::Mu { var: v2, body: b2 }) => {
            v1 == v2 && global_types_equal(b1, b2)
        }

        (GlobalType::Var(n1), GlobalType::Var(n2)) => n1 == n2,

        _ => false,
    }
}

/// Check if two LocalTypeRs are structurally equal.
fn local_types_equal(lt1: &LocalTypeR, lt2: &LocalTypeR) -> bool {
    match (lt1, lt2) {
        (LocalTypeR::End, LocalTypeR::End) => true,

        (
            LocalTypeR::Send {
                partner: p1,
                branches: b1,
            },
            LocalTypeR::Send {
                partner: p2,
                branches: b2,
            },
        ) => {
            p1 == p2
                && b1.len() == b2.len()
                && b1
                    .iter()
                    .zip(b2.iter())
                    .all(|((l1, _vt1, c1), (l2, _vt2, c2))| {
                        labels_equal(l1, l2) && local_types_equal(c1, c2)
                    })
        }

        (
            LocalTypeR::Recv {
                partner: p1,
                branches: b1,
            },
            LocalTypeR::Recv {
                partner: p2,
                branches: b2,
            },
        ) => {
            p1 == p2
                && b1.len() == b2.len()
                && b1
                    .iter()
                    .zip(b2.iter())
                    .all(|((l1, _vt1, c1), (l2, _vt2, c2))| {
                        labels_equal(l1, l2) && local_types_equal(c1, c2)
                    })
        }

        (LocalTypeR::Mu { var: v1, body: b1 }, LocalTypeR::Mu { var: v2, body: b2 }) => {
            v1 == v2 && local_types_equal(b1, b2)
        }

        (LocalTypeR::Var(n1), LocalTypeR::Var(n2)) => n1 == n2,

        _ => false,
    }
}

/// Check if two Labels are equal.
fn labels_equal(l1: &telltale_types::Label, l2: &telltale_types::Label) -> bool {
    l1.name == l2.name && l1.sort == l2.sort
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    #[test]
    fn test_global_roundtrip_valid() {
        let validator = Validator::new();
        let g = GlobalType::comm("A", "B", vec![(Label::new("msg"), GlobalType::End)]);

        assert!(validator.validate_global_roundtrip(&g).is_valid());
    }

    #[test]
    fn test_local_roundtrip_valid() {
        let validator = Validator::new();
        let lt = LocalTypeR::send("B", Label::new("hello"), LocalTypeR::End);

        assert!(validator.validate_local_roundtrip(&lt).is_valid());
    }

    #[test]
    fn test_recursive_roundtrip() {
        let validator = Validator::new();
        let g = GlobalType::mu(
            "X",
            GlobalType::comm("A", "B", vec![(Label::new("ping"), GlobalType::var("X"))]),
        );

        assert!(validator.validate_global_roundtrip(&g).is_valid());
    }

    #[test]
    fn test_compare_subtyping_match() {
        let validator = Validator::new();
        let result = validator.compare_subtyping(true, true);
        assert!(result.is_valid());
    }

    #[test]
    fn test_compare_subtyping_mismatch() {
        let validator = Validator::new();
        let result = validator.compare_subtyping(true, false);
        assert!(result.is_invalid());
    }

    #[test]
    fn test_compare_projection() {
        use serde_json::json;

        let validator = Validator::new();
        let rust_result = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let lean_json = json!({
            "kind": "send",
            "partner": "B",
            "branches": [{
                "label": { "name": "msg", "sort": "unit" },
                "continuation": { "kind": "end" }
            }]
        });

        let result = validator
            .compare_projection(&rust_result, &lean_json)
            .unwrap();
        assert!(result.is_valid());
    }
}
