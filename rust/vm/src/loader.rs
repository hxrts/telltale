//! Dynamic choreography loading.
//!
//! Matches `CodeImage`, `UntrustedImage`, `loadTrusted`, `loadUntrusted`
//! from `runtime.md §10`.

use std::collections::BTreeMap;

use telltale_types::{GlobalType, LocalTypeR};

use crate::instr::Instr;

/// A verified code image: program + global type + local types.
///
/// In the Lean spec, this carries well-formedness and projection correctness
/// proofs. In Rust, the proofs are replaced by runtime validation that was
/// performed before constructing the image.
#[derive(Debug, Clone)]
pub struct CodeImage {
    /// Bytecode programs per role.
    pub programs: BTreeMap<String, Vec<Instr>>,
    /// The global type this image was derived from.
    pub global_type: GlobalType,
    /// Projected local types per role.
    pub local_types: BTreeMap<String, LocalTypeR>,
}

/// An unverified code image: program + global type, no validation proof.
///
/// Must be validated before execution via `validate`.
#[derive(Debug, Clone)]
pub struct UntrustedImage {
    /// Bytecode programs per role.
    pub programs: BTreeMap<String, Vec<Instr>>,
    /// The global type this image was derived from.
    pub global_type: GlobalType,
    /// Projected local types per role (claimed, not yet verified).
    pub local_types: BTreeMap<String, LocalTypeR>,
}

/// Result of loading a code image.
#[derive(Debug)]
pub enum LoadResult {
    /// Image loaded successfully.
    Ok,
    /// Validation failed.
    ValidationFailed {
        /// Description of the validation failure.
        reason: String,
    },
}

impl CodeImage {
    /// Create a code image from projected local types by compiling each to bytecode.
    #[must_use]
    pub fn from_local_types(
        local_types: &BTreeMap<String, LocalTypeR>,
        global_type: &GlobalType,
    ) -> Self {
        let programs = local_types
            .iter()
            .map(|(role, lt)| (role.clone(), crate::compiler::compile(lt)))
            .collect();

        Self {
            programs,
            global_type: global_type.clone(),
            local_types: local_types.clone(),
        }
    }

    /// Role names in this image.
    #[must_use]
    pub fn roles(&self) -> Vec<String> {
        self.programs.keys().cloned().collect()
    }
}

impl UntrustedImage {
    /// Create an untrusted image from projected local types.
    #[must_use]
    pub fn from_local_types(
        local_types: &BTreeMap<String, LocalTypeR>,
        global_type: &GlobalType,
    ) -> Self {
        let programs = local_types
            .iter()
            .map(|(role, lt)| (role.clone(), crate::compiler::compile(lt)))
            .collect();

        Self {
            programs,
            global_type: global_type.clone(),
            local_types: local_types.clone(),
        }
    }

    /// Validate the image: check well-formedness and projection correctness.
    ///
    /// 1. Checks that the global type is well-formed.
    /// 2. Re-projects the global type onto each role.
    /// 3. Verifies that the claimed local types match the re-projected types.
    /// 4. Recompiles from the verified local types (ignoring claimed bytecode).
    ///
    /// # Errors
    ///
    /// Returns `LoadResult::ValidationFailed` if any check fails.
    pub fn validate(self) -> Result<CodeImage, LoadResult> {
        if !self.global_type.well_formed() {
            return Err(LoadResult::ValidationFailed {
                reason: "global type is not well-formed".into(),
            });
        }

        // Re-project global type onto all roles.
        let projected =
            telltale_theory::projection::project_all(&self.global_type).map_err(|e| {
                LoadResult::ValidationFailed {
                    reason: format!("projection failed: {e}"),
                }
            })?;

        let projected_map: BTreeMap<String, LocalTypeR> = projected.into_iter().collect();

        // Verify claimed roles match projected roles.
        if self.local_types.keys().collect::<Vec<_>>() != projected_map.keys().collect::<Vec<_>>() {
            return Err(LoadResult::ValidationFailed {
                reason: format!(
                    "role mismatch: claimed {:?}, projected {:?}",
                    self.local_types.keys().collect::<Vec<_>>(),
                    projected_map.keys().collect::<Vec<_>>(),
                ),
            });
        }

        // Verify each claimed local type matches the re-projected type.
        for (role, claimed) in &self.local_types {
            let expected = &projected_map[role];
            if claimed != expected {
                return Err(LoadResult::ValidationFailed {
                    reason: format!(
                        "local type mismatch for role {role}: claimed {claimed:?}, expected {expected:?}"
                    ),
                });
            }
        }

        // Recompile from verified local types (ignore claimed bytecode).
        Ok(CodeImage::from_local_types(
            &projected_map,
            &self.global_type,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    fn simple_global() -> GlobalType {
        GlobalType::mu(
            "step",
            GlobalType::send(
                "A",
                "B",
                Label::new("msg"),
                GlobalType::send("B", "A", Label::new("msg"), GlobalType::var("step")),
            ),
        )
    }

    #[test]
    fn test_untrusted_validate_correct() {
        let global = simple_global();
        let projected: BTreeMap<_, _> = telltale_theory::projection::project_all(&global)
            .unwrap()
            .into_iter()
            .collect();
        let image = UntrustedImage::from_local_types(&projected, &global);
        let verified = image.validate();
        assert!(verified.is_ok());
    }

    #[test]
    fn test_untrusted_validate_bad_local_type() {
        let global = simple_global();
        let mut locals = BTreeMap::new();
        // Claim A has End instead of correct projection.
        locals.insert("A".to_string(), LocalTypeR::End);
        locals.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Send {
                            partner: "A".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );
        let image = UntrustedImage::from_local_types(&locals, &global);
        let result = image.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_untrusted_validate_bad_global_type() {
        // Self-communication is not well-formed.
        let global = GlobalType::send("A", "A", Label::new("msg"), GlobalType::End);
        let mut locals = BTreeMap::new();
        locals.insert("A".to_string(), LocalTypeR::End);
        let image = UntrustedImage::from_local_types(&locals, &global);
        let result = image.validate();
        assert!(result.is_err());
    }
}
