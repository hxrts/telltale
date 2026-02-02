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

    /// Validate the image: check well-formedness of the global type.
    ///
    /// In a full implementation, this would also re-project and verify that
    /// the claimed local types match the projection. For now, it checks
    /// well-formedness only.
    ///
    /// # Errors
    ///
    /// Returns `LoadResult::ValidationFailed` if the global type is not well-formed.
    pub fn validate(self) -> Result<CodeImage, LoadResult> {
        if !self.global_type.well_formed() {
            return Err(LoadResult::ValidationFailed {
                reason: "global type is not well-formed".into(),
            });
        }
        Ok(CodeImage {
            programs: self.programs,
            global_type: self.global_type,
            local_types: self.local_types,
        })
    }
}
