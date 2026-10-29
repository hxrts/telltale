//! Dynamic choreography loading.
//!
//! Matches `CodeImage`, `UntrustedImage`, `loadTrusted`, `loadUntrusted`
//! from `lean/Runtime/ProtocolMachine/Model/Program.lean`.

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
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct UntrustedImage {
    /// Bytecode programs per role.
    pub programs: BTreeMap<String, Vec<Instr>>,
    /// The global type this image was derived from.
    pub global_type: GlobalType,
    /// Projected local types per role (claimed, not yet verified).
    pub local_types: BTreeMap<String, LocalTypeR>,
}

/// Result of validating an untrusted code image in tests.
#[cfg(test)]
#[derive(Debug)]
pub(crate) enum LoadResult {
    /// Validation failed.
    ValidationFailed {
        /// Description of the validation failure.
        reason: String,
    },
}

#[cfg(test)]
impl LoadResult {
    fn reason(&self) -> &str {
        match self {
            Self::ValidationFailed { reason } => reason,
        }
    }
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

    /// Validate trusted-image runtime shape constraints.
    ///
    /// # Errors
    ///
    /// Returns an error string when the image shape violates ProtocolMachine runtime
    /// expectations (role coverage, type coverage, or global well-formedness).
    pub fn validate_runtime_shape(&self) -> Result<(), String> {
        if self.programs.is_empty() {
            return Err("code image must contain at least one role program".to_string());
        }
        if !self.global_type.well_formed() {
            return Err("code image global type is not well-formed".to_string());
        }
        for (role, program) in &self.programs {
            Self::validate_runtime_role_program(role, program)?;
        }
        let program_roles: Vec<&String> = self.programs.keys().collect();
        let type_roles: Vec<&String> = self.local_types.keys().collect();
        if program_roles != type_roles {
            return Err(format!(
                "code image role mismatch: programs {:?}, local_types {:?}",
                program_roles, type_roles
            ));
        }
        Ok(())
    }

    fn validate_runtime_role_program(role: &str, program: &[Instr]) -> Result<(), String> {
        let mut declared = BTreeMap::new();
        let mut executable = false;
        for (pc, instruction) in program.iter().enumerate() {
            match instruction {
                Instr::Invoke {
                    action: crate::instr::InvokeAction::DeclareCommand(declaration),
                } => {
                    if executable
                        || declaration.interface.is_empty()
                        || declaration.operation.is_empty()
                    {
                        return Err("nominal declarations must precede executable instructions and name an operation".into());
                    }
                    let key = (&declaration.interface, &declaration.operation);
                    if declared.insert(key, declaration).is_some() {
                        return Err("duplicate nominal declaration".into());
                    }
                }
                Instr::Invoke {
                    action: crate::instr::InvokeAction::OperationLifecycle(action),
                } => {
                    executable = true;
                    Self::validate_runtime_operation_action(role, program, pc, action)?;
                }
                Instr::Invoke {
                    action: crate::instr::InvokeAction::NominalCommand(call),
                } => {
                    executable = true;
                    if declared
                        .get(&(&call.declaration.interface, &call.declaration.operation))
                        .copied()
                        != Some(&call.declaration)
                    {
                        return Err("nominal invocation has no exact admitted declaration".into());
                    }
                    Self::validate_runtime_nominal_call(role, program, pc, call)?;
                }
                _ => executable = true,
            }
        }
        Ok(())
    }

    fn validate_runtime_operation_action(
        role: &str,
        program: &[Instr],
        pc: usize,
        action: &crate::operation_lifecycle::OperationAction,
    ) -> Result<(), String> {
        use crate::operation_lifecycle::OperationAction;
        let name = match action {
            OperationAction::Begin { declaration } => {
                let invalid_children = declaration.required_children.iter().any(|slot| {
                    slot.pc <= pc
                        || declaration
                            .required_children
                            .iter()
                            .filter(|other| other.pc == slot.pc)
                            .count()
                            != 1
                        || slot.call.enclosing_operation != declaration.name
                        || slot.call.role != declaration.role
                        || slot.call.agreement_profile != declaration.agreement_profile
                        || slot.call.progress_contract != declaration.progress_contract
                        || slot.call.progress_window != declaration.progress_window
                        || slot.call.budget_ticks != declaration.budget_ticks
                        || !matches!(program.get(slot.pc), Some(Instr::Invoke {
                            action: crate::instr::InvokeAction::NominalCommand(actual)
                        }) if actual.as_ref() == &slot.call)
                });
                let has_terminal = program.iter().skip(pc + 1).any(|instruction| matches!(instruction,
                    Instr::Invoke { action: crate::instr::InvokeAction::OperationLifecycle(terminal) }
                    if matches!(terminal.as_ref(), OperationAction::Resolve { operation, .. }
                        | OperationAction::Invalidate { operation } if operation == &declaration.name)));
                if declaration.role != role
                    || !declaration.supported()
                    || invalid_children
                    || !has_terminal
                {
                    return Err("invalid original operation role/policy".into());
                }
                return Ok(());
            }
            OperationAction::Resolve {
                outcome: crate::operation_lifecycle::OperationResolution::Timeout(_),
                ..
            } => {
                return Err(
                    "timeout resolution requires actual original escalation lowering".into(),
                );
            }
            OperationAction::Await { operation }
            | OperationAction::Resolve { operation, .. }
            | OperationAction::Invalidate { operation } => operation,
        };
        if !program.iter().take(pc).any(|instruction| {
            matches!(instruction,
            Instr::Invoke { action: crate::instr::InvokeAction::OperationLifecycle(prior) }
            if matches!(prior.as_ref(), OperationAction::Begin { declaration }
                if declaration.name == *name && declaration.role == role))
        }) {
            return Err("operation transition has no original static begin".into());
        }
        Ok(())
    }

    fn validate_runtime_nominal_call(
        role: &str,
        program: &[Instr],
        pc: usize,
        call: &crate::nominal_command::NominalCommandCall,
    ) -> Result<(), String> {
        for instruction in program.iter().take(pc) {
            if let Instr::Invoke {
                action: crate::instr::InvokeAction::OperationLifecycle(action),
            } = instruction
            {
                if let crate::operation_lifecycle::OperationAction::Begin { declaration } =
                    action.as_ref()
                {
                    if declaration.name == call.enclosing_operation
                        && declaration
                            .required_children
                            .iter()
                            .filter(|slot| slot.pc == pc && slot.call == *call)
                            .count()
                            != 1
                    {
                        return Err(
                            "source child is absent from the exact original operation manifest"
                                .into(),
                        );
                    }
                }
            }
        }
        if !call.supported_agreement()
            || call.role != role
            || call.result == 0
            || call.on_ok == call.on_err
            || call.enclosing_operation.is_empty()
            || call.progress_contract.is_empty()
            || call.progress_window.is_empty()
            || call.on_ok <= pc
            || call.on_err <= pc
        {
            return Err("invalid nominal role, result destination or continuation".into());
        }
        for target in [call.on_ok, call.on_err] {
            let tail = if matches!(program.get(target + 1), Some(Instr::Invoke {
                action: crate::instr::InvokeAction::OperationLifecycle(action)
            }) if matches!(action.as_ref(), crate::operation_lifecycle::OperationAction::Await { operation }
                if operation == &call.enclosing_operation))
            {
                target + 2
            } else {
                target + 1
            };
            let terminal = matches!(program.get(tail), Some(Instr::Halt))
                || (matches!(program.get(tail), Some(Instr::Invoke {
                    action: crate::instr::InvokeAction::OperationLifecycle(action)
                }) if matches!(action.as_ref(), crate::operation_lifecycle::OperationAction::Resolve { operation, .. }
                    if operation == &call.enclosing_operation))
                    && matches!(program.get(tail + 1), Some(Instr::Halt)));
            if !matches!(program.get(target), Some(Instr::Offer { chan: 0, .. })) || !terminal {
                return Err("first nominal slice requires terminal offer continuations".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
impl UntrustedImage {
    /// Create an untrusted image from projected local types.
    #[must_use]
    pub(crate) fn from_local_types(
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
    pub(crate) fn validate(self) -> Result<CodeImage, LoadResult> {
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
            .expect("projection should succeed for a well-formed test global")
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
        let err = result.expect_err("validation should fail");
        assert!(err.reason().contains("local type mismatch"));
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
        let err = result.expect_err("validation should fail");
        assert!(err.reason().contains("not well-formed"));
    }

    #[test]
    fn test_trusted_and_untrusted_validated_images_match() {
        let global = simple_global();
        let projected: BTreeMap<_, _> = telltale_theory::projection::project_all(&global)
            .expect("projection should succeed for a well-formed test global")
            .into_iter()
            .collect();

        let trusted = CodeImage::from_local_types(&projected, &global);
        let validated = UntrustedImage::from_local_types(&projected, &global)
            .validate()
            .expect("untrusted image should validate");

        assert_eq!(trusted.global_type, validated.global_type);
        assert_eq!(trusted.local_types, validated.local_types);
        assert_eq!(trusted.programs, validated.programs);
    }

    #[test]
    fn test_validate_ignores_untrusted_program_payload_and_recompiles() {
        let global = simple_global();
        let projected: BTreeMap<_, _> = telltale_theory::projection::project_all(&global)
            .expect("projection should succeed for a well-formed test global")
            .into_iter()
            .collect();

        let mut untrusted = UntrustedImage::from_local_types(&projected, &global);
        untrusted
            .programs
            .insert("A".to_string(), vec![Instr::Halt, Instr::Halt]);
        untrusted
            .programs
            .insert("B".to_string(), vec![Instr::Yield]);

        let validated = untrusted
            .validate()
            .expect("validation should reproject and recompile");
        let trusted = CodeImage::from_local_types(&projected, &global);

        assert_eq!(validated.local_types, trusted.local_types);
        assert_eq!(validated.programs, trusted.programs);
    }

    #[test]
    fn test_trusted_runtime_shape_rejects_program_local_type_role_mismatch() {
        let global = simple_global();
        let projected: BTreeMap<_, _> = telltale_theory::projection::project_all(&global)
            .expect("projection should succeed for a well-formed test global")
            .into_iter()
            .collect();
        let mut image = CodeImage::from_local_types(&projected, &global);
        image.programs.remove("B");
        assert!(image.validate_runtime_shape().is_err());
    }
}
