//! First executable nominal-command lowering, retaining the original source.

use std::collections::BTreeMap;
use std::num::NonZeroU64;

use telltale_language::ast::{
    Annotations, AuthorityBindingMode, AuthorityExpr, Branch, Choreography, EffectAuthorityClass,
    MessageType, NonEmptyVec, Protocol,
};
use telltale_machine::instr::{Instr, InvokeAction};
use telltale_machine::nominal_command::{NominalCommandCall, NominalCommandDeclaration};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::semantic_objects::{
    AgreementEvidenceKind, AgreementLevel, AgreementProfile, AgreementRule, OperationVisibility,
};

/// A source-level refusal before any VM/session/host callback is admitted.
#[derive(Debug, thiserror::Error)]
pub enum CommandCompileError {
    /// Original frontend error, retained without converting its source to a string.
    #[error(transparent)]
    Parse(#[from] telltale_language::ParseError),
    /// Original communication projection failure.
    #[error(transparent)]
    Projection(#[from] telltale_language::ProjectionError),
    /// Original communication conversion failure.
    #[error(transparent)]
    Conversion(#[from] telltale_language::ast::convert::ConversionError),
    /// The selected declaration is outside the complete first executable slice.
    #[error("unsupported nominal command: {0}")]
    Unsupported(String),
}

fn unsupported(message: &str) -> CommandCompileError {
    CommandCompileError::Unsupported(message.to_string())
}

/// Compile the selected original operation to a real command/branch image.
/// Named tick windows are explicit runtime configuration, not physical clocks.
/// Missing windows refuse; retry never resolves or resets this selection.
///
/// # Errors
/// Retains the original parser/projection error or refuses a selected contract
/// whose executable authority, result or continuation is unsupported.
pub fn compile_command_operation(
    source: &str,
    operation_name: &str,
    windows: &BTreeMap<String, NonZeroU64>,
) -> Result<CodeImage, CommandCompileError> {
    compile_command_body(source, operation_name, windows, None)
}

// Only checked sibling lowerings can replace the body after preserving their
// own explicit executable actions; this is not a public authority-erasure API.
pub(crate) fn compile_command_body(
    source: &str,
    operation_name: &str,
    windows: &BTreeMap<String, NonZeroU64>,
    body: Option<Protocol>,
) -> Result<CodeImage, CommandCompileError> {
    let parent = telltale_language::parse_choreography_str(source)?;
    let (operation, mut parsed) =
        telltale_language::parse_declared_operation(&parent, operation_name)?;
    if let Some(body) = body {
        parsed.protocol = body;
    }
    let policy = select_command_policy(&parent, &operation, windows)?;
    let binding = select_command_binding(&parent, &operation, &parsed)?;
    let role = binding.role;
    let name = binding.name;
    let continuation = binding.continuation;
    let (mut image, ok_label, err_label) =
        compile_command_branches(&parsed, role, name, continuation)?;
    let declared = binding.declaration;
    let call = NominalCommandCall {
        declaration: declared.clone(),
        enclosing_operation: operation.name,
        agreement_profile: policy.agreement_profile,
        role: role.name().to_string(),
        progress_contract: policy.contract,
        progress_window: policy.window,
        budget_ticks: policy.budget,
        result: 2,
        on_ok: 2,
        on_err: 4,
    };
    image.programs.insert(
        role.name().to_string(),
        vec![
            Instr::Invoke {
                action: InvokeAction::DeclareCommand(declared),
            },
            Instr::Invoke {
                action: InvokeAction::NominalCommand(Box::new(call)),
            },
            Instr::Offer {
                chan: 0,
                label: ok_label.to_string(),
            },
            Instr::Halt,
            Instr::Offer {
                chan: 0,
                label: err_label.to_string(),
            },
            Instr::Halt,
        ],
    );
    image
        .validate_runtime_shape()
        .map_err(CommandCompileError::Unsupported)?;
    Ok(image)
}

struct SelectedCommandPolicy {
    agreement_profile: AgreementProfile,
    contract: String,
    window: String,
    budget: NonZeroU64,
}

fn select_command_policy(
    parent: &Choreography,
    operation: &telltale_language::ast::OperationDeclaration,
    windows: &BTreeMap<String, NonZeroU64>,
) -> Result<SelectedCommandPolicy, CommandCompileError> {
    if !operation.params.is_empty()
        || operation.within.is_some()
        || operation.child_effect_aggregation.is_some()
    {
        return Err(unsupported(
            "operation parameters, fragment selection and aggregation require their own lowering",
        ));
    }
    let progress = operation
        .progress_contract
        .as_ref()
        .ok_or_else(|| unsupported("missing original progress contract"))?;
    if progress.requires_profile.is_some()
        || progress.on_timeout.is_some()
        || progress.on_stall.is_some()
    {
        return Err(unsupported(
            "execution-profile and escalation continuations must not be erased",
        ));
    }
    let window = progress
        .within_window
        .as_ref()
        .ok_or_else(|| unsupported("missing selected named progress window"))?;
    let budget = *windows.get(window).ok_or_else(|| {
        unsupported("selected original progress window has no configured tick budget")
    })?;
    let attached = operation
        .agreement
        .as_ref()
        .ok_or_else(|| unsupported("missing original agreement profile"))?;
    if attached.prestate.is_some() {
        return Err(unsupported(
            "prestate binding requires actual agreement lowering",
        ));
    }
    let profile = parent
        .agreement_profile_declarations()
        .into_iter()
        .find(|profile| profile.name == attached.profile_name)
        .ok_or_else(|| unsupported("unknown agreement profile"))?;
    // A command is not evidence. Stronger source profiles must not silently become NoAgreement.
    if profile.visibility != "immediate"
        || profile.rule != "no_agreement"
        || profile.usable_at != "none"
        || profile.finalized_at != "none"
        || profile.evidence != "witness"
    {
        return Err(unsupported(
            "first command slice supports only the explicit NoAgreement profile",
        ));
    }
    let agreement_profile = AgreementProfile {
        profile_name: profile.name,
        visibility: OperationVisibility::Immediate,
        rule: AgreementRule::NoAgreement,
        usable_at: AgreementLevel::None,
        finalized_at: AgreementLevel::None,
        required_evidence_kind: AgreementEvidenceKind::Witness,
    };

    Ok(SelectedCommandPolicy {
        agreement_profile,
        contract: progress.contract_name.clone(),
        window: window.clone(),
        budget,
    })
}

struct SelectedCommandBinding<'a> {
    role: &'a telltale_language::ast::Role,
    name: &'a str,
    continuation: &'a Protocol,
    declaration: NominalCommandDeclaration,
}

fn select_command_binding<'a>(
    parent: &Choreography,
    operation: &telltale_language::ast::OperationDeclaration,
    parsed: &'a Choreography,
) -> Result<SelectedCommandBinding<'a>, CommandCompileError> {
    let Protocol::Let {
        execution_role: Some(role),
        name,
        mode,
        expr:
            AuthorityExpr::Check {
                effect,
                operation: effect_operation,
                args,
            },
        continuation,
        linear: false,
    } = &parsed.protocol
    else {
        return Err(unsupported("expected one explicitly placed command check"));
    };
    if *role.name() != operation.owner_role
        || role.is_parameterized()
        || role.is_indexed()
        || !args.is_empty()
    {
        return Err(unsupported(
            "command must execute at its declared concrete owner role with Unit input",
        ));
    }
    let interface = parent
        .effect_interface_declarations()
        .into_iter()
        .find(|interface| &interface.name == effect)
        .ok_or_else(|| unsupported("unknown nominal interface"))?;
    if !parent.protocol_uses().contains(effect) {
        return Err(unsupported("nominal interface is not admitted by uses"));
    }
    let declaration = interface
        .operations
        .iter()
        .find(|declaration| &declaration.name == effect_operation)
        .ok_or_else(|| unsupported("unknown nominal operation"))?;
    let readiness = *mode == AuthorityBindingMode::Authoritative;
    let expected_class = if readiness {
        EffectAuthorityClass::Authoritative
    } else {
        EffectAuthorityClass::Command
    };
    if !matches!(
        mode,
        AuthorityBindingMode::Plain | AuthorityBindingMode::Authoritative
    ) || declaration.authority_class != expected_class
        || declaration.semantic_class
            != if readiness {
                "authoritative"
            } else {
                "best_effort"
            }
        || declaration.region != "session"
        || declaration.agreement_use != "forbidden"
        || declaration.reentrancy != "allow"
        || declaration.input_type.trim() != "Unit"
        || declaration
            .output_type
            .split_whitespace()
            .collect::<Vec<_>>()
            != [
                "Result",
                "String",
                if readiness {
                    "ReadinessWitness"
                } else {
                    "Bool"
                },
            ]
        || !matches!(declaration.progress.as_str(), "immediate" | "may_block")
    {
        return Err(unsupported("nominal declaration is outside the supported Command Unit -> Result String Bool contract"));
    }
    Ok(SelectedCommandBinding {
        role,
        name,
        continuation,
        declaration: NominalCommandDeclaration {
            interface: effect.clone(),
            operation: effect_operation.clone(),
            may_block: declaration.progress == "may_block",
            readiness_predicate: readiness.then(|| format!("{effect}.{effect_operation}")),
        },
    })
}

fn inspect_command_branch(
    branch: &Protocol,
    role: &telltale_language::ast::Role,
) -> Result<(String, MessageType), CommandCompileError> {
    let Protocol::Send {
        from,
        to,
        message,
        continuation,
        annotations,
        from_annotations,
        to_annotations,
    } = branch
    else {
        return Err(unsupported(
            "first slice requires a terminal unit-message branch",
        ));
    };
    if from != role
        || to == role
        || to.is_parameterized()
        || to.is_indexed()
        || message.payload.is_some()
        || message.type_annotation.is_some()
        || !matches!(continuation.as_ref(), Protocol::End)
        || !annotations.dsl_entries().is_empty()
        || !from_annotations.dsl_entries().is_empty()
        || !to_annotations.dsl_entries().is_empty()
    {
        return Err(unsupported(
            "branch role, payload, annotations or continuation would require additional lowering",
        ));
    }
    Ok((to.name().to_string(), message.clone()))
}

fn compile_command_branches(
    parsed: &Choreography,
    role: &telltale_language::ast::Role,
    name: &str,
    continuation: &Protocol,
) -> Result<(CodeImage, String, String), CommandCompileError> {
    let Protocol::Case {
        expr: AuthorityExpr::Var(scrutinee),
        branches,
    } = continuation
    else {
        return Err(unsupported(
            "command result requires an immediate typed case continuation",
        ));
    };
    if scrutinee != name || branches.len() != 2 {
        return Err(unsupported(
            "case must consume this exact result with Ok and Err branches",
        ));
    }
    let ok = branches
        .iter()
        .find(|branch| branch.pattern.constructor == "Ok")
        .ok_or_else(|| unsupported("missing Ok continuation"))?;
    let err = branches
        .iter()
        .find(|branch| branch.pattern.constructor == "Err")
        .ok_or_else(|| unsupported("missing Err continuation"))?;
    if ok.pattern.binders.len() != 1 || err.pattern.binders.len() != 1 {
        return Err(unsupported(
            "typed Result patterns require their payload binders",
        ));
    }
    let (ok_peer, ok_label) = inspect_command_branch(&ok.protocol, role)?;
    let (err_peer, err_label) = inspect_command_branch(&err.protocol, role)?;
    if ok_peer != err_peer || ok_label.name == err_label.name {
        return Err(unsupported(
            "Result branches require distinct labels to the same peer",
        ));
    }
    let skeleton = Choreography {
        name: parsed.name.clone(),
        namespace: parsed.namespace.clone(),
        roles: parsed.roles.clone(),
        attrs: parsed.attrs.clone(),
        protocol: Protocol::Choice {
            role: role.clone(),
            annotations: Annotations::new(),
            branches: NonEmptyVec::new(vec![
                Branch {
                    label: ok_label.name.clone(),
                    guard: None,
                    protocol: ok.protocol.clone(),
                },
                Branch {
                    label: err_label.name.clone(),
                    guard: None,
                    protocol: err.protocol.clone(),
                },
            ])
            .map_err(|_| unsupported("missing communication continuation"))?,
        },
    };
    let global = telltale_language::ast::choreography_to_global(&skeleton)?;
    let mut locals = BTreeMap::new();
    for role in &skeleton.roles {
        let local = telltale_language::project(&skeleton, role)?;
        let local = telltale_language::ast::local_to_local_r(&local)?;
        locals.insert(role.name().to_string(), local);
    }
    let image = CodeImage::from_local_types(&locals, &global);
    Ok((image, ok_label.name.to_string(), err_label.name.to_string()))
}
