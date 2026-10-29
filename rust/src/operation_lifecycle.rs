//! Executable source operation boundaries; no callback or worker is invented by begin.

use std::collections::BTreeMap;
use std::num::NonZeroU64;

use telltale_language::ast::{CommitmentOutcome, Protocol};
use telltale_machine::instr::{Instr, InvokeAction};
use telltale_machine::operation_lifecycle::{
    OperationAction, OperationDeclaration, OperationResolution,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::semantic_objects::{
    AgreementEvidenceKind, AgreementLevel, AgreementProfile, AgreementRule, OperationVisibility,
};
use telltale_types::{GlobalType, LocalTypeR};

use crate::nominal_command::CommandCompileError;

fn unsupported(message: &str) -> CommandCompileError {
    CommandCompileError::Unsupported(message.into())
}

/// Compile explicit boundaries of a selected operation to typed executable code.
/// The first boundary slice admits no implicit body calls, unlowered callbacks,
/// payload expressions or authority-producing resolution. They cannot disappear.
///
/// # Errors
/// Retains original parser errors and refuses every unlowered construct.
pub fn compile_operation_lifecycle(
    source: &str,
    operation_name: &str,
    windows: &BTreeMap<String, NonZeroU64>,
) -> Result<CodeImage, CommandCompileError> {
    let parent = telltale_language::parse_choreography_str(source)?;
    let (selected, parsed) = telltale_language::parse_declared_operation(&parent, operation_name)?;
    if !selected.params.is_empty()
        || selected.within.is_some()
        || selected.child_effect_aggregation.is_some()
    {
        return Err(unsupported(
            "operation argument, fragment and aggregation lowering is required",
        ));
    }
    let progress = selected
        .progress_contract
        .as_ref()
        .ok_or_else(|| unsupported("missing explicit original progress contract"))?;
    if progress.requires_profile.is_some()
        || progress.on_timeout.is_some()
        || progress.on_stall.is_some()
    {
        return Err(unsupported(
            "profile/escalation continuations cannot be erased",
        ));
    }
    let window = progress
        .within_window
        .as_ref()
        .ok_or_else(|| unsupported("missing original named logical window"))?;
    let budget = windows
        .get(window)
        .copied()
        .ok_or_else(|| unsupported("original window has no selected logical budget"))?;
    let agreement = selected
        .agreement
        .as_ref()
        .ok_or_else(|| unsupported("missing selected agreement policy"))?;
    if agreement.prestate.is_some() {
        return Err(unsupported("original prestate lowering is required"));
    }
    let profile = parent
        .agreement_profile_declarations()
        .into_iter()
        .find(|profile| profile.name == agreement.profile_name)
        .ok_or_else(|| unsupported("unknown selected agreement profile"))?;
    if profile.visibility != "immediate"
        || profile.rule != "no_agreement"
        || profile.usable_at != "none"
        || profile.finalized_at != "none"
        || profile.evidence != "witness"
    {
        return Err(unsupported(
            "stronger agreement must not become observational success",
        ));
    }
    let declaration = OperationDeclaration {
        name: selected.name,
        role: selected.owner_role,
        progress_contract: progress.contract_name.clone(),
        progress_window: window.clone(),
        budget_ticks: budget,
        requires_proof: true,
        required_children: Vec::new(),
        agreement_profile: AgreementProfile {
            profile_name: profile.name,
            visibility: OperationVisibility::Immediate,
            rule: AgreementRule::NoAgreement,
            usable_at: AgreementLevel::None,
            finalized_at: AgreementLevel::None,
            required_evidence_kind: AgreementEvidenceKind::Witness,
        },
    };
    if let Protocol::Begin { continuation, .. } = &parsed.protocol {
        if matches!(continuation.as_ref(), Protocol::Let { .. }) {
            return compile_child_boundaries(
                source,
                operation_name,
                windows,
                &parsed.protocol,
                &declaration,
            );
        }
    }
    let mut code = Vec::new();
    lower_boundaries(&parsed.protocol, &declaration, &mut code, false, false)?;
    let locals = parsed
        .roles
        .iter()
        .map(|role| (role.name().to_string(), LocalTypeR::End))
        .collect();
    let mut image = CodeImage::from_local_types(&locals, &GlobalType::End);
    code.push(Instr::Halt);
    let target = image
        .programs
        .get_mut(&declaration.role)
        .ok_or_else(|| unsupported("declared owner role is absent"))?;
    *target = code;
    Ok(image)
}

fn lower_boundaries(
    protocol: &Protocol,
    declaration: &OperationDeclaration,
    code: &mut Vec<Instr>,
    begun: bool,
    resolved: bool,
) -> Result<(), CommandCompileError> {
    let (action, continuation, next_begun, next_resolved) = match protocol {
        Protocol::Begin { operation, args, progress, continuation } if !begun && !resolved
            && operation == &declaration.name && args.is_empty() && progress.is_none() =>
            (OperationAction::Begin { declaration: declaration.clone() }, continuation, true, false),
        Protocol::Await { operation, continuation } if begun && !resolved && operation == &declaration.name =>
            (OperationAction::Await { operation: operation.clone() }, continuation, true, false),
        Protocol::Resolve { operation, outcome, continuation } if begun && !resolved && operation == &declaration.name => {
            let outcome = match outcome {
                CommitmentOutcome::Success(None) => OperationResolution::Success(None),
                CommitmentOutcome::Failure(None) => OperationResolution::Failure(None),
                CommitmentOutcome::Cancelled => OperationResolution::Cancelled,
                // Timeout needs its actual original window-escalation branch, not a caller-forged tag.
                _ => return Err(unsupported("resolution payload or timeout branch requires actual typed lowering")),
            };
            (OperationAction::Resolve { operation: operation.clone(), outcome }, continuation, true, true)
        },
        Protocol::Invalidate { operation, continuation } if begun && !resolved && operation == &declaration.name =>
            (OperationAction::Invalidate { operation: operation.clone() }, continuation, true, true),
        Protocol::End if begun && resolved => return Ok(()),
        _ => return Err(unsupported("original operation must have one explicit begin and terminal resolution; no unsupported body may be erased")),
    };
    code.push(Instr::Invoke {
        action: InvokeAction::OperationLifecycle(Box::new(action)),
    });
    lower_boundaries(continuation, declaration, code, next_begun, next_resolved)
}

fn branch_resolution(
    tail: &Protocol,
    operation: &str,
) -> Result<(bool, OperationResolution), CommandCompileError> {
    let (await_child, tail) = if let Protocol::Await {
        operation: actual,
        continuation,
    } = tail
    {
        if actual != operation {
            return Err(unsupported(
                "await must name the original enclosing instance",
            ));
        }
        (true, continuation.as_ref())
    } else {
        (false, tail)
    };
    let Protocol::Resolve {
        operation: actual,
        outcome,
        continuation,
    } = tail
    else {
        return Err(unsupported(
            "each original command branch must explicitly resolve its enclosing operation",
        ));
    };
    if actual != operation || !matches!(continuation.as_ref(), Protocol::End) {
        return Err(unsupported("resolution must consume this exact enclosing operation and preserve its terminal continuation"));
    }
    let outcome = match outcome {
        CommitmentOutcome::Success(None) => OperationResolution::Success(None),
        CommitmentOutcome::Failure(None) => OperationResolution::Failure(None),
        CommitmentOutcome::Cancelled => OperationResolution::Cancelled,
        _ => {
            return Err(unsupported(
                "typed resolution payload/timeout lowering remains required",
            ))
        }
    };
    Ok((await_child, outcome))
}

fn compile_resolution_branch(
    label: &str,
    offer: &Instr,
    operation_name: &str,
    resolutions: &BTreeMap<String, (bool, OperationResolution)>,
) -> Result<Vec<Instr>, CommandCompileError> {
    let (await_child, resolution) = resolutions
        .get(label)
        .ok_or_else(|| unsupported("missing exact original branch resolution"))?;
    let mut code = vec![offer.clone()];
    if *await_child {
        code.push(Instr::Invoke {
            action: InvokeAction::OperationLifecycle(Box::new(OperationAction::Await {
                operation: operation_name.into(),
            })),
        });
    }
    code.push(Instr::Invoke {
        action: InvokeAction::OperationLifecycle(Box::new(OperationAction::Resolve {
            operation: operation_name.into(),
            outcome: resolution.clone(),
        })),
    });
    code.push(Instr::Halt);
    Ok(code)
}

fn compile_child_boundaries(
    source: &str,
    operation_name: &str,
    windows: &BTreeMap<String, NonZeroU64>,
    protocol: &Protocol,
    declaration: &OperationDeclaration,
) -> Result<CodeImage, CommandCompileError> {
    let Protocol::Begin {
        operation,
        args,
        progress,
        continuation,
    } = protocol
    else {
        return Err(unsupported(
            "child operation requires an explicit original begin",
        ));
    };
    if operation != operation_name || !args.is_empty() || progress.is_some() {
        return Err(unsupported(
            "begin must use the exact original selected operation policy",
        ));
    }
    let mut child = continuation.as_ref().clone();
    let Protocol::Let { continuation, .. } = &mut child else {
        return Err(unsupported("missing original nominal child"));
    };
    let Protocol::Case { branches, .. } = continuation.as_mut() else {
        return Err(unsupported("missing original typed child result branches"));
    };
    let mut resolutions = BTreeMap::new();
    for branch in branches {
        let Protocol::Send { continuation, .. } = &mut branch.protocol else {
            return Err(unsupported(
                "child branch must retain its actual terminal communication",
            ));
        };
        let resolution = branch_resolution(continuation, operation_name)?;
        if resolutions
            .insert(branch.pattern.constructor.clone(), resolution)
            .is_some()
        {
            return Err(unsupported("duplicate original child result branch"));
        }
        **continuation = Protocol::End;
    }
    let mut image =
        crate::nominal_command::compile_command_body(source, operation_name, windows, Some(child))?;
    let original = image
        .programs
        .get(&declaration.role)
        .ok_or_else(|| unsupported("original owner program is absent"))?;
    let [declared, Instr::Invoke {
        action: InvokeAction::NominalCommand(call),
    }, ok, Instr::Halt, err, Instr::Halt] = original.as_slice()
    else {
        return Err(unsupported(
            "original nominal compiler returned an unsupported executable shape",
        ));
    };
    let ok = compile_resolution_branch("Ok", ok, operation_name, &resolutions)?;
    let err = compile_resolution_branch("Err", err, operation_name, &resolutions)?;
    let mut call = call.as_ref().clone();
    call.on_ok = 3;
    call.on_err = 3 + ok.len();
    let mut original_declaration = declaration.clone();
    original_declaration.required_children.push(
        telltale_machine::operation_lifecycle::DeclaredOperationChild {
            pc: 2,
            call: call.clone(),
        },
    );
    let mut code = vec![
        declared.clone(),
        Instr::Invoke {
            action: InvokeAction::OperationLifecycle(Box::new(OperationAction::Begin {
                declaration: original_declaration,
            })),
        },
        Instr::Invoke {
            action: InvokeAction::NominalCommand(Box::new(call)),
        },
    ];
    code.extend(ok);
    code.extend(err);
    image.programs.insert(declaration.role.clone(), code);
    image
        .validate_runtime_shape()
        .map_err(CommandCompileError::Unsupported)?;
    Ok(image)
}

/// Select an executable lowering from the actual selected operation AST.
/// Unknown authority constructs refuse; this never falls back to communication
/// projection or generic host invocation.
///
/// # Errors
/// Retains original frontend errors and the selected lowerer's refusal.
pub fn compile_operation_image(
    source: &str,
    operation_name: &str,
    windows: &BTreeMap<String, NonZeroU64>,
) -> Result<CodeImage, CommandCompileError> {
    let parent = telltale_language::parse_choreography_str(source)?;
    let (_, parsed) = telltale_language::parse_declared_operation(&parent, operation_name)?;
    if matches!(parsed.protocol, Protocol::Begin { .. }) {
        compile_operation_lifecycle(source, operation_name, windows)
    } else {
        crate::compile_command_operation(source, operation_name, windows)
    }
}
