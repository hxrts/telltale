use super::types::VmCoreOp;
use super::*;

fn linear_usage_error(input: &str, message: impl Into<String>) -> ParseError {
    ParseError::Syntax {
        span: ErrorSpan::from_line_col(1, 1, input),
        message: message.into(),
    }
}

fn consume_linear_asset(
    live_assets: &mut HashSet<String>,
    asset: &str,
    input: &str,
    op: &str,
) -> Result<(), ParseError> {
    if live_assets.remove(asset) {
        Ok(())
    } else {
        Err(linear_usage_error(
            input,
            format!("linear asset '{asset}' used by {op} before acquire"),
        ))
    }
}

fn validate_preserved_linear_assets(
    input: &str,
    expected: &HashSet<String>,
    actual: &HashSet<String>,
    message: &str,
) -> Result<(), ParseError> {
    if actual == expected {
        Ok(())
    } else {
        Err(linear_usage_error(input, message))
    }
}

fn validate_linear_choice_branches(
    branches: &[types::ChoiceBranch],
    live_assets: &HashSet<String>,
    input: &str,
) -> Result<HashSet<String>, ParseError> {
    let mut merged: Option<HashSet<String>> = None;
    for branch in branches {
        let out = validate_linear_block(&branch.statements, live_assets, input)?;
        if let Some(prev) = &merged {
            if prev != &out {
                return Err(linear_usage_error(
                    input,
                    "linear assets diverge across choice branches",
                ));
            }
        } else {
            merged = Some(out);
        }
    }
    Ok(merged.unwrap_or_else(|| live_assets.clone()))
}

fn validate_linear_heartbeat(
    body: &[Statement],
    on_missing_body: &[Statement],
    live_assets: &HashSet<String>,
    input: &str,
) -> Result<HashSet<String>, ParseError> {
    let alive = validate_linear_block(body, live_assets, input)?;
    let missing = validate_linear_block(on_missing_body, live_assets, input)?;
    if alive == missing && alive == *live_assets {
        Ok(alive)
    } else {
        Err(linear_usage_error(
            input,
            "heartbeat branches must preserve identical linear assets",
        ))
    }
}

fn validate_linear_block(
    statements: &[Statement],
    incoming: &HashSet<String>,
    input: &str,
) -> Result<HashSet<String>, ParseError> {
    let mut live_assets = incoming.clone();

    for statement in statements {
        match statement {
            Statement::Let { name, expr, body } => {
                if matches!(expr, super::types::AuthorityExprSpec::Transfer { .. })
                    && !live_assets.insert(name.clone())
                {
                    return Err(linear_usage_error(
                        input,
                        format!("linear asset '{name}' bound more than once"),
                    ));
                }
                if let Some(body) = body {
                    let out = validate_linear_block(body, &live_assets, input)?;
                    validate_preserved_linear_assets(
                        input,
                        &live_assets,
                        &out,
                        "let ... in body must preserve linear assets",
                    )?;
                }
            }
            Statement::Case { branches, .. } => {
                let mut branch_blocks = Vec::with_capacity(branches.len());
                for branch in branches {
                    branch_blocks.push(branch.statements.clone());
                }
                let pseudo_branches: Vec<super::types::ChoiceBranch> = branch_blocks
                    .into_iter()
                    .map(|statements| super::types::ChoiceBranch {
                        label: quote::format_ident!("Case"),
                        guard: None,
                        statements,
                    })
                    .collect();
                live_assets =
                    validate_linear_choice_branches(&pseudo_branches, &live_assets, input)?;
            }
            Statement::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                let body_out = validate_linear_block(body, &live_assets, input)?;
                let timeout_out = validate_linear_block(on_timeout, &live_assets, input)?;
                validate_preserved_linear_assets(
                    input,
                    &body_out,
                    &timeout_out,
                    "timeout branches must preserve linear assets",
                )?;
                if let Some(on_cancel) = on_cancel {
                    let cancel_out = validate_linear_block(on_cancel, &live_assets, input)?;
                    validate_preserved_linear_assets(
                        input,
                        &body_out,
                        &cancel_out,
                        "cancel branches must preserve linear assets",
                    )?;
                }
                live_assets = body_out;
            }
            Statement::VmCoreOp { op } => match op {
                VmCoreOp::Acquire { dst, .. } => {
                    if !live_assets.insert(dst.clone()) {
                        return Err(linear_usage_error(
                            input,
                            format!("linear asset '{dst}' acquired more than once"),
                        ));
                    }
                }
                VmCoreOp::Release { evidence, .. } => {
                    consume_linear_asset(&mut live_assets, evidence, input, "release")?;
                }
                VmCoreOp::Transfer { endpoint, .. } => {
                    consume_linear_asset(&mut live_assets, endpoint, input, "transfer")?;
                }
                VmCoreOp::Fork { .. }
                | VmCoreOp::Join
                | VmCoreOp::Abort
                | VmCoreOp::Tag { .. }
                | VmCoreOp::Check { .. } => {}
            },
            Statement::Choice { branches, .. } => {
                live_assets = validate_linear_choice_branches(branches, &live_assets, input)?;
            }
            Statement::Loop { body, .. } => {
                let out = validate_linear_block(body, &live_assets, input)?;
                validate_preserved_linear_assets(
                    input,
                    &live_assets,
                    &out,
                    "loop body must preserve linear assets across iterations",
                )?;
            }
            Statement::Rec { body, .. } => {
                let out = validate_linear_block(body, &live_assets, input)?;
                validate_preserved_linear_assets(
                    input,
                    &live_assets,
                    &out,
                    "recursive body must preserve linear assets across unfoldings",
                )?;
            }
            Statement::Parallel { branches } => {
                for branch in branches {
                    let out = validate_linear_block(branch, &live_assets, input)?;
                    validate_preserved_linear_assets(
                        input,
                        &live_assets,
                        &out,
                        "parallel branches must preserve linear assets",
                    )?;
                }
            }
            Statement::Heartbeat {
                on_missing_body,
                body,
                ..
            } => {
                live_assets =
                    validate_linear_heartbeat(body, on_missing_body, &live_assets, input)?;
            }
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Publish { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Handshake { .. }
            | Statement::QuorumCollect { .. }
            | Statement::Call { .. } => {}
        }
    }

    Ok(live_assets)
}

pub(super) fn validate_linear_vm_assets(
    statements: &[Statement],
    input: &str,
) -> Result<(), ParseError> {
    validate_linear_block(statements, &HashSet::new(), input).map(|_| ())
}

pub(super) fn validate_authority_surface(
    statements: &[Statement],
    input: &str,
) -> Result<(), ParseError> {
    validate_case_exhaustiveness(statements, input)?;
    validate_linear_bindings(statements, input)?;
    Ok(())
}

fn validate_case_exhaustiveness(statements: &[Statement], input: &str) -> Result<(), ParseError> {
    for statement in statements {
        match statement {
            Statement::Case { branches, .. } => {
                let ctors: HashSet<&str> = branches
                    .iter()
                    .map(|branch| branch.pattern.constructor.as_str())
                    .collect();
                let result_family: HashSet<&str> = ["Ok", "Err"].into_iter().collect();
                let maybe_family: HashSet<&str> = ["Just", "Nothing"].into_iter().collect();
                if !ctors.is_empty() && ctors.is_subset(&result_family) && ctors != result_family {
                    return Err(linear_usage_error(
                        input,
                        "non-exhaustive Result match in authority case/of",
                    ));
                }
                if !ctors.is_empty() && ctors.is_subset(&maybe_family) && ctors != maybe_family {
                    return Err(linear_usage_error(
                        input,
                        "non-exhaustive Maybe match in authority case/of",
                    ));
                }
                for branch in branches {
                    validate_case_exhaustiveness(&branch.statements, input)?;
                }
            }
            Statement::Choice { branches, .. } => {
                for branch in branches {
                    validate_case_exhaustiveness(&branch.statements, input)?;
                }
            }
            Statement::Loop { body, .. } | Statement::Rec { body, .. } => {
                validate_case_exhaustiveness(body, input)?;
            }
            Statement::Parallel { branches } => {
                for branch in branches {
                    validate_case_exhaustiveness(branch, input)?;
                }
            }
            Statement::Heartbeat {
                on_missing_body,
                body,
                ..
            } => {
                validate_case_exhaustiveness(on_missing_body, input)?;
                validate_case_exhaustiveness(body, input)?;
            }
            Statement::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                validate_case_exhaustiveness(body, input)?;
                validate_case_exhaustiveness(on_timeout, input)?;
                if let Some(on_cancel) = on_cancel {
                    validate_case_exhaustiveness(on_cancel, input)?;
                }
            }
            Statement::Let { body, .. } => {
                if let Some(body) = body {
                    validate_case_exhaustiveness(body, input)?;
                }
            }
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Publish { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Handshake { .. }
            | Statement::QuorumCollect { .. }
            | Statement::Call { .. }
            | Statement::VmCoreOp { .. } => {}
        }
    }
    Ok(())
}

fn validate_linear_bindings(statements: &[Statement], input: &str) -> Result<(), ParseError> {
    for (idx, statement) in statements.iter().enumerate() {
        if let Statement::Let {
            name,
            expr: super::types::AuthorityExprSpec::Transfer { .. },
            body,
        } = statement
        {
            let usage_count = if let Some(body) = body {
                count_binding_uses(body, name)
            } else {
                count_binding_uses(&statements[idx + 1..], name)
            };
            if usage_count == 0 {
                return Err(linear_usage_error(
                    input,
                    format!("linear binding '{name}' is never consumed"),
                ));
            }
            if usage_count > 1 {
                return Err(linear_usage_error(
                    input,
                    format!("linear binding '{name}' is consumed more than once"),
                ));
            }
        }
        match statement {
            Statement::Choice { branches, .. } => {
                for branch in branches {
                    validate_linear_bindings(&branch.statements, input)?;
                }
            }
            Statement::Loop { body, .. } | Statement::Rec { body, .. } => {
                validate_linear_bindings(body, input)?;
            }
            Statement::Parallel { branches } => {
                for branch in branches {
                    validate_linear_bindings(branch, input)?;
                }
            }
            Statement::Heartbeat {
                on_missing_body,
                body,
                ..
            } => {
                validate_linear_bindings(on_missing_body, input)?;
                validate_linear_bindings(body, input)?;
            }
            Statement::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                validate_linear_bindings(body, input)?;
                validate_linear_bindings(on_timeout, input)?;
                if let Some(on_cancel) = on_cancel {
                    validate_linear_bindings(on_cancel, input)?;
                }
            }
            Statement::Case { branches, .. } => {
                for branch in branches {
                    validate_linear_bindings(&branch.statements, input)?;
                }
            }
            Statement::Let { body, .. } => {
                if let Some(body) = body {
                    validate_linear_bindings(body, input)?;
                }
            }
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Publish { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Handshake { .. }
            | Statement::QuorumCollect { .. }
            | Statement::Call { .. }
            | Statement::VmCoreOp { .. } => {}
        }
    }
    Ok(())
}

fn count_binding_uses(statements: &[Statement], name: &str) -> usize {
    statements
        .iter()
        .map(|statement| count_statement_uses(statement, name))
        .sum()
}

fn count_statement_uses(statement: &Statement, name: &str) -> usize {
    match statement {
        Statement::Let { expr, body, .. } => {
            count_expr_uses(expr, name)
                + body
                    .as_deref()
                    .map_or(0, |body| count_binding_uses(body, name))
        }
        Statement::Case { expr, branches } => {
            count_expr_uses(expr, name)
                + branches
                    .iter()
                    .map(|branch| count_binding_uses(&branch.statements, name))
                    .sum::<usize>()
        }
        Statement::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            count_binding_uses(body, name)
                + count_binding_uses(on_timeout, name)
                + on_cancel
                    .as_deref()
                    .map_or(0, |branch| count_binding_uses(branch, name))
        }
        Statement::Send { message, .. } | Statement::Broadcast { message, .. } => {
            message.payload.as_ref().map_or(0, |payload| {
                payload.to_string().split(name).count().saturating_sub(1)
            })
        }
        Statement::Choice { branches, .. } => branches
            .iter()
            .map(|branch| count_binding_uses(&branch.statements, name))
            .sum(),
        Statement::Loop { body, .. } | Statement::Rec { body, .. } => {
            count_binding_uses(body, name)
        }
        Statement::Parallel { branches } => branches
            .iter()
            .map(|branch| count_binding_uses(branch, name))
            .sum(),
        Statement::Heartbeat {
            on_missing_body,
            body,
            ..
        } => count_binding_uses(on_missing_body, name) + count_binding_uses(body, name),
        Statement::VmCoreOp { .. }
        | Statement::Publish { .. }
        | Statement::Continue { .. }
        | Statement::Handshake { .. }
        | Statement::QuorumCollect { .. }
        | Statement::Call { .. } => 0,
        Statement::Handoff {
            operation,
            target,
            receipt,
        } => {
            operation.split(name).count().saturating_sub(1)
                + target
                    .name()
                    .to_string()
                    .split(name)
                    .count()
                    .saturating_sub(1)
                + receipt.split(name).count().saturating_sub(1)
        }
        Statement::DependentWork {
            arg, required_for, ..
        } => {
            arg.as_ref()
                .map_or(0, |v| v.split(name).count().saturating_sub(1))
                + required_for.split(name).count().saturating_sub(1)
        }
    }
}

fn count_expr_uses(expr: &super::types::AuthorityExprSpec, name: &str) -> usize {
    match expr {
        super::types::AuthorityExprSpec::Var(var) => usize::from(var == name),
        super::types::AuthorityExprSpec::Check { args, .. }
        | super::types::AuthorityExprSpec::Observe { args, .. }
        | super::types::AuthorityExprSpec::Call { args, .. } => args
            .iter()
            .map(|arg| arg.split(name).count().saturating_sub(1))
            .sum(),
        super::types::AuthorityExprSpec::Transfer { from, to, subject } => [from, to, subject]
            .iter()
            .map(|value| value.split(name).count().saturating_sub(1))
            .sum(),
        super::types::AuthorityExprSpec::Constructor { arg, .. } => arg
            .as_ref()
            .map_or(0, |value| value.split(name).count().saturating_sub(1)),
    }
}

// RECURSION_SAFE: recursion consumes finite nested statement blocks.
fn collect_vm_required_capabilities(statements: &[Statement], out: &mut HashSet<String>) {
    for statement in statements {
        match statement {
            Statement::Let { body, .. } => {
                if let Some(body) = body {
                    collect_vm_required_capabilities(body, out);
                }
            }
            Statement::Case { branches, .. } => {
                for branch in branches {
                    collect_vm_required_capabilities(&branch.statements, out);
                }
            }
            Statement::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                collect_vm_required_capabilities(body, out);
                collect_vm_required_capabilities(on_timeout, out);
                if let Some(on_cancel) = on_cancel {
                    collect_vm_required_capabilities(on_cancel, out);
                }
            }
            Statement::VmCoreOp { op } => {
                out.insert(op.required_capability().to_string());
            }
            Statement::Choice { branches, .. } => {
                for branch in branches {
                    collect_vm_required_capabilities(&branch.statements, out);
                }
            }
            Statement::Loop { body, .. } | Statement::Rec { body, .. } => {
                collect_vm_required_capabilities(body, out);
            }
            Statement::Parallel { branches } => {
                for branch in branches {
                    collect_vm_required_capabilities(branch, out);
                }
            }
            Statement::Heartbeat {
                on_missing_body,
                body,
                ..
            } => {
                collect_vm_required_capabilities(on_missing_body, out);
                collect_vm_required_capabilities(body, out);
            }
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Publish { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Handshake { .. }
            | Statement::QuorumCollect { .. }
            | Statement::Call { .. } => {}
        }
    }
}

pub(super) fn infer_required_proof_bundles(
    explicit_required: &[String],
    proof_bundles: &[ProofBundleDecl],
    statements: &[Statement],
) -> Vec<String> {
    if !explicit_required.is_empty() {
        return Vec::new();
    }
    if proof_bundles.is_empty() {
        return Vec::new();
    }

    let mut required_caps = HashSet::new();
    collect_vm_required_capabilities(statements, &mut required_caps);
    if required_caps.is_empty() {
        return Vec::new();
    }

    let mut selected = Vec::new();
    let mut covered = HashSet::new();
    let mut caps: Vec<_> = required_caps.into_iter().collect();
    caps.sort();

    for cap in caps {
        if covered.contains(&cap) {
            continue;
        }
        let Some(bundle) = proof_bundles
            .iter()
            .find(|bundle| bundle.capabilities.iter().any(|c| c == &cap))
        else {
            return Vec::new();
        };
        if !selected.contains(&bundle.name) {
            selected.push(bundle.name.clone());
        }
        for bundle_cap in &bundle.capabilities {
            covered.insert(bundle_cap.clone());
        }
    }

    selected
}
