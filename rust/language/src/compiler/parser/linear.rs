use super::*;

fn linear_usage_error(input: &str, message: impl Into<String>) -> ParseError {
    ParseError::Syntax {
        span: ErrorSpan::from_line_col(1, 1, input),
        message: message.into(),
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
                let mut differing_assets: Vec<_> =
                    prev.symmetric_difference(&out).cloned().collect();
                differing_assets.sort();
                let message = if let [asset] = differing_assets.as_slice() {
                    format!("linear binding '{asset}' diverges across choice branches")
                } else {
                    "linear assets diverge across choice branches".to_string()
                };
                return Err(linear_usage_error(input, message));
            }
        } else {
            merged = Some(out);
        }
    }
    Ok(merged.unwrap_or_else(|| live_assets.clone()))
}

fn validate_linear_block(
    statements: &[Statement],
    incoming: &HashSet<String>,
    input: &str,
) -> Result<HashSet<String>, ParseError> {
    let mut live_assets = incoming.clone();

    for statement in statements {
        match statement {
            Statement::Begin { .. }
            | Statement::Await { .. }
            | Statement::Resolve { .. }
            | Statement::Invalidate { .. } => {}
            Statement::Let {
                name, expr, body, ..
            } => {
                consume_live_assets_in_expr(expr, &mut live_assets);
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
            Statement::Send { .. }
            | Statement::Broadcast { .. }
            | Statement::Publish { .. }
            | Statement::PublishAuthority { .. }
            | Statement::Materialize { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Call { .. } => consume_live_assets(statement, &mut live_assets),
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
            Statement::Begin { .. }
            | Statement::Await { .. }
            | Statement::Resolve { .. }
            | Statement::Invalidate { .. } => {}
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
            | Statement::PublishAuthority { .. }
            | Statement::Materialize { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Call { .. } => {}
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
            ..
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
            let remaining = if let Some(body) = body {
                body.as_slice()
            } else {
                &statements[idx + 1..]
            };
            if binding_usage_diverges_across_choice_branches(remaining, name) {
                return Err(linear_usage_error(
                    input,
                    format!("linear binding '{name}' diverges across choice branches"),
                ));
            }
        }
        match statement {
            Statement::Begin { .. }
            | Statement::Await { .. }
            | Statement::Resolve { .. }
            | Statement::Invalidate { .. } => {}
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
            | Statement::PublishAuthority { .. }
            | Statement::Materialize { .. }
            | Statement::Handoff { .. }
            | Statement::DependentWork { .. }
            | Statement::Continue { .. }
            | Statement::Call { .. } => {}
        }
    }
    Ok(())
}

fn binding_usage_diverges_across_choice_branches(statements: &[Statement], name: &str) -> bool {
    statements
        .iter()
        .any(|statement| statement_binding_usage_diverges(statement, name))
}

fn statement_binding_usage_diverges(statement: &Statement, name: &str) -> bool {
    match statement {
        Statement::Begin { .. }
        | Statement::Await { .. }
        | Statement::Resolve { .. }
        | Statement::Invalidate { .. } => false,
        Statement::Choice { branches, .. } => {
            let counts: Vec<usize> = branches
                .iter()
                .map(|branch| count_binding_uses(&branch.statements, name))
                .collect();
            let divergent_here = counts.windows(2).any(|window| window[0] != window[1]);
            divergent_here
                || branches.iter().any(|branch| {
                    binding_usage_diverges_across_choice_branches(&branch.statements, name)
                })
        }
        Statement::Loop { body, .. } | Statement::Rec { body, .. } => {
            binding_usage_diverges_across_choice_branches(body, name)
        }
        Statement::Parallel { branches } => branches
            .iter()
            .any(|branch| binding_usage_diverges_across_choice_branches(branch, name)),
        Statement::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            binding_usage_diverges_across_choice_branches(body, name)
                || binding_usage_diverges_across_choice_branches(on_timeout, name)
                || on_cancel.as_deref().is_some_and(|branch| {
                    binding_usage_diverges_across_choice_branches(branch, name)
                })
        }
        Statement::Case { branches, .. } => {
            branches
                .iter()
                .map(|branch| count_binding_uses(&branch.statements, name))
                .collect::<Vec<_>>()
                .windows(2)
                .any(|window| window[0] != window[1])
                || branches.iter().any(|branch| {
                    binding_usage_diverges_across_choice_branches(&branch.statements, name)
                })
        }
        Statement::Let { body, .. } => body
            .as_deref()
            .is_some_and(|body| binding_usage_diverges_across_choice_branches(body, name)),
        Statement::Send { .. }
        | Statement::Broadcast { .. }
        | Statement::Publish { .. }
        | Statement::PublishAuthority { .. }
        | Statement::Materialize { .. }
        | Statement::Handoff { .. }
        | Statement::DependentWork { .. }
        | Statement::Continue { .. }
        | Statement::Call { .. } => false,
    }
}

fn count_binding_uses(statements: &[Statement], name: &str) -> usize {
    statements
        .iter()
        .map(|statement| count_statement_uses(statement, name))
        .sum()
}

fn count_statement_uses(statement: &Statement, name: &str) -> usize {
    match statement {
        Statement::Begin { .. }
        | Statement::Await { .. }
        | Statement::Resolve { .. }
        | Statement::Invalidate { .. } => 0,
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
        Statement::Publish { .. }
        | Statement::PublishAuthority { .. }
        | Statement::Materialize { .. }
        | Statement::Continue { .. }
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

fn consume_live_assets(statement: &Statement, live_assets: &mut HashSet<String>) {
    let consumed: Vec<String> = live_assets
        .iter()
        .filter(|name| count_statement_uses(statement, name) > 0)
        .cloned()
        .collect();
    for asset in consumed {
        live_assets.remove(&asset);
    }
}

fn consume_live_assets_in_expr(
    expr: &super::types::AuthorityExprSpec,
    live_assets: &mut HashSet<String>,
) {
    let consumed: Vec<String> = live_assets
        .iter()
        .filter(|name| count_expr_uses(expr, name) > 0)
        .cloned()
        .collect();
    for asset in consumed {
        live_assets.remove(&asset);
    }
}

pub(super) fn infer_required_proof_bundles(
    explicit_required: &[String],
    proof_bundles: &[TheoremPackDeclaration],
    statements: &[Statement],
) -> Vec<String> {
    if !explicit_required.is_empty() {
        return Vec::new();
    }
    if proof_bundles.is_empty() {
        return Vec::new();
    }
    let _ = statements;
    Vec::new()
}
