use super::*;
use super::types::VmCoreOp;

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
            Statement::Choice { branches, .. } | Statement::TimedChoice { branches, .. } => {
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
            Statement::Branch { body, .. } => {
                let out = validate_linear_block(body, &live_assets, input)?;
                validate_preserved_linear_assets(
                    input,
                    &live_assets,
                    &out,
                    "branch blocks must preserve linear assets",
                )?;
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

// RECURSION_SAFE: recursion consumes finite nested statement blocks.
fn collect_vm_required_capabilities(statements: &[Statement], out: &mut HashSet<String>) {
    for statement in statements {
        match statement {
            Statement::VmCoreOp { op } => {
                out.insert(op.required_capability().to_string());
            }
            Statement::Choice { branches, .. } | Statement::TimedChoice { branches, .. } => {
                for branch in branches {
                    collect_vm_required_capabilities(&branch.statements, out);
                }
            }
            Statement::Loop { body, .. }
            | Statement::Rec { body, .. }
            | Statement::Branch { body, .. } => {
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
