use super::super::error::{ErrorSpan, ParseError};
use super::super::types::{ChoiceBranch, Statement};
use std::collections::HashMap;

/// Inline all Call statements by replacing them with their definitions.
pub(crate) fn inline_calls(
    statements: &[Statement],
    protocol_defs: &HashMap<String, Vec<Statement>>,
    input: &str,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut result = Vec::new();

    for statement in statements {
        match statement {
            Statement::Call { name } => {
                let key = name.to_string();
                let called =
                    protocol_defs
                        .get(&key)
                        .ok_or_else(|| ParseError::UndefinedProtocol {
                            protocol: key.clone(),
                            span: ErrorSpan::from_line_col(1, 1, input),
                        })?;
                result.extend(inline_calls(called, protocol_defs, input)?);
            }
            Statement::Choice { role, branches, .. } => {
                let mut new_branches = Vec::new();
                for b in branches {
                    new_branches.push(ChoiceBranch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        statements: inline_calls(&b.statements, protocol_defs, input)?,
                    });
                }
                result.push(Statement::Choice {
                    role: role.clone(),
                    branches: new_branches,
                    annotations: HashMap::new(),
                });
            }
            Statement::TimedChoice {
                role,
                duration_ms,
                branches,
            } => {
                let mut new_branches = Vec::new();
                for b in branches {
                    new_branches.push(ChoiceBranch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        statements: inline_calls(&b.statements, protocol_defs, input)?,
                    });
                }
                result.push(Statement::TimedChoice {
                    role: role.clone(),
                    duration_ms: *duration_ms,
                    branches: new_branches,
                });
            }
            Statement::Heartbeat {
                sender,
                receiver,
                interval_ms,
                on_missing_count,
                on_missing_body,
                body,
            } => {
                result.push(Statement::Heartbeat {
                    sender: sender.clone(),
                    receiver: receiver.clone(),
                    interval_ms: *interval_ms,
                    on_missing_count: *on_missing_count,
                    on_missing_body: inline_calls(on_missing_body, protocol_defs, input)?,
                    body: inline_calls(body, protocol_defs, input)?,
                });
            }
            Statement::Loop { condition, body } => {
                result.push(Statement::Loop {
                    condition: condition.clone(),
                    body: inline_calls(body, protocol_defs, input)?,
                });
            }
            Statement::Parallel { branches } => {
                let mut new_branches = Vec::new();
                for b in branches {
                    new_branches.push(inline_calls(b, protocol_defs, input)?);
                }
                result.push(Statement::Parallel {
                    branches: new_branches,
                });
            }
            Statement::Branch { body, span } => {
                result.push(Statement::Branch {
                    body: inline_calls(body, protocol_defs, input)?,
                    span: span.clone(),
                });
            }
            Statement::Rec { label, body } => {
                result.push(Statement::Rec {
                    label: label.clone(),
                    body: inline_calls(body, protocol_defs, input)?,
                });
            }
            Statement::Handshake {
                initiator,
                responder,
                label,
            } => {
                result.push(Statement::Handshake {
                    initiator: initiator.clone(),
                    responder: responder.clone(),
                    label: label.clone(),
                });
            }
            Statement::QuorumCollect {
                source,
                destination,
                min_responses,
                message,
            } => {
                result.push(Statement::QuorumCollect {
                    source: source.clone(),
                    destination: destination.clone(),
                    min_responses: *min_responses,
                    message: message.clone(),
                });
            }
            Statement::VmCoreOp { op } => {
                result.push(Statement::VmCoreOp { op: op.clone() });
            }
            _ => {
                result.push(statement.clone());
            }
        }
    }

    Ok(result)
}
