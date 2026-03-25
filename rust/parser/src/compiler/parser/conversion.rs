//! Protocol conversion and call inlining.
//!
//! This module converts the intermediate Statement representation
//! to the final Protocol AST, including desugaring of high-level constructs
//! and inlining of protocol calls.

use crate::ast::{
    Annotations, AuthorityExpr, Branch, CaseBranch, CasePattern, ChoiceGuard, Condition,
    MessageType, NonEmptyVec, Protocol, Role,
};
use quote::format_ident;

use super::types::{AuthorityExprSpec, CaseBranchSpec, ChoiceGuardSpec, Statement};

#[path = "conversion_inline_calls.rs"]
mod inline_calls;
pub(crate) use inline_calls::inline_calls;

fn convert_authority_expr(expr: &AuthorityExprSpec) -> AuthorityExpr {
    match expr {
        AuthorityExprSpec::Var(name) => AuthorityExpr::Var(name.clone()),
        AuthorityExprSpec::Check {
            effect,
            operation,
            args,
        } => AuthorityExpr::Check {
            effect: effect.clone(),
            operation: operation.clone(),
            args: args.clone(),
        },
        AuthorityExprSpec::Observe {
            effect,
            operation,
            args,
        } => AuthorityExpr::Observe {
            effect: effect.clone(),
            operation: operation.clone(),
            args: args.clone(),
        },
        AuthorityExprSpec::Transfer { subject, from, to } => AuthorityExpr::Transfer {
            subject: subject.clone(),
            from: from.clone(),
            to: to.clone(),
        },
        AuthorityExprSpec::Constructor { name, arg } => AuthorityExpr::Constructor {
            name: name.clone(),
            arg: arg.clone(),
        },
        AuthorityExprSpec::Call { name, args } => AuthorityExpr::Call {
            name: name.clone(),
            args: args.clone(),
        },
    }
}

fn convert_choice_guard(guard: &ChoiceGuardSpec) -> ChoiceGuard {
    match guard {
        ChoiceGuardSpec::Predicate(tokens) => ChoiceGuard::Predicate(tokens.clone()),
        ChoiceGuardSpec::Evidence {
            effect,
            operation,
            args,
            binding,
        } => ChoiceGuard::Evidence {
            effect: effect.clone(),
            operation: operation.clone(),
            args: args.clone(),
            binding: binding.clone(),
        },
    }
}

fn convert_case_branch(branch: &CaseBranchSpec, roles: &[Role]) -> CaseBranch {
    CaseBranch {
        pattern: CasePattern {
            constructor: branch.pattern.constructor.clone(),
            binders: branch.pattern.binders.clone(),
        },
        protocol: convert_statements_to_protocol(&branch.statements, roles),
    }
}

fn binding_is_linear(expr: &AuthorityExprSpec) -> bool {
    matches!(expr, AuthorityExprSpec::Transfer { .. })
}

/// Convert statements to protocol AST.
#[allow(clippy::too_many_lines)]
// RECURSION_SAFE: recursion consumes finite nested statement blocks.
pub(crate) fn convert_statements_to_protocol(statements: &[Statement], roles: &[Role]) -> Protocol {
    if statements.is_empty() {
        return Protocol::End;
    }

    let mut current = Protocol::End;

    // Build protocol from back to front
    for statement in statements.iter().rev() {
        current = match statement {
            Statement::Begin {
                operation,
                args,
                progress,
            } => Protocol::Begin {
                operation: operation.clone(),
                args: args.clone(),
                progress: progress.clone(),
                continuation: Box::new(current),
            },
            Statement::Await { operation } => Protocol::Await {
                operation: operation.clone(),
                continuation: Box::new(current),
            },
            Statement::Resolve { operation, outcome } => Protocol::Resolve {
                operation: operation.clone(),
                outcome: outcome.clone(),
                continuation: Box::new(current),
            },
            Statement::Invalidate { operation } => Protocol::Invalidate {
                operation: operation.clone(),
                continuation: Box::new(current),
            },
            Statement::Let {
                name,
                mode,
                expr,
                body,
            } => {
                let continuation = if let Some(body) = body {
                    convert_statements_to_protocol(body, roles)
                } else {
                    current
                };
                Protocol::Let {
                    name: name.clone(),
                    mode: *mode,
                    expr: convert_authority_expr(expr),
                    linear: binding_is_linear(expr),
                    continuation: Box::new(continuation),
                }
            }
            Statement::Case { expr, branches } => {
                let branch_vec: Vec<_> = branches
                    .iter()
                    .map(|branch| convert_case_branch(branch, roles))
                    .collect();
                if let Ok(branches) = NonEmptyVec::new(branch_vec) {
                    Protocol::Case {
                        expr: convert_authority_expr(expr),
                        branches,
                    }
                } else {
                    current
                }
            }
            Statement::Timeout {
                role,
                duration_ms,
                body,
                on_timeout,
                on_cancel,
            } => Protocol::Timeout {
                role: role.clone(),
                duration_ms: *duration_ms,
                body: Box::new(convert_statements_to_protocol(body, roles)),
                on_timeout: Box::new(convert_statements_to_protocol(on_timeout, roles)),
                on_cancel: on_cancel
                    .as_ref()
                    .map(|branch| Box::new(convert_statements_to_protocol(branch, roles))),
            },
            Statement::Send {
                from,
                to,
                message,
                annotations,
                from_annotations,
                to_annotations,
            } => Protocol::Send {
                from: from.clone(),
                to: to.clone(),
                message: MessageType {
                    name: message.name.clone(),
                    type_annotation: message.type_annotation.clone(),
                    payload: message.payload.clone(),
                },
                continuation: Box::new(current),
                annotations: Annotations::from_dsl_map(annotations),
                from_annotations: Annotations::from_dsl_map(from_annotations),
                to_annotations: Annotations::from_dsl_map(to_annotations),
            },
            Statement::Broadcast {
                from,
                message,
                annotations,
                from_annotations,
            } => {
                // Resolve to all roles except the sender
                let to_all = roles
                    .iter()
                    .filter(|r| r.name() != from.name())
                    .cloned()
                    .collect();
                if let Ok(to_all) = NonEmptyVec::new(to_all) {
                    Protocol::Broadcast {
                        from: from.clone(),
                        to_all,
                        message: MessageType {
                            name: message.name.clone(),
                            type_annotation: message.type_annotation.clone(),
                            payload: message.payload.clone(),
                        },
                        continuation: Box::new(current),
                        annotations: Annotations::from_dsl_map(annotations),
                        from_annotations: Annotations::from_dsl_map(from_annotations),
                    }
                } else {
                    // No non-sender recipients: treat as no-op and preserve continuation.
                    current
                }
            }
            Statement::Choice {
                role,
                branches,
                annotations,
            } => {
                let branch_vec: Vec<_> = branches
                    .iter()
                    .map(|b| Branch {
                        label: b.label.clone(),
                        guard: b.guard.as_ref().map(convert_choice_guard),
                        protocol: convert_statements_to_protocol(&b.statements, roles),
                    })
                    .collect();
                if let Ok(branches) = NonEmptyVec::new(branch_vec) {
                    Protocol::Choice {
                        role: role.clone(),
                        branches,
                        annotations: Annotations::from_dsl_map(annotations),
                    }
                } else {
                    current
                }
            }
            // RoleDecides desugars to choice+rec pattern (Option B: fused with first message)
            //   loop decide by Client { Client -> Server: Request; ... }
            // becomes:
            //   rec RoleDecidesLoop {
            //       choice Client at {
            //           Request { Client -> Server: Request; ...; continue RoleDecidesLoop }
            //           Done { Client -> Server: Done }
            //       }
            //   }
            Statement::Loop {
                condition: Some(Condition::RoleDecides(deciding_role)),
                body,
            } => {
                // Check if first statement is a Send from the deciding role
                if let Some(Statement::Send {
                    from,
                    to,
                    message,
                    annotations: send_annotations,
                    from_annotations,
                    to_annotations,
                }) = body.first()
                {
                    if from == deciding_role {
                        let rec_label = format_ident!("RoleDecidesLoop");
                        let remaining_body: Vec<_> = body.iter().skip(1).cloned().collect();

                        // Build continue branch: remaining body + continue
                        let mut continue_body = remaining_body;
                        continue_body.push(Statement::Continue {
                            label: rec_label.clone(),
                        });
                        let continue_protocol =
                            convert_statements_to_protocol(&continue_body, roles);

                        // The continue branch includes the first send
                        let continue_branch_protocol = Protocol::Send {
                            from: from.clone(),
                            to: to.clone(),
                            message: MessageType {
                                name: message.name.clone(),
                                type_annotation: message.type_annotation.clone(),
                                payload: message.payload.clone(),
                            },
                            continuation: Box::new(continue_protocol),
                            annotations: Annotations::from_dsl_map(send_annotations),
                            from_annotations: Annotations::from_dsl_map(from_annotations),
                            to_annotations: Annotations::from_dsl_map(to_annotations),
                        };

                        let continue_branch = Branch {
                            label: message.name.clone(),
                            guard: None,
                            protocol: continue_branch_protocol,
                        };

                        // Build done branch: deciding role sends Done, then continue with
                        // whatever comes after the loop (stored in `current`)
                        let done_branch_protocol = Protocol::Send {
                            from: from.clone(),
                            to: to.clone(),
                            message: MessageType {
                                name: format_ident!("Done"),
                                type_annotation: None,
                                payload: None,
                            },
                            continuation: Box::new(current),
                            annotations: Annotations::new(),
                            from_annotations: Annotations::new(),
                            to_annotations: Annotations::new(),
                        };

                        let done_branch = Branch {
                            label: format_ident!("Done"),
                            guard: None,
                            protocol: done_branch_protocol,
                        };

                        // Build the choice the at deciding role
                        let choice = Protocol::Choice {
                            role: deciding_role.clone(),
                            branches: NonEmptyVec::from_head_tail(
                                continue_branch,
                                vec![done_branch],
                            ),
                            annotations: Annotations::new(),
                        };

                        // Wrap in recursion
                        Protocol::Rec {
                            label: rec_label,
                            body: Box::new(choice),
                        }
                    } else {
                        // First statement is a Send but not from deciding role - keep as Loop
                        Protocol::Loop {
                            condition: Some(Condition::RoleDecides(deciding_role.clone())),
                            body: Box::new(convert_statements_to_protocol(body, roles)),
                        }
                    }
                } else {
                    // First statement is not a Send - keep as Loop (runner will produce error)
                    Protocol::Loop {
                        condition: Some(Condition::RoleDecides(deciding_role.clone())),
                        body: Box::new(convert_statements_to_protocol(body, roles)),
                    }
                }
            }
            Statement::Loop { condition, body } => Protocol::Loop {
                condition: condition.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Parallel { branches } => {
                let protocols_vec: Vec<_> = branches
                    .iter()
                    .map(|b| convert_statements_to_protocol(b, roles))
                    .collect();
                if let Ok(protocols) = NonEmptyVec::new(protocols_vec) {
                    Protocol::Parallel { protocols }
                } else {
                    current
                }
            }
            Statement::Rec { label, body } => Protocol::Rec {
                label: label.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Continue { label } => Protocol::Var(label.clone()),
            Statement::Call { .. } => current,
            Statement::Publish { event, arg } => Protocol::Publish {
                event: event.clone(),
                arg: arg.clone(),
                continuation: Box::new(current),
            },
            Statement::PublishAuthority {
                witness,
                publication_name,
            } => Protocol::PublishAuthority {
                witness: witness.clone(),
                publication_name: publication_name.clone(),
                continuation: Box::new(current),
            },
            Statement::Materialize { proof, publication } => Protocol::Materialize {
                proof: proof.clone(),
                publication: publication.clone(),
                continuation: Box::new(current),
            },
            Statement::Handoff {
                operation,
                target,
                receipt,
            } => Protocol::Handoff {
                operation: operation.clone(),
                target: target.clone(),
                receipt: receipt.clone(),
                continuation: Box::new(current),
            },
            Statement::DependentWork {
                name,
                arg,
                required_for,
            } => Protocol::DependentWork {
                name: name.clone(),
                arg: arg.clone(),
                required_for: required_for.clone(),
                continuation: Box::new(current),
            },
        };
    }

    current
}
