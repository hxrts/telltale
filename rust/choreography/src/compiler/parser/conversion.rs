//! Protocol conversion and call inlining.
//!
//! This module converts the intermediate Statement representation
//! to the final Protocol AST, including desugaring of high-level constructs
//! and inlining of protocol calls.

use crate::ast::{
    Annotations, Branch, Condition, LocalType, MessageType, NonEmptyVec, Protocol,
    ProtocolAnnotation, Role,
};
use crate::compiler::projection::ProjectionError;
use crate::extensions::{
    CodegenContext, ExtensionValidationError, ProjectionContext, ProtocolExtension,
};
use quote::format_ident;
use std::any::{Any, TypeId};

use super::types::{Statement, VmCoreOp};

#[path = "conversion_inline_calls.rs"]
mod inline_calls;
pub(crate) use inline_calls::inline_calls;

#[derive(Debug, Clone)]
struct VmCoreOpExtension {
    op_name: String,
}

impl VmCoreOpExtension {
    fn new(op_name: impl Into<String>) -> Self {
        Self {
            op_name: op_name.into(),
        }
    }
}

impl ProtocolExtension for VmCoreOpExtension {
    fn type_name(&self) -> &'static str {
        "vm_core_op"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        false
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::End)
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let op = &self.op_name;
        quote::quote! {
            {
                let _vm_core_op: &str = #op;
                // Intentional discard: suppress unused warning in generated code.
                let _ = _vm_core_op;
            }
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

#[derive(Debug, Clone)]
struct DslCombinatorExtension {
    kind: String,
}

impl DslCombinatorExtension {
    fn new(kind: impl Into<String>) -> Self {
        Self { kind: kind.into() }
    }
}

impl ProtocolExtension for DslCombinatorExtension {
    fn type_name(&self) -> &'static str {
        "dsl_combinator"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        false
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::End)
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let kind = &self.kind;
        quote::quote! {
            {
                let _dsl_combinator_kind: &str = #kind;
                // Intentional discard: suppress unused warning in generated code.
                let _ = _dsl_combinator_kind;
            }
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

fn vm_op_operands(op: &VmCoreOp) -> String {
    match op {
        VmCoreOp::Acquire { layer, dst } => format!("layer={layer},dst={dst}"),
        VmCoreOp::Release { layer, evidence } => {
            format!("layer={layer},evidence={evidence}")
        }
        VmCoreOp::Fork { ghost } => format!("ghost={ghost}"),
        VmCoreOp::Join => "none".to_string(),
        VmCoreOp::Abort => "none".to_string(),
        VmCoreOp::Transfer {
            endpoint,
            target,
            bundle,
        } => format!(
            "endpoint={endpoint},target={target},bundle={}",
            bundle.as_deref().unwrap_or("none")
        ),
        VmCoreOp::Tag { fact, dst } => format!("fact={fact},dst={dst}"),
        VmCoreOp::Check {
            knowledge,
            target_role,
            dst,
        } => format!("knowledge={knowledge},target_role={target_role},dst={dst}"),
    }
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
                annotations: Annotations::from_map(annotations),
                from_annotations: Annotations::from_map(from_annotations),
                to_annotations: Annotations::from_map(to_annotations),
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
                        annotations: Annotations::from_map(annotations),
                        from_annotations: Annotations::from_map(from_annotations),
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
                        guard: b.guard.clone(),
                        protocol: convert_statements_to_protocol(&b.statements, roles),
                    })
                    .collect();
                if let Ok(branches) = NonEmptyVec::new(branch_vec) {
                    Protocol::Choice {
                        role: role.clone(),
                        branches,
                        annotations: Annotations::from_map(annotations),
                    }
                } else {
                    current
                }
            }
            // TimedChoice desugars to standard Choice with typed annotation.
            // This preserves Lean verification (Choice is core MPST) while carrying
            // timeout info for code generation via typed ProtocolAnnotation.
            Statement::TimedChoice {
                role,
                duration_ms,
                branches,
            } => {
                // Use typed annotation instead of string key-value pair
                let annotations =
                    Annotations::single(ProtocolAnnotation::timed_choice_ms(*duration_ms));

                let branch_vec: Vec<_> = branches
                    .iter()
                    .map(|b| Branch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        protocol: convert_statements_to_protocol(&b.statements, roles),
                    })
                    .collect();

                if let Ok(branches) = NonEmptyVec::new(branch_vec) {
                    Protocol::Choice {
                        role: role.clone(),
                        branches,
                        annotations,
                    }
                } else {
                    current
                }
            }
            // Heartbeat desugars to recursive choice with liveness detection:
            //   rec HeartbeatLoop {
            //       Sender -> Receiver: Heartbeat;
            //       choice at Receiver {
            //           Alive { body; continue HeartbeatLoop }
            //           Dead { on_missing_body }
            //       }
            //   }
            Statement::Heartbeat {
                sender,
                receiver,
                interval_ms,
                on_missing_count,
                on_missing_body,
                body,
            } => {
                let rec_label = format_ident!("HeartbeatLoop");

                // Heartbeat annotation carries runtime info (interval, on_missing_count)
                let heartbeat_annotation =
                    ProtocolAnnotation::heartbeat_ms(*interval_ms, *on_missing_count);
                let annotations = Annotations::single(heartbeat_annotation);

                // Build body with continue at the end
                let mut alive_body = body.clone();
                alive_body.push(Statement::Continue {
                    label: rec_label.clone(),
                });
                let alive_protocol = convert_statements_to_protocol(&alive_body, roles);

                // Build on_missing body (Dead branch)
                let dead_protocol = convert_statements_to_protocol(on_missing_body, roles);

                // Build the choice: Receiver decides Alive or Dead
                let alive_branch = Branch {
                    label: format_ident!("Alive"),
                    guard: None,
                    protocol: alive_protocol,
                };
                let dead_branch = Branch {
                    label: format_ident!("Dead"),
                    guard: None,
                    protocol: dead_protocol,
                };
                let choice = Protocol::Choice {
                    role: receiver.clone(),
                    branches: NonEmptyVec::from_head_tail(alive_branch, vec![dead_branch]),
                    annotations,
                };

                // Build the heartbeat send: Sender -> Receiver: Heartbeat
                let heartbeat_send = Protocol::Send {
                    from: sender.clone(),
                    to: receiver.clone(),
                    message: MessageType {
                        name: format_ident!("Heartbeat"),
                        type_annotation: None,
                        payload: None,
                    },
                    continuation: Box::new(choice),
                    annotations: Annotations::new(),
                    from_annotations: Annotations::new(),
                    to_annotations: Annotations::new(),
                };

                // Wrap in recursion
                Protocol::Rec {
                    label: rec_label,
                    body: Box::new(heartbeat_send),
                }
            }
            // RoleDecides desugars to choice+rec pattern (Option B: fused with first message)
            //   loop decide by Client { Client -> Server: Request; ... }
            // becomes:
            //   rec RoleDecidesLoop {
            //       choice at Client {
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
                            annotations: Annotations::from_map(send_annotations),
                            from_annotations: Annotations::from_map(from_annotations),
                            to_annotations: Annotations::from_map(to_annotations),
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

                        // Build the choice at the deciding role
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
            Statement::Handshake {
                initiator,
                responder,
                label,
            } => {
                let ack_label = format_ident!("{}Ack", label);
                let ack = Protocol::Send {
                    from: responder.clone(),
                    to: initiator.clone(),
                    message: MessageType {
                        name: ack_label,
                        type_annotation: None,
                        payload: None,
                    },
                    continuation: Box::new(current),
                    annotations: Annotations::new(),
                    from_annotations: Annotations::new(),
                    to_annotations: Annotations::new(),
                };
                Protocol::Send {
                    from: initiator.clone(),
                    to: responder.clone(),
                    message: MessageType {
                        name: label.clone(),
                        type_annotation: None,
                        payload: None,
                    },
                    continuation: Box::new(ack),
                    annotations: Annotations::new(),
                    from_annotations: Annotations::new(),
                    to_annotations: Annotations::new(),
                }
            }
            Statement::QuorumCollect {
                source,
                destination,
                min_responses,
                message,
            } => {
                let annotations = Annotations::from_vec(vec![
                    ProtocolAnnotation::custom("dsl_combinator", "quorum_collect"),
                    ProtocolAnnotation::custom("quorum_min", min_responses.to_string()),
                    ProtocolAnnotation::custom("quorum_source", source.name().to_string()),
                    ProtocolAnnotation::custom(
                        "quorum_destination",
                        destination.name().to_string(),
                    ),
                    ProtocolAnnotation::custom("quorum_message", message.name.to_string()),
                ]);
                Protocol::Extension {
                    extension: Box::new(DslCombinatorExtension::new("quorum_collect")),
                    continuation: Box::new(current),
                    annotations,
                }
            }
            Statement::VmCoreOp { op } => {
                let annotations = Annotations::from_vec(vec![
                    ProtocolAnnotation::custom("vm_core_op", op.op_name()),
                    ProtocolAnnotation::custom("required_capability", op.required_capability()),
                    ProtocolAnnotation::custom("vm_core_operands", vm_op_operands(op)),
                ]);
                Protocol::Extension {
                    extension: Box::new(VmCoreOpExtension::new(op.op_name())),
                    continuation: Box::new(current),
                    annotations,
                }
            }
        };
    }

    current
}
