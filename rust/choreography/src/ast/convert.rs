//! Conversion utilities between DSL AST types and theory types.
//!
//! This module provides bidirectional conversion between choreography DSL types
//! (Protocol, LocalType) and the formal theory types (GlobalType, LocalTypeR)
//! from `rumpsteak-types`.
//!
//! ## Supported Conversions
//!
//! - `Protocol → GlobalType`: For protocols using the common subset (Send, Choice, Rec, Var, End)
//! - `LocalType → LocalTypeR`: For comparison of projection results
//!
//! ## Unsupported DSL Features
//!
//! The following DSL features cannot be converted to theory types:
//! - `Broadcast`: Use `desugar_broadcast` first to convert to nested Sends
//! - `Loop`: Use `desugar_loop` first to convert to Rec/Var
//! - `Parallel`: No theory equivalent
//! - `Extension`: No theory equivalent
//! - `LocalChoice`: DSL-only feature for local decisions

use super::{Branch, Choreography, LocalType, MessageType, Protocol};
use rumpsteak_types::{GlobalType as GlobalTypeCore, Label, LocalTypeR, PayloadSort};
use thiserror::Error;

/// Errors that can occur during conversion.
#[derive(Debug, Clone, Error)]
pub enum ConversionError {
    /// Protocol contains unsupported DSL feature
    #[error("unsupported DSL feature: {feature}. {hint}")]
    UnsupportedFeature { feature: String, hint: String },

    /// Empty choice branches
    #[error("choice has no branches")]
    EmptyChoice,

    /// Invalid choice structure (branches don't start with Send from decider)
    #[error("invalid choice: branch '{label}' does not start with Send from decider")]
    InvalidChoice { label: String },

    /// Inconsistent choice receivers
    #[error("choice has inconsistent receivers: expected all branches to send to {expected}, but branch '{label}' sends to {actual}")]
    InconsistentReceivers {
        expected: String,
        actual: String,
        label: String,
    },
}

/// Result type for conversion operations.
pub type ConversionResult<T> = Result<T, ConversionError>;

// ============================================================================
// Protocol → GlobalType conversion
// ============================================================================

/// Convert a Choreography to a GlobalType (theory type).
///
/// This converts the common subset of protocols that are expressible in both
/// the DSL and the formal theory.
///
/// # Errors
///
/// Returns an error if the protocol uses DSL-only features.
pub fn choreography_to_global(choreography: &Choreography) -> ConversionResult<GlobalTypeCore> {
    protocol_to_global(&choreography.protocol)
}

/// Convert a Protocol to a GlobalType (theory type).
///
/// # Supported Protocol Variants
///
/// - `Send`: Converts to `GlobalType::Comm` with single branch
/// - `Choice`: Converts to `GlobalType::Comm` with multiple branches
/// - `Rec`: Converts to `GlobalType::Mu`
/// - `Var`: Converts to `GlobalType::Var`
/// - `End`: Converts to `GlobalType::End`
///
/// # Errors
///
/// Returns `UnsupportedFeature` for: Broadcast, Loop, Parallel, Extension
pub fn protocol_to_global(protocol: &Protocol) -> ConversionResult<GlobalTypeCore> {
    match protocol {
        Protocol::End => Ok(GlobalTypeCore::End),

        Protocol::Var(ident) => Ok(GlobalTypeCore::var(ident.to_string())),

        Protocol::Rec { label, body } => {
            let body_global = protocol_to_global(body)?;
            Ok(GlobalTypeCore::mu(label.to_string(), body_global))
        }

        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            let cont_global = protocol_to_global(continuation)?;
            let label = message_to_label(message);
            Ok(GlobalTypeCore::send(
                from.name.to_string(),
                to.name.to_string(),
                label,
                cont_global,
            ))
        }

        Protocol::Choice {
            role: decider,
            branches,
            ..
        } => {
            if branches.is_empty() {
                return Err(ConversionError::EmptyChoice);
            }

            // Extract receiver from first branch (all branches must have same receiver)
            let first_receiver = extract_receiver(&branches[0], decider)?;

            // Convert all branches
            let mut global_branches = Vec::with_capacity(branches.len());
            for branch in branches {
                let (label, cont) = convert_choice_branch(branch, decider, &first_receiver)?;
                global_branches.push((label, cont));
            }

            Ok(GlobalTypeCore::comm(
                decider.name.to_string(),
                first_receiver,
                global_branches,
            ))
        }

        Protocol::Broadcast { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Broadcast".to_string(),
            hint: "Desugar to nested Sends using desugar_broadcast() first".to_string(),
        }),

        Protocol::Loop { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Loop".to_string(),
            hint: "Convert to Rec/Var using desugar_loop() first".to_string(),
        }),

        Protocol::Parallel { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Parallel".to_string(),
            hint: "Parallel composition has no theory equivalent".to_string(),
        }),

        Protocol::Extension { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Extension".to_string(),
            hint: "Protocol extensions have no theory equivalent".to_string(),
        }),
    }
}

/// Extract the receiver from a choice branch's initial Send.
fn extract_receiver(branch: &Branch, decider: &super::Role) -> ConversionResult<String> {
    match &branch.protocol {
        Protocol::Send { from, to, .. } => {
            if from.name != decider.name {
                return Err(ConversionError::InvalidChoice {
                    label: branch.label.to_string(),
                });
            }
            Ok(to.name.to_string())
        }
        _ => Err(ConversionError::InvalidChoice {
            label: branch.label.to_string(),
        }),
    }
}

/// Convert a choice branch to a (Label, GlobalType) pair.
fn convert_choice_branch(
    branch: &Branch,
    decider: &super::Role,
    expected_receiver: &str,
) -> ConversionResult<(Label, GlobalTypeCore)> {
    match &branch.protocol {
        Protocol::Send {
            from,
            to,
            message,
            continuation,
            ..
        } => {
            if from.name != decider.name {
                return Err(ConversionError::InvalidChoice {
                    label: branch.label.to_string(),
                });
            }
            if to.name.to_string() != expected_receiver {
                return Err(ConversionError::InconsistentReceivers {
                    expected: expected_receiver.to_string(),
                    actual: to.name.to_string(),
                    label: branch.label.to_string(),
                });
            }

            let cont_global = protocol_to_global(continuation)?;
            let label = message_to_label(message);
            Ok((label, cont_global))
        }
        _ => Err(ConversionError::InvalidChoice {
            label: branch.label.to_string(),
        }),
    }
}

/// Convert a MessageType to a Label.
fn message_to_label(message: &MessageType) -> Label {
    // Use the message name as the label name
    // If there's a type annotation, we could map it to PayloadSort
    let name = message.name.to_string();

    // For now, use Unit sort. Could be extended to parse type annotations.
    Label::with_sort(name, PayloadSort::Unit)
}

// ============================================================================
// LocalType → LocalTypeR conversion
// ============================================================================

/// Convert a LocalType (DSL) to a LocalTypeR (theory type).
///
/// # Supported LocalType Variants
///
/// - `Send`: Converts to `LocalTypeR::Send`
/// - `Receive`: Converts to `LocalTypeR::Recv`
/// - `Select`: Converts to `LocalTypeR::Send` (internal choice)
/// - `Branch`: Converts to `LocalTypeR::Recv` (external choice)
/// - `Mu`/`Var`: Convert directly
/// - `End`: Converts to `LocalTypeR::End`
///
/// # Errors
///
/// Returns error for: `LocalChoice`, `Loop` (DSL-only features)
pub fn local_to_local_r(local: &LocalType) -> ConversionResult<LocalTypeR> {
    match local {
        LocalType::End => Ok(LocalTypeR::End),

        LocalType::Var(ident) => Ok(LocalTypeR::Var(ident.to_string())),

        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let cont_r = local_to_local_r(continuation)?;
            let label = message_to_label(message);
            Ok(LocalTypeR::send(to.name.to_string(), label, cont_r))
        }

        LocalType::Receive {
            from,
            message,
            continuation,
        } => {
            let cont_r = local_to_local_r(continuation)?;
            let label = message_to_label(message);
            Ok(LocalTypeR::recv(from.name.to_string(), label, cont_r))
        }

        LocalType::Select { to, branches } => {
            let mut r_branches = Vec::with_capacity(branches.len());
            for (ident, cont) in branches {
                // Flatten nested Send that duplicates the choice label
                // DSL produces: Select { Accept -> Send(Accept, End) }
                // Theory expects: Send { (Accept, End) }
                let cont_r = match cont {
                    // If continuation is a Send to same partner with matching label, flatten it
                    LocalType::Send {
                        to: send_to,
                        message,
                        continuation,
                    } if send_to.name == to.name && message.name.to_string() == ident.to_string() => {
                        local_to_local_r(continuation)?
                    }
                    _ => local_to_local_r(cont)?,
                };
                let label = Label::new(ident.to_string());
                r_branches.push((label, cont_r));
            }
            Ok(LocalTypeR::Send {
                partner: to.name.to_string(),
                branches: r_branches,
            })
        }

        LocalType::Branch { from, branches } => {
            let mut r_branches = Vec::with_capacity(branches.len());
            for (ident, cont) in branches {
                // Flatten nested Receive that duplicates the choice label
                // DSL produces: Branch { Accept -> Recv(Accept, End) }
                // Theory expects: Recv { (Accept, End) }
                let cont_r = match cont {
                    // If continuation is a Receive from same partner with matching label, flatten it
                    LocalType::Receive {
                        from: recv_from,
                        message,
                        continuation,
                    } if recv_from.name == from.name
                        && message.name.to_string() == ident.to_string() =>
                    {
                        local_to_local_r(continuation)?
                    }
                    _ => local_to_local_r(cont)?,
                };
                let label = Label::new(ident.to_string());
                r_branches.push((label, cont_r));
            }
            Ok(LocalTypeR::Recv {
                partner: from.name.to_string(),
                branches: r_branches,
            })
        }

        LocalType::Rec { label, body } => {
            let body_r = local_to_local_r(body)?;
            Ok(LocalTypeR::mu(label.to_string(), body_r))
        }

        LocalType::LocalChoice { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "LocalChoice".to_string(),
            hint: "LocalChoice (local decisions without communication) has no theory equivalent"
                .to_string(),
        }),

        LocalType::Loop { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Loop".to_string(),
            hint: "Loop should be converted to Rec/Var before conversion".to_string(),
        }),

        LocalType::Timeout { .. } => Err(ConversionError::UnsupportedFeature {
            feature: "Timeout".to_string(),
            hint: "Timeout is a DSL extension with no theory equivalent".to_string(),
        }),
    }
}

// ============================================================================
// Comparison utilities
// ============================================================================

/// Compare two LocalTypeR values for structural equivalence.
///
/// This compares the structure, ignoring payload sorts (which are often Unit
/// in DSL-generated types).
pub fn local_types_equivalent(lt1: &LocalTypeR, lt2: &LocalTypeR) -> bool {
    match (lt1, lt2) {
        (LocalTypeR::End, LocalTypeR::End) => true,

        (LocalTypeR::Var(v1), LocalTypeR::Var(v2)) => v1 == v2,

        (LocalTypeR::Mu { var: v1, body: b1 }, LocalTypeR::Mu { var: v2, body: b2 }) => {
            // For alpha-equivalence, we'd need more sophisticated comparison
            // For now, require same variable names
            v1 == v2 && local_types_equivalent(b1, b2)
        }

        (
            LocalTypeR::Send {
                partner: p1,
                branches: bs1,
            },
            LocalTypeR::Send {
                partner: p2,
                branches: bs2,
            },
        ) => {
            p1 == p2
                && bs1.len() == bs2.len()
                && bs1.iter().zip(bs2.iter()).all(|((l1, c1), (l2, c2))| {
                    l1.name == l2.name && local_types_equivalent(c1, c2)
                })
        }

        (
            LocalTypeR::Recv {
                partner: p1,
                branches: bs1,
            },
            LocalTypeR::Recv {
                partner: p2,
                branches: bs2,
            },
        ) => {
            p1 == p2
                && bs1.len() == bs2.len()
                && bs1.iter().zip(bs2.iter()).all(|((l1, c1), (l2, c2))| {
                    l1.name == l2.name && local_types_equivalent(c1, c2)
                })
        }

        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Ident;
    use proc_macro2::Span;
    use std::collections::HashMap;

    fn ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn role(name: &str) -> super::super::Role {
        super::super::Role {
            name: ident(name),
            param: None,
            index: None,
            array_size: None,
        }
    }

    fn message(name: &str) -> MessageType {
        MessageType {
            name: ident(name),
            type_annotation: None,
            payload: None,
        }
    }

    #[test]
    fn test_simple_send_conversion() {
        // A -> B: msg. end
        let protocol = Protocol::Send {
            from: role("A"),
            to: role("B"),
            message: message("msg"),
            continuation: Box::new(Protocol::End),
            annotations: HashMap::new(),
            from_annotations: HashMap::new(),
            to_annotations: HashMap::new(),
        };

        let global = protocol_to_global(&protocol).unwrap();
        assert!(matches!(global, GlobalTypeCore::Comm { sender, receiver, .. }
            if sender == "A" && receiver == "B"));
    }

    #[test]
    fn test_recursive_conversion() {
        // rec Loop { A -> B: msg. Loop }
        let protocol = Protocol::Rec {
            label: ident("Loop"),
            body: Box::new(Protocol::Send {
                from: role("A"),
                to: role("B"),
                message: message("msg"),
                continuation: Box::new(Protocol::Var(ident("Loop"))),
                annotations: HashMap::new(),
                from_annotations: HashMap::new(),
                to_annotations: HashMap::new(),
            }),
        };

        let global = protocol_to_global(&protocol).unwrap();
        assert!(matches!(global, GlobalTypeCore::Mu { var, .. } if var == "Loop"));
    }

    #[test]
    fn test_broadcast_unsupported() {
        let protocol = Protocol::Broadcast {
            from: role("A"),
            to_all: vec![role("B"), role("C")],
            message: message("msg"),
            continuation: Box::new(Protocol::End),
            annotations: HashMap::new(),
            from_annotations: HashMap::new(),
        };

        let result = protocol_to_global(&protocol);
        assert!(matches!(result, Err(ConversionError::UnsupportedFeature { feature, .. }) if feature == "Broadcast"));
    }

    #[test]
    fn test_local_type_conversion() {
        // Send to B: msg. End
        let local = LocalType::Send {
            to: role("B"),
            message: message("msg"),
            continuation: Box::new(LocalType::End),
        };

        let local_r = local_to_local_r(&local).unwrap();
        assert!(matches!(local_r, LocalTypeR::Send { partner, .. } if partner == "B"));
    }

    #[test]
    fn test_equivalence_check() {
        let lt1 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let lt2 = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let lt3 = LocalTypeR::send("C", Label::new("msg"), LocalTypeR::End);

        assert!(local_types_equivalent(&lt1, &lt2));
        assert!(!local_types_equivalent(&lt1, &lt3));
    }
}
