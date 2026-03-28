// Protocol AST definitions

use super::annotation::Annotations;
use super::{MessageType, NonEmptyVec, ProgressAttachment, Role, ValidationError};
use proc_macro2::{Ident, TokenStream};

#[path = "protocol_validation.rs"]
mod validation;
use validation::{ensure_declared_role, validate_choice_branches};

fn annotation_has_key(annotation: &super::annotation::ProtocolAnnotation, key: &str) -> bool {
    annotation
        .dsl_entries()
        .iter()
        .any(|(entry_key, _)| entry_key == key)
}

fn annotation_has_value(
    annotation: &super::annotation::ProtocolAnnotation,
    key: &str,
    value: &str,
) -> bool {
    annotation
        .dsl_entries()
        .iter()
        .any(|(entry_key, entry_value)| entry_key == key && entry_value.eq_ignore_ascii_case(value))
}

/// Protocol specification using choreographic constructs
#[derive(Debug)]
pub enum Protocol {
    /// Begin one explicit semantic operation instance.
    Begin {
        operation: String,
        args: Vec<String>,
        progress: Option<ProgressAttachment>,
        continuation: Box<Protocol>,
    },

    /// Await one previously begun semantic operation instance.
    Await {
        operation: String,
        continuation: Box<Protocol>,
    },

    /// Resolve one previously begun semantic operation instance.
    Resolve {
        operation: String,
        outcome: CommitmentOutcome,
        continuation: Box<Protocol>,
    },

    /// Invalidate one previously begun semantic operation instance.
    Invalidate {
        operation: String,
        continuation: Box<Protocol>,
    },

    /// Message send: A -> B: Message
    Send {
        from: Role,
        to: Role,
        message: MessageType,
        continuation: Box<Protocol>,
        /// Statement-level annotations
        annotations: Annotations,
        /// From role annotations
        from_annotations: Annotations,
        /// To role annotations
        to_annotations: Annotations,
    },

    /// Broadcast: A -> *: Message
    Broadcast {
        from: Role,
        to_all: NonEmptyVec<Role>,
        message: MessageType,
        continuation: Box<Protocol>,
        /// Statement-level annotations
        annotations: Annotations,
        /// From role annotations
        from_annotations: Annotations,
    },

    /// Choice made by a role
    Choice {
        role: Role,
        branches: NonEmptyVec<Branch>,
        /// Statement-level annotations
        annotations: Annotations,
    },

    /// Local authority/evidence binding.
    Let {
        /// Bound variable name.
        name: String,
        /// Whether the binding is authoritative, observational, or plain.
        mode: AuthorityBindingMode,
        /// Bound expression.
        expr: AuthorityExpr,
        /// Whether the binding is linear/single-use.
        linear: bool,
        /// Continuation after the binding.
        continuation: Box<Protocol>,
    },

    /// Local authority/result match.
    Case {
        /// Scrutinee expression.
        expr: AuthorityExpr,
        /// Match branches.
        branches: NonEmptyVec<CaseBranch>,
    },

    /// Explicit timeout/cancel surface syntax prior to projection lowering.
    Timeout {
        /// Role that owns the timeout decision.
        role: Role,
        /// Timeout duration in milliseconds.
        duration_ms: u64,
        /// Main body before timeout fires.
        body: Box<Protocol>,
        /// Timeout branch.
        on_timeout: Box<Protocol>,
        /// Optional explicit cancellation branch.
        on_cancel: Option<Box<Protocol>>,
    },

    /// Loop construct
    Loop {
        condition: Option<Condition>,
        body: Box<Protocol>,
    },

    /// Parallel composition
    Parallel { protocols: NonEmptyVec<Protocol> },

    /// Recursive protocol with label
    Rec { label: Ident, body: Box<Protocol> },

    /// Reference to recursive label
    Var(Ident),

    /// Canonical semantic publication surface.
    Publish {
        event: String,
        arg: Option<String>,
        continuation: Box<Protocol>,
    },

    /// Canonical publication that lifts an authoritative witness into a named publication.
    PublishAuthority {
        witness: String,
        publication_name: String,
        continuation: Box<Protocol>,
    },

    /// Canonical materialization from one named publication.
    Materialize {
        proof: String,
        publication: String,
        continuation: Box<Protocol>,
    },

    /// Explicit semantic owner handoff.
    Handoff {
        operation: String,
        target: Role,
        receipt: String,
        continuation: Box<Protocol>,
    },

    /// Declared semantically required dependent work.
    DependentWork {
        name: String,
        arg: Option<String>,
        required_for: String,
        continuation: Box<Protocol>,
    },

    /// Protocol extension point for custom behaviors
    Extension {
        /// The extension implementation
        extension: Box<dyn crate::extensions::ProtocolExtension>,
        /// Continuation after this extension
        continuation: Box<Protocol>,
        /// Statement-level annotations
        annotations: Annotations,
    },

    /// Protocol termination
    End,
}

/// A branch in a choice
#[derive(Debug, Clone)]
pub struct Branch {
    pub label: Ident,
    pub guard: Option<ChoiceGuard>,
    pub protocol: Protocol,
}

/// Match branch in a `case/of` expression.
#[derive(Debug, Clone)]
pub struct CaseBranch {
    pub pattern: CasePattern,
    pub protocol: Protocol,
}

/// Pattern accepted by DSL `case/of`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CasePattern {
    pub constructor: String,
    pub binders: Vec<String>,
}

/// Explicit authority/observation mode for one local binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthorityBindingMode {
    Plain,
    Authoritative,
    Observe,
}

impl Clone for Protocol {
    fn clone(&self) -> Self {
        match self {
            Protocol::Begin {
                operation,
                args,
                progress,
                continuation,
            } => Protocol::Begin {
                operation: operation.clone(),
                args: args.clone(),
                progress: progress.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Await {
                operation,
                continuation,
            } => Protocol::Await {
                operation: operation.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Resolve {
                operation,
                outcome,
                continuation,
            } => Protocol::Resolve {
                operation: operation.clone(),
                outcome: outcome.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Invalidate {
                operation,
                continuation,
            } => Protocol::Invalidate {
                operation: operation.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                annotations,
                from_annotations,
                to_annotations,
            } => Protocol::Send {
                from: from.clone(),
                to: to.clone(),
                message: message.clone(),
                continuation: continuation.clone(),
                annotations: annotations.clone(),
                from_annotations: from_annotations.clone(),
                to_annotations: to_annotations.clone(),
            },
            Protocol::Broadcast {
                from,
                to_all,
                message,
                continuation,
                annotations,
                from_annotations,
            } => Protocol::Broadcast {
                from: from.clone(),
                to_all: to_all.clone(),
                message: message.clone(),
                continuation: continuation.clone(),
                annotations: annotations.clone(),
                from_annotations: from_annotations.clone(),
            },
            Protocol::Choice {
                role,
                branches,
                annotations,
            } => Protocol::Choice {
                role: role.clone(),
                branches: branches.clone(),
                annotations: annotations.clone(),
            },
            Protocol::Let {
                name,
                mode,
                expr,
                linear,
                continuation,
            } => Protocol::Let {
                name: name.clone(),
                mode: *mode,
                expr: expr.clone(),
                linear: *linear,
                continuation: continuation.clone(),
            },
            Protocol::Case { expr, branches } => Protocol::Case {
                expr: expr.clone(),
                branches: branches.clone(),
            },
            Protocol::Timeout {
                role,
                duration_ms,
                body,
                on_timeout,
                on_cancel,
            } => Protocol::Timeout {
                role: role.clone(),
                duration_ms: *duration_ms,
                body: body.clone(),
                on_timeout: on_timeout.clone(),
                on_cancel: on_cancel.clone(),
            },
            Protocol::Loop { condition, body } => Protocol::Loop {
                condition: condition.clone(),
                body: body.clone(),
            },
            Protocol::Parallel { protocols } => Protocol::Parallel {
                protocols: protocols.clone(),
            },
            Protocol::Rec { label, body } => Protocol::Rec {
                label: label.clone(),
                body: body.clone(),
            },
            Protocol::Var(label) => Protocol::Var(label.clone()),
            Protocol::Publish {
                event,
                arg,
                continuation,
            } => Protocol::Publish {
                event: event.clone(),
                arg: arg.clone(),
                continuation: continuation.clone(),
            },
            Protocol::PublishAuthority {
                witness,
                publication_name,
                continuation,
            } => Protocol::PublishAuthority {
                witness: witness.clone(),
                publication_name: publication_name.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Materialize {
                proof,
                publication,
                continuation,
            } => Protocol::Materialize {
                proof: proof.clone(),
                publication: publication.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Handoff {
                operation,
                target,
                receipt,
                continuation,
            } => Protocol::Handoff {
                operation: operation.clone(),
                target: target.clone(),
                receipt: receipt.clone(),
                continuation: continuation.clone(),
            },
            Protocol::DependentWork {
                name,
                arg,
                required_for,
                continuation,
            } => Protocol::DependentWork {
                name: name.clone(),
                arg: arg.clone(),
                required_for: required_for.clone(),
                continuation: continuation.clone(),
            },
            Protocol::Extension {
                extension,
                continuation,
                annotations,
            } => Protocol::Extension {
                extension: extension.clone(),
                continuation: continuation.clone(),
                annotations: annotations.clone(),
            },
            Protocol::End => Protocol::End,
        }
    }
}

/// Authority- or evidence-oriented expression surface syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuthorityExpr {
    Var(String),
    Check {
        effect: String,
        operation: String,
        args: Vec<String>,
    },
    Observe {
        effect: String,
        operation: String,
        args: Vec<String>,
    },
    Transfer {
        subject: String,
        from: String,
        to: String,
    },
    Constructor {
        name: String,
        arg: Option<String>,
    },
    Call {
        name: String,
        args: Vec<String>,
    },
}

/// Explicit outcome used to resolve a begun semantic operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommitmentOutcome {
    Success(Option<String>),
    Failure(Option<String>),
    Timeout(Option<String>),
    Cancelled,
}

/// Guard surface syntax attached to one choice branch.
#[derive(Debug, Clone)]
pub enum ChoiceGuard {
    Predicate(TokenStream),
    Evidence {
        effect: String,
        operation: String,
        args: Vec<String>,
        binding: String,
    },
}

/// Loop condition
#[derive(Debug, Clone)]
pub enum Condition {
    /// Loop while a role decides
    RoleDecides(Role),
    /// Fixed iteration count
    Count(usize),
    /// Custom condition
    Custom(TokenStream),
    /// Fuel-based bounding: maximum number of loop iterations
    Fuel(usize),
    /// Yield control after N communication steps
    YieldAfter(usize),
    /// Yield when a specific label/condition is encountered
    YieldWhen(String),
}

impl Protocol {
    #[must_use]
    pub fn mentions_role(&self, role: &Role) -> bool {
        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => continuation.mentions_role(role),
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                from.matches_family(role)
                    || to.matches_family(role)
                    || continuation.mentions_role(role)
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                from.matches_family(role)
                    || to_all.iter().any(|r| r.matches_family(role))
                    || continuation.mentions_role(role)
            }
            Protocol::Choice {
                role: r, branches, ..
            } => r.matches_family(role) || branches.iter().any(|b| b.protocol.mentions_role(role)),
            Protocol::Let { continuation, .. } => continuation.mentions_role(role),
            Protocol::Case { branches, .. } => {
                branches.iter().any(|b| b.protocol.mentions_role(role))
            }
            Protocol::Timeout {
                role: timeout_role,
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                timeout_role.matches_family(role)
                    || body.mentions_role(role)
                    || on_timeout.mentions_role(role)
                    || on_cancel
                        .as_deref()
                        .is_some_and(|branch| branch.mentions_role(role))
            }
            Protocol::Loop { body, .. } => body.mentions_role(role),
            Protocol::Parallel { protocols } => protocols.iter().any(|p| p.mentions_role(role)),
            Protocol::Rec { body, .. } => body.mentions_role(role),
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => continuation.mentions_role(role),
            Protocol::Handoff {
                target,
                continuation,
                ..
            } => target.matches_family(role) || continuation.mentions_role(role),
            Protocol::Extension {
                extension,
                continuation,
                ..
            } => extension.mentions_role(role) || continuation.mentions_role(role),
            Protocol::Var(_) | Protocol::End => false,
        }
    }

    pub(crate) fn validate(&self, roles: &[Role]) -> Result<(), ValidationError> {
        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => continuation.validate(roles),
            Protocol::Send {
                from,
                to,
                continuation,
                ..
            } => {
                ensure_declared_role(roles, from)?;
                ensure_declared_role(roles, to)?;
                continuation.validate(roles)
            }
            Protocol::Broadcast {
                from,
                to_all,
                continuation,
                ..
            } => {
                ensure_declared_role(roles, from)?;
                for to in to_all {
                    ensure_declared_role(roles, to)?;
                }
                continuation.validate(roles)
            }
            Protocol::Choice { role, branches, .. } => {
                ensure_declared_role(roles, role)?;
                validate_choice_branches(role, branches)?;
                Ok(())
            }
            Protocol::Let { continuation, .. } => continuation.validate(roles),
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    branch.protocol.validate(roles)?;
                }
                Ok(())
            }
            Protocol::Timeout {
                role,
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                ensure_declared_role(roles, role)?;
                body.validate(roles)?;
                on_timeout.validate(roles)?;
                if let Some(on_cancel) = on_cancel.as_deref() {
                    on_cancel.validate(roles)?;
                }
                Ok(())
            }
            Protocol::Loop { body, .. } => body.validate(roles),
            Protocol::Parallel { protocols } => {
                for p in protocols {
                    p.validate(roles)?;
                }
                Ok(())
            }
            Protocol::Rec { body, .. } => body.validate(roles),
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => continuation.validate(roles),
            Protocol::Handoff {
                target,
                continuation,
                ..
            } => {
                ensure_declared_role(roles, target)?;
                continuation.validate(roles)
            }
            Protocol::Extension {
                extension,
                continuation,
                ..
            } => {
                // Validate the extension with the extension system's validation
                extension.validate(roles).map_err(|e| {
                    ValidationError::ExtensionError(format!("Extension validation failed: {}", e))
                })?;
                continuation.validate(roles)
            }
            Protocol::Var(_) | Protocol::End => Ok(()),
        }
    }

    /// Get statement-level annotations for this protocol node
    pub fn get_annotations(&self) -> &Annotations {
        match self {
            Protocol::Send { annotations, .. } => annotations,
            Protocol::Broadcast { annotations, .. } => annotations,
            Protocol::Choice { annotations, .. } => annotations,
            Protocol::Begin { .. }
            | Protocol::Await { .. }
            | Protocol::Resolve { .. }
            | Protocol::Invalidate { .. }
            | Protocol::Let { .. }
            | Protocol::Case { .. }
            | Protocol::Timeout { .. }
            | Protocol::Publish { .. }
            | Protocol::PublishAuthority { .. }
            | Protocol::Materialize { .. }
            | Protocol::Handoff { .. }
            | Protocol::DependentWork { .. } => {
                static EMPTY: std::sync::OnceLock<Annotations> = std::sync::OnceLock::new();
                EMPTY.get_or_init(Annotations::new)
            }
            Protocol::Extension { annotations, .. } => annotations,
            Protocol::Loop { .. }
            | Protocol::Parallel { .. }
            | Protocol::Rec { .. }
            | Protocol::Var(_)
            | Protocol::End => {
                // Return empty annotations for protocol nodes that don't have annotations yet
                static EMPTY: std::sync::OnceLock<Annotations> = std::sync::OnceLock::new();
                EMPTY.get_or_init(Annotations::new)
            }
        }
    }

    /// Get from-role annotations for Send/Broadcast statements
    pub fn get_from_annotations(&self) -> Option<&Annotations> {
        match self {
            Protocol::Send {
                from_annotations, ..
            } => Some(from_annotations),
            Protocol::Broadcast {
                from_annotations, ..
            } => Some(from_annotations),
            _ => None,
        }
    }

    /// Get to-role annotations for Send statements
    pub fn get_to_annotations(&self) -> Option<&Annotations> {
        match self {
            Protocol::Send { to_annotations, .. } => Some(to_annotations),
            _ => None,
        }
    }

    /// Get mutable reference to annotations for modification
    pub fn get_annotations_mut(&mut self) -> Option<&mut Annotations> {
        match self {
            Protocol::Send { annotations, .. } => Some(annotations),
            Protocol::Broadcast { annotations, .. } => Some(annotations),
            Protocol::Choice { annotations, .. } => Some(annotations),
            Protocol::Begin { .. }
            | Protocol::Await { .. }
            | Protocol::Resolve { .. }
            | Protocol::Invalidate { .. }
            | Protocol::Let { .. }
            | Protocol::Case { .. }
            | Protocol::Timeout { .. }
            | Protocol::Publish { .. }
            | Protocol::PublishAuthority { .. }
            | Protocol::Materialize { .. }
            | Protocol::Handoff { .. }
            | Protocol::DependentWork { .. } => None,
            Protocol::Extension { annotations, .. } => Some(annotations),
            Protocol::Loop { .. }
            | Protocol::Parallel { .. }
            | Protocol::Rec { .. }
            | Protocol::Var(_)
            | Protocol::End => None,
        }
    }

    /// Get mutable reference to from-role annotations
    pub fn get_from_annotations_mut(&mut self) -> Option<&mut Annotations> {
        match self {
            Protocol::Send {
                from_annotations, ..
            } => Some(from_annotations),
            Protocol::Broadcast {
                from_annotations, ..
            } => Some(from_annotations),
            _ => None,
        }
    }

    /// Get mutable reference to to-role annotations
    pub fn get_to_annotations_mut(&mut self) -> Option<&mut Annotations> {
        match self {
            Protocol::Send { to_annotations, .. } => Some(to_annotations),
            _ => None,
        }
    }

    /// Add a typed annotation
    pub fn add_annotation(&mut self, annotation: super::annotation::ProtocolAnnotation) -> bool {
        if let Some(annotations) = self.get_annotations_mut() {
            annotations.push(annotation);
            true
        } else {
            false
        }
    }

    /// Clear all annotations on this protocol node
    pub fn clear_annotations(&mut self) {
        if let Some(annotations) = self.get_annotations_mut() {
            annotations.clear();
        }
        if let Some(from_annotations) = self.get_from_annotations_mut() {
            from_annotations.clear();
        }
        if let Some(to_annotations) = self.get_to_annotations_mut() {
            to_annotations.clear();
        }
    }

    /// Check if any annotations are present
    pub fn has_any_annotations(&self) -> bool {
        !self.get_annotations().is_empty()
            || self.get_from_annotations().is_some_and(|a| !a.is_empty())
            || self.get_to_annotations().is_some_and(|a| !a.is_empty())
    }

    /// Count total number of annotations (statement + role annotations)
    pub fn annotation_count(&self) -> usize {
        self.get_annotations().len()
            + self.get_from_annotations().map_or(0, |a| a.len())
            + self.get_to_annotations().map_or(0, |a| a.len())
    }

    /// Merge annotations from another protocol node
    pub fn merge_annotations_from(&mut self, other: &Protocol) {
        // Merge statement annotations
        if let Some(self_annotations) = self.get_annotations_mut() {
            self_annotations.merge(other.get_annotations());
        }

        // Merge from-role annotations
        if let (Some(self_from), Some(other_from)) = (
            self.get_from_annotations_mut(),
            other.get_from_annotations(),
        ) {
            self_from.merge(other_from);
        }

        // Merge to-role annotations
        if let (Some(self_to), Some(other_to)) =
            (self.get_to_annotations_mut(), other.get_to_annotations())
        {
            self_to.merge(other_to);
        }
    }

    /// Validate that required annotations are present
    pub fn validate_required_annotations(&self, required_keys: &[&str]) -> Result<(), Vec<String>> {
        let missing: Vec<String> = required_keys
            .iter()
            .filter(|&key| {
                !self
                    .get_annotations()
                    .iter()
                    .any(|annotation| annotation_has_key(annotation, key))
            })
            .map(|&key| key.to_string())
            .collect();

        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }

    /// Collect all protocol nodes that have a specific annotation (recursive traversal)
    pub fn collect_nodes_with_annotation<'a>(&'a self, key: &str, nodes: &mut Vec<&'a Protocol>) {
        if self
            .get_annotations()
            .iter()
            .any(|annotation| annotation_has_key(annotation, key))
        {
            nodes.push(self);
        }

        // Recursively traverse protocol structure
        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Send { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Let { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    branch.protocol.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                body.collect_nodes_with_annotation(key, nodes);
                on_timeout.collect_nodes_with_annotation(key, nodes);
                if let Some(on_cancel) = on_cancel.as_deref() {
                    on_cancel.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Loop { body, .. } => {
                body.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.collect_nodes_with_annotation(key, nodes);
                }
            }
            Protocol::Rec { body, .. } => {
                body.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::Handoff { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Extension { continuation, .. } => {
                continuation.collect_nodes_with_annotation(key, nodes);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no further traversal needed
            }
        }
    }

    /// Collect all protocol nodes that have a specific annotation with a specific value
    pub fn collect_nodes_with_annotation_value<'a>(
        &'a self,
        key: &str,
        value: &str,
        nodes: &mut Vec<&'a Protocol>,
    ) {
        if self
            .get_annotations()
            .iter()
            .any(|annotation| annotation_has_value(annotation, key, value))
        {
            nodes.push(self);
        }

        // Recursively traverse protocol structure
        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Send { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Let { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch
                        .protocol
                        .collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    branch
                        .protocol
                        .collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                body.collect_nodes_with_annotation_value(key, value, nodes);
                on_timeout.collect_nodes_with_annotation_value(key, value, nodes);
                if let Some(on_cancel) = on_cancel.as_deref() {
                    on_cancel.collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Loop { body, .. } => {
                body.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.collect_nodes_with_annotation_value(key, value, nodes);
                }
            }
            Protocol::Rec { body, .. } => {
                body.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::Handoff { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Extension { continuation, .. } => {
                continuation.collect_nodes_with_annotation_value(key, value, nodes);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no further traversal needed
            }
        }
    }

    /// Count total annotations throughout the protocol tree (recursive)
    pub fn deep_annotation_count(&self) -> usize {
        let mut count = self.annotation_count();

        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Send { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Broadcast { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Let { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    count += branch.protocol.deep_annotation_count();
                }
            }
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    count += branch.protocol.deep_annotation_count();
                }
            }
            Protocol::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                count += body.deep_annotation_count();
                count += on_timeout.deep_annotation_count();
                if let Some(on_cancel) = on_cancel.as_deref() {
                    count += on_cancel.deep_annotation_count();
                }
            }
            Protocol::Loop { body, .. } => {
                count += body.deep_annotation_count();
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    count += protocol.deep_annotation_count();
                }
            }
            Protocol::Rec { body, .. } => {
                count += body.deep_annotation_count();
            }
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::Handoff { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Extension { continuation, .. } => {
                count += continuation.deep_annotation_count();
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes - no additional annotations
            }
        }

        count
    }

    /// Apply a function to all protocol nodes that have annotations (visitor pattern)
    pub fn visit_annotated_nodes<F>(&self, f: &mut F)
    where
        F: FnMut(&Protocol),
    {
        if self.has_any_annotations() {
            f(self);
        }

        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Send { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Let { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes(f);
                }
            }
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes(f);
                }
            }
            Protocol::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                body.visit_annotated_nodes(f);
                on_timeout.visit_annotated_nodes(f);
                if let Some(on_cancel) = on_cancel.as_deref() {
                    on_cancel.visit_annotated_nodes(f);
                }
            }
            Protocol::Loop { body, .. } => {
                body.visit_annotated_nodes(f);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.visit_annotated_nodes(f);
                }
            }
            Protocol::Rec { body, .. } => {
                body.visit_annotated_nodes(f);
            }
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::Handoff { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Extension { continuation, .. } => {
                continuation.visit_annotated_nodes(f);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes
            }
        }
    }

    /// Apply a mutable function to all protocol nodes that have annotations
    pub fn visit_annotated_nodes_mut<F>(&mut self, f: &mut F)
    where
        F: FnMut(&mut Protocol),
    {
        if self.has_any_annotations() {
            f(self);
        }

        match self {
            Protocol::Begin { continuation, .. }
            | Protocol::Await { continuation, .. }
            | Protocol::Resolve { continuation, .. }
            | Protocol::Invalidate { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Send { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Broadcast { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Let { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Choice { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Case { branches, .. } => {
                for branch in branches {
                    branch.protocol.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Timeout {
                body,
                on_timeout,
                on_cancel,
                ..
            } => {
                body.visit_annotated_nodes_mut(f);
                on_timeout.visit_annotated_nodes_mut(f);
                if let Some(on_cancel) = on_cancel.as_deref_mut() {
                    on_cancel.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Loop { body, .. } => {
                body.visit_annotated_nodes_mut(f);
            }
            Protocol::Parallel { protocols } => {
                for protocol in protocols {
                    protocol.visit_annotated_nodes_mut(f);
                }
            }
            Protocol::Rec { body, .. } => {
                body.visit_annotated_nodes_mut(f);
            }
            Protocol::Publish { continuation, .. }
            | Protocol::PublishAuthority { continuation, .. }
            | Protocol::Materialize { continuation, .. }
            | Protocol::Handoff { continuation, .. }
            | Protocol::DependentWork { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Extension { continuation, .. } => {
                continuation.visit_annotated_nodes_mut(f);
            }
            Protocol::Var(_) | Protocol::End => {
                // Terminal nodes
            }
        }
    }
}
