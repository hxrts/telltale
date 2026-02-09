//! Execution Hints for Choreographic Protocols
//!
//! This module defines execution hints that are extracted from choreography annotations
//! and used during code generation. Hints are separate from the pure session types
//! (LocalType) to maintain Lean correspondence.
//!
//! # Design Rationale
//!
//! Annotations like `@parallel` and `@min_responses(N)` are deployment concerns,
//! not protocol semantics. Keeping them separate from LocalType:
//! - Preserves Lean correspondence (LocalType matches LocalTypeR)
//! - Aligns with spatial type theory (Intent vs Deployment layers)
//! - Allows hints to evolve independently of type theory
//!
//! # Architecture
//!
//! ```text
//! Choreography AST                    ExecutionHints
//! (with annotations)                  (extracted separately)
//!        │                                   │
//!        │ projection                        │ (passed through)
//!        ▼                                   ▼
//!    LocalType              +          ExecutionHints
//!   (pure types)                      (keyed by path)
//!        │                                   │
//!        └──────────────┬────────────────────┘
//!                       │ codegen
//!                       ▼
//!               Generated Code
//!          (consults hints for parallel)
//! ```

use super::choreography::Choreography;
use super::protocol::Protocol;
use super::Annotations;
use std::collections::HashMap;
use std::fmt;

/// A step in the path to an operation within a local type tree.
///
/// Used to identify specific operations for hint application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OperationStep {
    /// Send operation at index N in sequence
    Send(usize),
    /// Receive operation at index N in sequence
    Recv(usize),
    /// Branch with given label
    Branch(String),
    /// Select with given label
    Select(String),
    /// Loop iteration at index N
    Loop(usize),
    /// Recursion point with given label
    Rec(String),
}

impl fmt::Display for OperationStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperationStep::Send(n) => write!(f, "send:{}", n),
            OperationStep::Recv(n) => write!(f, "recv:{}", n),
            OperationStep::Branch(label) => write!(f, "branch:{}", label),
            OperationStep::Select(label) => write!(f, "select:{}", label),
            OperationStep::Loop(n) => write!(f, "loop:{}", n),
            OperationStep::Rec(label) => write!(f, "rec:{}", label),
        }
    }
}

/// Path to an operation in the local type tree.
///
/// A sequence of steps that uniquely identifies an operation.
/// For example, `[Send(0), Branch("Accept"), Recv(0)]` identifies
/// the first receive inside the "Accept" branch after the first send.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct OperationPath(Vec<OperationStep>);

impl OperationPath {
    /// Create an empty path (root).
    #[must_use]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Create a path from steps.
    #[must_use]
    pub fn from_steps(steps: Vec<OperationStep>) -> Self {
        Self(steps)
    }

    /// Append a step to the path, returning a new path.
    #[must_use]
    pub fn push(&self, step: OperationStep) -> Self {
        let mut steps = self.0.clone();
        steps.push(step);
        Self(steps)
    }

    /// Get the steps in this path.
    #[must_use]
    pub fn steps(&self) -> &[OperationStep] {
        &self.0
    }

    /// Check if this path is empty (root).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get the length of the path.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl fmt::Display for OperationPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "<root>")
        } else {
            let parts: Vec<String> = self.0.iter().map(|s| s.to_string()).collect();
            write!(f, "{}", parts.join("/"))
        }
    }
}

/// Execution hints for a single operation.
///
/// These hints control how code is generated for broadcast/collect operations.
#[derive(Debug, Clone, Default)]
pub struct OperationHints {
    /// Execute broadcast/collect operations in parallel using `join_all`.
    pub parallel: bool,

    /// Minimum number of responses required for collect operations.
    /// If None, all responses are required.
    pub min_responses: Option<u32>,

    /// Preserve message ordering (relevant for parallel operations).
    /// When true, results are returned in the order roles were resolved.
    pub ordered: bool,
}

impl OperationHints {
    /// Create hints for parallel execution.
    #[must_use]
    pub fn parallel() -> Self {
        Self {
            parallel: true,
            ..Default::default()
        }
    }

    /// Create hints with minimum responses requirement.
    #[must_use]
    pub fn with_min_responses(min: u32) -> Self {
        Self {
            min_responses: Some(min),
            ..Default::default()
        }
    }

    /// Create hints for ordered parallel execution.
    #[must_use]
    pub fn parallel_ordered() -> Self {
        Self {
            parallel: true,
            ordered: true,
            ..Default::default()
        }
    }

    /// Builder: enable parallel execution.
    #[must_use]
    pub fn with_parallel(mut self) -> Self {
        self.parallel = true;
        self
    }

    /// Builder: disable parallel execution (sequential).
    #[must_use]
    pub fn sequential(mut self) -> Self {
        self.parallel = false;
        self
    }

    /// Builder: set minimum responses.
    #[must_use]
    pub fn set_min_responses(mut self, min: Option<u32>) -> Self {
        self.min_responses = min;
        self
    }

    /// Builder: enable ordered execution.
    #[must_use]
    pub fn with_ordered(mut self) -> Self {
        self.ordered = true;
        self
    }

    /// Builder: disable ordered execution.
    #[must_use]
    pub fn unordered(mut self) -> Self {
        self.ordered = false;
        self
    }

    /// Merge with another hints, taking non-default values.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        Self {
            parallel: self.parallel || other.parallel,
            min_responses: self.min_responses.or(other.min_responses),
            ordered: self.ordered || other.ordered,
        }
    }
}

/// Collection of execution hints for a protocol.
///
/// Maps operation paths to their execution hints. Operations without
/// explicit hints use default behavior (sequential, all responses required).
#[derive(Debug, Clone, Default)]
pub struct ExecutionHints {
    /// Hints keyed by operation path.
    hints: HashMap<OperationPath, OperationHints>,

    /// Role name this hints collection is for (after projection).
    role: Option<String>,
}

impl ExecutionHints {
    /// Create an empty hints collection.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create hints for a specific role.
    #[must_use]
    pub fn for_role(role: impl Into<String>) -> Self {
        Self {
            hints: HashMap::new(),
            role: Some(role.into()),
        }
    }

    /// Get the role this hints collection is for.
    #[must_use]
    pub fn role(&self) -> Option<&str> {
        self.role.as_deref()
    }

    /// Insert hints for an operation path.
    pub fn insert(&mut self, path: OperationPath, hints: OperationHints) {
        self.hints.insert(path, hints);
    }

    /// Get hints for an operation path.
    #[must_use]
    pub fn get(&self, path: &OperationPath) -> Option<&OperationHints> {
        self.hints.get(path)
    }

    /// Check if an operation should use parallel execution.
    #[must_use]
    pub fn is_parallel(&self, path: &OperationPath) -> bool {
        self.get(path).map(|h| h.parallel).unwrap_or(false)
    }

    /// Get the minimum responses requirement for an operation.
    #[must_use]
    pub fn min_responses(&self, path: &OperationPath) -> Option<u32> {
        self.get(path).and_then(|h| h.min_responses)
    }

    /// Check if an operation should preserve ordering.
    #[must_use]
    pub fn is_ordered(&self, path: &OperationPath) -> bool {
        self.get(path).map(|h| h.ordered).unwrap_or(false)
    }

    /// Check if there are any hints.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.hints.is_empty()
    }

    /// Get the number of hints.
    #[must_use]
    pub fn len(&self) -> usize {
        self.hints.len()
    }

    /// Iterate over all hints.
    pub fn iter(&self) -> impl Iterator<Item = (&OperationPath, &OperationHints)> {
        self.hints.iter()
    }

    /// Merge with another hints collection.
    #[must_use]
    pub fn merge(&self, other: &Self) -> Self {
        let mut merged = self.clone();
        for (path, hints) in &other.hints {
            merged
                .hints
                .entry(path.clone())
                .and_modify(|h| *h = h.merge(hints))
                .or_insert_with(|| hints.clone());
        }
        merged
    }

    /// Extract execution hints from a Protocol tree.
    ///
    /// Walks the protocol and extracts `@parallel`, `@min_responses`, and `@ordered`
    /// annotations into an ExecutionHints collection.
    #[must_use]
    pub fn extract_from_protocol(protocol: &Protocol) -> Self {
        let mut hints = Self::new();
        let mut counters = HintExtractionCounters::default();
        Self::extract_recursive(protocol, &OperationPath::new(), &mut hints, &mut counters);
        hints
    }

    /// Recursive helper for hint extraction.
    fn extract_recursive(
        protocol: &Protocol,
        path: &OperationPath,
        hints: &mut ExecutionHints,
        counters: &mut HintExtractionCounters,
    ) {
        match protocol {
            Protocol::Send {
                annotations,
                continuation,
                ..
            } => {
                let send_path = path.push(OperationStep::Send(counters.send_count));
                counters.send_count += 1;

                if let Some(op_hints) = Self::hints_from_annotations(annotations) {
                    hints.insert(send_path.clone(), op_hints);
                }

                Self::extract_recursive(continuation, &send_path, hints, counters);
            }

            Protocol::Broadcast {
                annotations,
                continuation,
                ..
            } => {
                let send_path = path.push(OperationStep::Send(counters.send_count));
                counters.send_count += 1;

                if let Some(op_hints) = Self::hints_from_annotations(annotations) {
                    hints.insert(send_path.clone(), op_hints);
                }

                Self::extract_recursive(continuation, &send_path, hints, counters);
            }

            Protocol::Choice {
                branches,
                annotations,
                ..
            } => {
                // Check for annotations on the choice itself
                if let Some(op_hints) = Self::hints_from_annotations(annotations) {
                    hints.insert(path.clone(), op_hints);
                }

                for branch in branches.as_slice() {
                    let branch_path = path.push(OperationStep::Branch(branch.label.to_string()));
                    let mut branch_counters = HintExtractionCounters::default();
                    Self::extract_recursive(
                        &branch.protocol,
                        &branch_path,
                        hints,
                        &mut branch_counters,
                    );
                }
            }

            Protocol::Loop { body, .. } => {
                let loop_path = path.push(OperationStep::Loop(counters.loop_count));
                counters.loop_count += 1;
                let mut loop_counters = HintExtractionCounters::default();
                Self::extract_recursive(body, &loop_path, hints, &mut loop_counters);
            }

            Protocol::Rec { label, body } => {
                let rec_path = path.push(OperationStep::Rec(label.to_string()));
                let mut rec_counters = HintExtractionCounters::default();
                Self::extract_recursive(body, &rec_path, hints, &mut rec_counters);
            }

            Protocol::Parallel { protocols } => {
                for (i, proto) in protocols.as_slice().iter().enumerate() {
                    let parallel_path = path.push(OperationStep::Loop(i)); // Reuse Loop for parallel branches
                    let mut parallel_counters = HintExtractionCounters::default();
                    Self::extract_recursive(proto, &parallel_path, hints, &mut parallel_counters);
                }
            }

            Protocol::Extension {
                annotations,
                continuation,
                ..
            } => {
                if let Some(op_hints) = Self::hints_from_annotations(annotations) {
                    hints.insert(path.clone(), op_hints);
                }
                Self::extract_recursive(continuation, path, hints, counters);
            }

            Protocol::Var(_) | Protocol::End => {
                // No hints to extract from terminal nodes
            }
        }
    }

    /// Extract OperationHints from Annotations if any relevant ones are present.
    fn hints_from_annotations(annotations: &Annotations) -> Option<OperationHints> {
        let parallel = annotations.has_parallel();
        let ordered = annotations.has_ordered();
        let min_responses = annotations.min_responses();

        if parallel || ordered || min_responses.is_some() {
            Some(OperationHints {
                parallel,
                ordered,
                min_responses,
            })
        } else {
            None
        }
    }
}

/// Counters for tracking position during hint extraction.
#[derive(Default)]
struct HintExtractionCounters {
    send_count: usize,
    loop_count: usize,
}

/// A choreography paired with its extracted execution hints.
///
/// This struct holds a choreography and the execution hints extracted from
/// its annotations. The hints are separate from the choreography to maintain
/// clean separation between protocol semantics and deployment configuration.
#[derive(Debug)]
pub struct ChoreographyWithHints {
    /// The parsed choreography
    pub choreography: Choreography,
    /// Execution hints extracted from annotations
    pub hints: ExecutionHints,
}

impl ChoreographyWithHints {
    /// Create a new choreography with hints from a choreography.
    ///
    /// Extracts execution hints from the choreography's protocol annotations.
    #[must_use]
    pub fn from_choreography(choreography: Choreography) -> Self {
        let hints = ExecutionHints::extract_from_protocol(&choreography.protocol);
        Self {
            choreography,
            hints,
        }
    }

    /// Create from a choreography with pre-computed hints.
    #[must_use]
    pub fn new(choreography: Choreography, hints: ExecutionHints) -> Self {
        Self {
            choreography,
            hints,
        }
    }
}

/// Builder for constructing ExecutionHints.
#[derive(Debug, Default)]
pub struct ExecutionHintsBuilder {
    hints: ExecutionHints,
    current_path: OperationPath,
}

impl ExecutionHintsBuilder {
    /// Create a new builder.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a builder for a specific role.
    #[must_use]
    pub fn for_role(role: impl Into<String>) -> Self {
        Self {
            hints: ExecutionHints::for_role(role),
            current_path: OperationPath::new(),
        }
    }

    /// Set the current path context.
    #[must_use]
    pub fn at_path(mut self, path: OperationPath) -> Self {
        self.current_path = path;
        self
    }

    /// Add a parallel hint at the current path.
    #[must_use]
    pub fn parallel(mut self) -> Self {
        let hints = self
            .hints
            .hints
            .entry(self.current_path.clone())
            .or_default();
        hints.parallel = true;
        self
    }

    /// Add a min_responses hint at the current path.
    #[must_use]
    pub fn min_responses(mut self, min: u32) -> Self {
        let hints = self
            .hints
            .hints
            .entry(self.current_path.clone())
            .or_default();
        hints.min_responses = Some(min);
        self
    }

    /// Add an ordered hint at the current path.
    #[must_use]
    pub fn ordered(mut self) -> Self {
        let hints = self
            .hints
            .hints
            .entry(self.current_path.clone())
            .or_default();
        hints.ordered = true;
        self
    }

    /// Add hints at a specific path.
    #[must_use]
    pub fn with_hints(mut self, path: OperationPath, hints: OperationHints) -> Self {
        self.hints.insert(path, hints);
        self
    }

    /// Build the ExecutionHints.
    #[must_use]
    pub fn build(self) -> ExecutionHints {
        self.hints
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_operation_path_display() {
        let path = OperationPath::new();
        assert_eq!(path.to_string(), "<root>");

        let path = path.push(OperationStep::Send(0));
        assert_eq!(path.to_string(), "send:0");

        let path = path.push(OperationStep::Branch("Accept".to_string()));
        assert_eq!(path.to_string(), "send:0/branch:Accept");

        let path = path.push(OperationStep::Recv(1));
        assert_eq!(path.to_string(), "send:0/branch:Accept/recv:1");
    }

    #[test]
    fn test_execution_hints_basic() {
        let mut hints = ExecutionHints::new();
        let path = OperationPath::from_steps(vec![OperationStep::Send(0)]);

        hints.insert(path.clone(), OperationHints::parallel());

        assert!(hints.is_parallel(&path));
        assert!(!hints.is_ordered(&path));
        assert_eq!(hints.min_responses(&path), None);
    }

    #[test]
    fn test_execution_hints_min_responses() {
        let mut hints = ExecutionHints::new();
        let path = OperationPath::from_steps(vec![OperationStep::Recv(0)]);

        hints.insert(
            path.clone(),
            OperationHints::with_min_responses(3).with_parallel(),
        );

        assert!(hints.is_parallel(&path));
        assert_eq!(hints.min_responses(&path), Some(3));
    }

    #[test]
    fn test_execution_hints_builder() {
        let hints = ExecutionHintsBuilder::for_role("Coordinator")
            .at_path(OperationPath::from_steps(vec![OperationStep::Send(0)]))
            .parallel()
            .at_path(OperationPath::from_steps(vec![OperationStep::Recv(0)]))
            .min_responses(3)
            .ordered()
            .build();

        let send_path = OperationPath::from_steps(vec![OperationStep::Send(0)]);
        let recv_path = OperationPath::from_steps(vec![OperationStep::Recv(0)]);

        assert!(hints.is_parallel(&send_path));
        assert!(!hints.is_ordered(&send_path));

        assert!(!hints.is_parallel(&recv_path));
        assert!(hints.is_ordered(&recv_path));
        assert_eq!(hints.min_responses(&recv_path), Some(3));
    }

    #[test]
    fn test_operation_hints_merge() {
        let h1 = OperationHints {
            parallel: true,
            min_responses: None,
            ordered: false,
        };
        let h2 = OperationHints {
            parallel: false,
            min_responses: Some(3),
            ordered: true,
        };

        let merged = h1.merge(&h2);
        assert!(merged.parallel); // true || false
        assert_eq!(merged.min_responses, Some(3)); // None.or(Some(3))
        assert!(merged.ordered); // false || true
    }

    #[test]
    fn test_execution_hints_default_values() {
        let hints = ExecutionHints::new();
        let path = OperationPath::from_steps(vec![OperationStep::Send(0)]);

        // Default: not parallel, no min_responses, not ordered
        assert!(!hints.is_parallel(&path));
        assert_eq!(hints.min_responses(&path), None);
        assert!(!hints.is_ordered(&path));
    }

    #[test]
    fn test_extract_from_protocol_with_parallel() {
        use crate::ast::annotation::Annotations;
        use crate::ast::role::Role;
        use crate::ast::MessageType;
        use proc_macro2::Ident;
        use proc_macro2::Span;

        // Create a protocol: @parallel A -> B : Msg
        let mut annotations = Annotations::new();
        annotations.push(crate::ast::ProtocolAnnotation::Parallel);

        let protocol = Protocol::Send {
            from: Role::new(Ident::new("A", Span::call_site())).unwrap(),
            to: Role::new(Ident::new("B", Span::call_site())).unwrap(),
            message: MessageType {
                name: Ident::new("Msg", Span::call_site()),
                type_annotation: None,
                payload: None,
            },
            continuation: Box::new(Protocol::End),
            annotations,
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        };

        let hints = ExecutionHints::extract_from_protocol(&protocol);
        let path = OperationPath::from_steps(vec![OperationStep::Send(0)]);

        assert!(hints.is_parallel(&path));
        assert!(!hints.is_ordered(&path));
        assert_eq!(hints.min_responses(&path), None);
    }

    #[test]
    fn test_extract_from_protocol_with_min_responses() {
        use crate::ast::annotation::Annotations;
        use crate::ast::role::Role;
        use crate::ast::MessageType;
        use proc_macro2::Ident;
        use proc_macro2::Span;

        // Create a protocol: @min_responses(3) A -> B : Msg
        let mut annotations = Annotations::new();
        annotations.push(crate::ast::ProtocolAnnotation::MinResponses(3));

        let protocol = Protocol::Send {
            from: Role::new(Ident::new("A", Span::call_site())).unwrap(),
            to: Role::new(Ident::new("B", Span::call_site())).unwrap(),
            message: MessageType {
                name: Ident::new("Msg", Span::call_site()),
                type_annotation: None,
                payload: None,
            },
            continuation: Box::new(Protocol::End),
            annotations,
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        };

        let hints = ExecutionHints::extract_from_protocol(&protocol);
        let path = OperationPath::from_steps(vec![OperationStep::Send(0)]);

        assert!(!hints.is_parallel(&path));
        assert_eq!(hints.min_responses(&path), Some(3));
    }

    #[test]
    fn test_extract_from_protocol_combined() {
        use crate::ast::annotation::Annotations;
        use crate::ast::role::Role;
        use crate::ast::MessageType;
        use proc_macro2::Ident;
        use proc_macro2::Span;

        // Create a protocol: @parallel @ordered @min_responses(2) A -> B : Msg
        let mut annotations = Annotations::new();
        annotations.push(crate::ast::ProtocolAnnotation::Parallel);
        annotations.push(crate::ast::ProtocolAnnotation::Ordered);
        annotations.push(crate::ast::ProtocolAnnotation::MinResponses(2));

        let protocol = Protocol::Send {
            from: Role::new(Ident::new("A", Span::call_site())).unwrap(),
            to: Role::new(Ident::new("B", Span::call_site())).unwrap(),
            message: MessageType {
                name: Ident::new("Msg", Span::call_site()),
                type_annotation: None,
                payload: None,
            },
            continuation: Box::new(Protocol::End),
            annotations,
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        };

        let hints = ExecutionHints::extract_from_protocol(&protocol);
        let path = OperationPath::from_steps(vec![OperationStep::Send(0)]);

        assert!(hints.is_parallel(&path));
        assert!(hints.is_ordered(&path));
        assert_eq!(hints.min_responses(&path), Some(2));
    }

    #[test]
    fn test_extract_no_hints_when_no_annotations() {
        use crate::ast::annotation::Annotations;
        use crate::ast::role::Role;
        use crate::ast::MessageType;
        use proc_macro2::Ident;
        use proc_macro2::Span;

        // Create a protocol with no execution annotations: A -> B : Msg
        let protocol = Protocol::Send {
            from: Role::new(Ident::new("A", Span::call_site())).unwrap(),
            to: Role::new(Ident::new("B", Span::call_site())).unwrap(),
            message: MessageType {
                name: Ident::new("Msg", Span::call_site()),
                type_annotation: None,
                payload: None,
            },
            continuation: Box::new(Protocol::End),
            annotations: Annotations::new(),
            from_annotations: Annotations::new(),
            to_annotations: Annotations::new(),
        };

        let hints = ExecutionHints::extract_from_protocol(&protocol);

        // Should have no hints
        assert!(hints.is_empty());
    }
}
