// Projection from global choreographies to local session types

use crate::ast::{
    Branch, Choreography, LocalType, MessageType, Protocol, RangeExpr, Role, RoleIndex, RoleParam,
    RoleRange,
};
use std::collections::HashMap;

/// Project a choreography to a local session type for a specific role
pub fn project(choreography: &Choreography, role: &Role) -> Result<LocalType, ProjectionError> {
    let mut context = ProjectionContext::new(choreography, role);
    context.project_protocol(&choreography.protocol)
}

/// Errors that can occur during projection
#[derive(Debug, thiserror::Error)]
pub enum ProjectionError {
    #[error("Cannot project choice for non-participant role")]
    NonParticipantChoice,

    #[error("Parallel composition not supported for role {0}")]
    UnsupportedParallel(String),

    #[error("Inconsistent projections in parallel branches")]
    InconsistentParallel,

    #[error("Recursive variable {0} not in scope")]
    UnboundVariable(String),

    #[error("Dynamic role {role} requires runtime context for projection")]
    DynamicRoleProjection { role: String },

    #[error("Symbolic role parameter '{param}' not bound in context")]
    UnboundSymbolic { param: String },

    #[error("Range role index cannot be projected to concrete local type")]
    RangeProjection,

    #[error("Wildcard role index requires specialized projection context")]
    WildcardProjection,

    #[error("Cannot merge branches: {0}")]
    MergeFailure(String),
}

/// Context for projection algorithm
struct ProjectionContext<'a> {
    role: &'a Role,
    /// Bindings for symbolic role parameters (e.g., N -> 5)
    role_bindings: HashMap<String, u32>,
    /// Bindings for symbolic index variables (e.g., i -> 2)
    #[allow(dead_code)]
    index_bindings: HashMap<String, u32>,
}

impl<'a> ProjectionContext<'a> {
    fn new(_choreography: &'a Choreography, role: &'a Role) -> Self {
        ProjectionContext {
            role,
            role_bindings: HashMap::new(),
            index_bindings: HashMap::new(),
        }
    }

    /// Create a new context with dynamic role bindings
    #[allow(dead_code)]
    fn with_bindings(
        _choreography: &'a Choreography,
        role: &'a Role,
        role_bindings: HashMap<String, u32>,
        index_bindings: HashMap<String, u32>,
    ) -> Self {
        ProjectionContext {
            role,
            role_bindings,
            index_bindings,
        }
    }

    /// Check if this projection role matches the given protocol role
    fn role_matches(&self, protocol_role: &Role) -> Result<bool, ProjectionError> {
        // First check for exact name match
        if self.role.name != protocol_role.name {
            return Ok(false);
        }

        // If both are simple roles, they match
        if !self.role.is_parameterized() && !protocol_role.is_parameterized() {
            return Ok(true);
        }

        // Handle dynamic role matching
        self.matches_dynamic_role(protocol_role)
    }

    /// Check if the projection role matches a dynamic protocol role
    fn matches_dynamic_role(&self, protocol_role: &Role) -> Result<bool, ProjectionError> {
        match (&self.role.param, &protocol_role.param) {
            // Static vs Static: must have same count
            (Some(RoleParam::Static(self_count)), Some(RoleParam::Static(proto_count))) => {
                Ok(self_count == proto_count)
            }
            // Static vs Symbolic: resolve symbolic and compare
            (Some(RoleParam::Static(self_count)), Some(RoleParam::Symbolic(sym_name))) => {
                if let Some(&resolved_count) = self.role_bindings.get(sym_name) {
                    Ok(*self_count == resolved_count)
                } else {
                    Err(ProjectionError::UnboundSymbolic {
                        param: sym_name.clone(),
                    })
                }
            }
            // Symbolic vs Static: resolve symbolic and compare
            (Some(RoleParam::Symbolic(sym_name)), Some(RoleParam::Static(proto_count))) => {
                if let Some(&resolved_count) = self.role_bindings.get(sym_name) {
                    Ok(resolved_count == *proto_count)
                } else {
                    Err(ProjectionError::UnboundSymbolic {
                        param: sym_name.clone(),
                    })
                }
            }
            // Symbolic vs Symbolic: resolve both and compare
            (Some(RoleParam::Symbolic(self_sym)), Some(RoleParam::Symbolic(proto_sym))) => {
                let self_resolved = self.role_bindings.get(self_sym).ok_or_else(|| {
                    ProjectionError::UnboundSymbolic {
                        param: self_sym.clone(),
                    }
                })?;
                let proto_resolved = self.role_bindings.get(proto_sym).ok_or_else(|| {
                    ProjectionError::UnboundSymbolic {
                        param: proto_sym.clone(),
                    }
                })?;
                Ok(self_resolved == proto_resolved)
            }
            // Runtime roles require special handling
            (_, Some(RoleParam::Runtime)) | (Some(RoleParam::Runtime), _) => {
                Err(ProjectionError::DynamicRoleProjection {
                    role: protocol_role.name.to_string(),
                })
            }
            // One parameterized, one not: no match
            (Some(_), None) | (None, Some(_)) => Ok(false),
            // Both None: already handled above
            (None, None) => Ok(true),
        }
    }

    /// Check if the projection role matches a specific index of a protocol role
    #[allow(dead_code)]
    fn matches_role_index(&self, protocol_role: &Role) -> Result<bool, ProjectionError> {
        // First check if the base role names match
        if self.role.name != protocol_role.name {
            return Ok(false);
        }

        match (&self.role.index, &protocol_role.index) {
            // Both have concrete indices
            (Some(RoleIndex::Concrete(self_idx)), Some(RoleIndex::Concrete(proto_idx))) => {
                Ok(self_idx == proto_idx)
            }
            // Self has concrete index, protocol has symbolic
            (Some(RoleIndex::Concrete(self_idx)), Some(RoleIndex::Symbolic(sym_name))) => {
                if let Some(&resolved_idx) = self.index_bindings.get(sym_name) {
                    Ok(*self_idx == resolved_idx)
                } else {
                    Err(ProjectionError::UnboundSymbolic {
                        param: sym_name.clone(),
                    })
                }
            }
            // Self has symbolic index, protocol has concrete
            (Some(RoleIndex::Symbolic(sym_name)), Some(RoleIndex::Concrete(proto_idx))) => {
                if let Some(&resolved_idx) = self.index_bindings.get(sym_name) {
                    Ok(resolved_idx == *proto_idx)
                } else {
                    Err(ProjectionError::UnboundSymbolic {
                        param: sym_name.clone(),
                    })
                }
            }
            // Protocol has wildcard: self matches if it has any index
            (Some(_), Some(RoleIndex::Wildcard)) => Ok(true),
            // Protocol has range: check if self's index is in range
            (Some(RoleIndex::Concrete(self_idx)), Some(RoleIndex::Range(range))) => {
                self.index_in_range(*self_idx, range)
            }
            // Other combinations require more complex handling
            _ => Ok(false),
        }
    }

    /// Check if an index is within a range
    #[allow(dead_code)]
    fn index_in_range(&self, index: u32, range: &RoleRange) -> Result<bool, ProjectionError> {
        let start = match &range.start {
            RangeExpr::Concrete(val) => *val,
            RangeExpr::Symbolic(sym) => *self
                .index_bindings
                .get(sym)
                .ok_or_else(|| ProjectionError::UnboundSymbolic { param: sym.clone() })?,
        };

        let end = match &range.end {
            RangeExpr::Concrete(val) => *val,
            RangeExpr::Symbolic(sym) => *self
                .index_bindings
                .get(sym)
                .ok_or_else(|| ProjectionError::UnboundSymbolic { param: sym.clone() })?,
        };

        Ok(index >= start && index < end)
    }

    fn project_protocol(&mut self, protocol: &Protocol) -> Result<LocalType, ProjectionError> {
        match protocol {
            Protocol::Send {
                from,
                to,
                message,
                continuation,
                ..
            } => self.project_send(from, to, message, continuation),

            Protocol::Broadcast {
                from,
                to_all,
                message,
                continuation,
                ..
            } => self.project_broadcast(from, to_all, message, continuation),

            Protocol::Choice {
                role: choice_role,
                branches,
                ..
            } => self.project_choice(choice_role, branches),

            Protocol::Loop { condition, body } => self.project_loop(condition.as_ref(), body),

            Protocol::Parallel { protocols } => self.project_parallel(protocols),

            Protocol::Rec { label, body } => self.project_rec(label, body),

            Protocol::Var(label) => self.project_var(label),

            Protocol::End => Ok(LocalType::End),

            Protocol::Extension {
                extension: _,
                continuation: _,
                annotations: _,
            } => {
                // Delegate projection to the extension implementation
                // Note: We would need to convert between ProjectionContext types here
                // For now, just return a placeholder
                Ok(LocalType::End)
            }
        }
    }

    /// Project a send operation onto the local type for this role
    ///
    /// # Projection Rules
    /// - If `role == from`: Project to `Send(to, message, continuation↓role)`
    /// - If `role == to`: Project to `Receive(from, message, continuation↓role)`
    /// - Otherwise: Project to `continuation↓role` (uninvolved party)
    ///
    /// This implements the standard session type projection rule where
    /// uninvolved parties simply skip communication they don't participate in.
    fn project_send(
        &mut self,
        from: &Role,
        to: &Role,
        message: &MessageType,
        continuation: &Protocol,
    ) -> Result<LocalType, ProjectionError> {
        let is_sender = self.role_matches(from)?;
        let is_receiver = self.role_matches(to)?;

        if is_sender {
            // We are the sender
            Ok(LocalType::Send {
                to: to.clone(),
                message: message.clone(),
                continuation: Box::new(self.project_protocol(continuation)?),
            })
        } else if is_receiver {
            // We are the receiver
            Ok(LocalType::Receive {
                from: from.clone(),
                message: message.clone(),
                continuation: Box::new(self.project_protocol(continuation)?),
            })
        } else {
            // We are not involved, skip to continuation
            self.project_protocol(continuation)
        }
    }

    /// Project a broadcast operation onto the local type for this role
    ///
    /// # Projection Rules
    /// - If `role == from`: Expand into nested sends to all recipients
    /// - If `role ∈ to_all`: Project to `Receive(from, message, continuation↓role)`  
    /// - Otherwise: Project to `continuation↓role`
    ///
    /// # Implementation Note
    /// Broadcasts are expanded into sequential sends at the sender side.
    /// Sends are built in reverse order to create proper nesting:
    /// `Broadcast(A, [B,C], msg) → Send(A→B, Send(A→C, continuation))`
    fn project_broadcast(
        &mut self,
        from: &Role,
        to_all: &[Role],
        message: &MessageType,
        continuation: &Protocol,
    ) -> Result<LocalType, ProjectionError> {
        let is_sender = self.role_matches(from)?;

        // Check if we are a recipient using dynamic role matching
        let mut is_receiver = false;
        for to_role in to_all {
            if self.role_matches(to_role)? {
                is_receiver = true;
                break;
            }
        }

        if is_sender {
            // We are broadcasting - need to send to each recipient
            let mut current = self.project_protocol(continuation)?;

            // Build sends in reverse order so they nest correctly
            for to in to_all.iter().rev() {
                current = LocalType::Send {
                    to: to.clone(),
                    message: message.clone(),
                    continuation: Box::new(current),
                };
            }

            Ok(current)
        } else if is_receiver {
            // We are receiving the broadcast
            Ok(LocalType::Receive {
                from: from.clone(),
                message: message.clone(),
                continuation: Box::new(self.project_protocol(continuation)?),
            })
        } else {
            // Not involved in broadcast
            self.project_protocol(continuation)
        }
    }

    /// Project a choice operation onto the local type for this role
    ///
    /// # Projection Rules (Enhanced)
    /// - If `role == choice_role`:
    ///   - If branches start with Send: Project as `Select` (communicated choice)
    ///   - Otherwise: Project as `LocalChoice` (local decision)
    /// - If `role` receives the choice: Project as `Branch`
    /// - Otherwise: Merge continuations (uninvolved party)
    ///
    /// # Implementation Notes
    /// This enhancement supports choice branches that don't start with Send,
    /// allowing for local decisions and more complex choreographic patterns.
    fn project_choice(
        &mut self,
        choice_role: &Role,
        branches: &[Branch],
    ) -> Result<LocalType, ProjectionError> {
        let is_choice_maker = self.role_matches(choice_role)?;

        if is_choice_maker {
            // We make the choice
            // Check if this is a communicated choice (branches start with Send)
            let first_sends = branches
                .iter()
                .all(|b| matches!(&b.protocol, Protocol::Send { .. }));

            if first_sends && !branches.is_empty() {
                // Communicated choice - project as Select
                let mut local_branches = Vec::new();

                for branch in branches {
                    // Skip the initial send (it's implied by the choice)
                    let inner_protocol = match &branch.protocol {
                        Protocol::Send { continuation, .. } => continuation,
                        _ => &branch.protocol, // Won't happen due to check above
                    };

                    let local_type = self.project_protocol(inner_protocol)?;
                    local_branches.push((branch.label.clone(), local_type));
                }

                // Find the recipient (from first branch's send)
                let recipient = match &branches[0].protocol {
                    Protocol::Send { to, .. } => to.clone(),
                    _ => {
                        return Err(ProjectionError::NonParticipantChoice);
                    }
                };

                Ok(LocalType::Select {
                    to: recipient,
                    branches: local_branches,
                })
            } else {
                // Local choice (no communication) - project as LocalChoice
                let mut local_branches = Vec::new();

                for branch in branches {
                    let local_type = self.project_protocol(&branch.protocol)?;
                    local_branches.push((branch.label.clone(), local_type));
                }

                Ok(LocalType::LocalChoice {
                    branches: local_branches,
                })
            }
        } else {
            // Check if we receive the choice
            let mut receives_choice = false;
            let mut sender = None;

            for branch in branches {
                if let Protocol::Send { from, to, .. } = &branch.protocol {
                    if self.role_matches(to)? {
                        receives_choice = true;
                        sender = Some(from.clone());
                        break;
                    }
                }
            }

            if receives_choice {
                // We receive the choice - project as Branch
                let sender = sender.expect("sender must be Some when receives_choice is true");
                let mut local_branches = Vec::new();

                for branch in branches {
                    let local_type = self.project_protocol(&branch.protocol)?;
                    local_branches.push((branch.label.clone(), local_type));
                }

                Ok(LocalType::Branch {
                    from: sender,
                    branches: local_branches,
                })
            } else {
                // Not involved in the choice - merge continuations
                self.merge_choice_continuations(branches)
            }
        }
    }

    /// Project a loop operation onto the local type for this role
    ///
    /// # Projection Rules
    /// - Project the loop body
    /// - If the role participates in the loop: Wrap in `Loop` with condition
    /// - If the role doesn't participate: Project to End
    ///
    /// # Implementation Notes
    /// Loop conditions are now preserved in the local type, allowing runtime
    /// to make decisions about loop iteration based on the condition type.
    fn project_loop(
        &mut self,
        condition: Option<&crate::ast::protocol::Condition>,
        body: &Protocol,
    ) -> Result<LocalType, ProjectionError> {
        let body_projection = self.project_protocol(body)?;

        // Only include Loop if the body actually involves this role
        if body_projection == LocalType::End {
            Ok(LocalType::End)
        } else {
            Ok(LocalType::Loop {
                condition: condition.cloned(),
                body: Box::new(body_projection),
            })
        }
    }

    /// Project a parallel composition onto the local type for this role
    ///
    /// # Projection Rules (Enhanced)
    /// - If role appears in 0 branches: Project to `End`
    /// - If role appears in 1 branch: Use that projection
    /// - If role appears in multiple branches:
    ///   - Check for conflicts (incompatible operations)
    ///   - If mergeable: Interleave operations
    ///   - If conflicting: Return error with details
    ///
    /// # Implementation Notes
    /// This enhancement detects conflicting parallel operations (e.g., sending
    /// to the same recipient simultaneously) and provides better error messages.
    fn project_parallel(&mut self, protocols: &[Protocol]) -> Result<LocalType, ProjectionError> {
        // Project all parallel branches for this role
        let mut projections = Vec::new();
        for protocol in protocols {
            if protocol.mentions_role(self.role) {
                projections.push(self.project_protocol(protocol)?);
            }
        }

        match projections.len() {
            0 => {
                // Role doesn't appear in any parallel branch
                Ok(LocalType::End)
            }
            1 => {
                // Role appears in exactly one branch - use that projection
                Ok(projections
                    .into_iter()
                    .next()
                    .expect("projections must have exactly one element"))
            }
            _ => {
                // Role appears in multiple parallel branches
                // Check for conflicts before merging
                self.merge_parallel_projections(projections)
            }
        }
    }

    /// Merge multiple parallel projections for a single role
    ///
    /// # Conflict Detection
    /// Checks for incompatible parallel operations:
    /// - Multiple sends to the same role
    /// - Multiple receives from the same role
    /// - Conflicting choices
    ///
    /// # Merging Strategy
    /// For compatible operations, interleaves them sequentially.
    /// The actual execution order is non-deterministic (depends on runtime).
    fn merge_parallel_projections(
        &mut self,
        projections: Vec<LocalType>,
    ) -> Result<LocalType, ProjectionError> {
        // Remove End projections as they don't contribute
        let non_end: Vec<_> = projections
            .into_iter()
            .filter(|p| p != &LocalType::End)
            .collect();

        match non_end.len() {
            0 => Ok(LocalType::End),
            1 => Ok(non_end
                .into_iter()
                .next()
                .expect("non_end must have exactly one element")),
            _ => {
                // Check for conflicts
                self.check_parallel_conflicts(&non_end)?;

                // Multiple non-trivial projections - merge them
                // Interleaving is allowed in parallel composition
                // The merge creates a sequential composition (non-deterministic order)
                let mut merged = LocalType::End;
                for proj in non_end.into_iter().rev() {
                    merged = self.sequential_merge(proj, merged);
                }
                Ok(merged)
            }
        }
    }

    /// Check for conflicts between parallel projections
    ///
    /// Returns an error if the projections have incompatible operations
    /// that cannot be safely interleaved.
    fn check_parallel_conflicts(&self, projections: &[LocalType]) -> Result<(), ProjectionError> {
        // Check for conflicting sends
        let mut send_targets = Vec::new();
        let mut recv_sources = Vec::new();

        for proj in projections {
            match proj {
                LocalType::Send { to, .. } => {
                    if send_targets.contains(to) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    send_targets.push(to.clone());
                }
                LocalType::Receive { from, .. } => {
                    if recv_sources.contains(from) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    recv_sources.push(from.clone());
                }
                LocalType::Select { to, .. } => {
                    if send_targets.contains(to) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    send_targets.push(to.clone());
                }
                LocalType::Branch { from, .. } => {
                    if recv_sources.contains(from) {
                        return Err(ProjectionError::InconsistentParallel);
                    }
                    recv_sources.push(from.clone());
                }
                _ => {
                    // Other types are compatible with parallel composition
                }
            }
        }

        Ok(())
    }

    fn sequential_merge(&self, first: LocalType, second: LocalType) -> LocalType {
        // Merge two local types sequentially
        match (first, second) {
            (LocalType::End, other) | (other, LocalType::End) => other,
            (first, second) => {
                // Chain them together
                self.append_continuation(first, second)
            }
        }
    }

    fn append_continuation(&self, local_type: LocalType, continuation: LocalType) -> LocalType {
        Self::append_continuation_static(local_type, continuation)
    }

    fn append_continuation_static(local_type: LocalType, continuation: LocalType) -> LocalType {
        match local_type {
            LocalType::Send {
                to,
                message,
                continuation: cont,
            } => LocalType::Send {
                to,
                message,
                continuation: Box::new(Self::append_continuation_static(
                    *cont,
                    continuation.clone(),
                )),
            },
            LocalType::Receive {
                from,
                message,
                continuation: cont,
            } => LocalType::Receive {
                from,
                message,
                continuation: Box::new(Self::append_continuation_static(
                    *cont,
                    continuation.clone(),
                )),
            },
            LocalType::End => continuation,
            // For other types, just return as-is with continuation appended at the end
            other => other,
        }
    }

    fn project_rec(
        &mut self,
        label: &proc_macro2::Ident,
        body: &Protocol,
    ) -> Result<LocalType, ProjectionError> {
        let body_projection = self.project_protocol(body)?;

        // Only include Rec if the body actually uses this role
        if body_projection == LocalType::End {
            Ok(LocalType::End)
        } else {
            Ok(LocalType::Rec {
                label: label.clone(),
                body: Box::new(body_projection),
            })
        }
    }

    fn project_var(&mut self, label: &proc_macro2::Ident) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::Var(label.clone()))
    }

    fn merge_choice_continuations(
        &mut self,
        branches: &[Branch],
    ) -> Result<LocalType, ProjectionError> {
        // Project each branch and find where we rejoin
        let mut projections = Vec::new();

        for branch in branches {
            projections.push(self.project_protocol(&branch.protocol)?);
        }

        // Check if all projections are identical (common case)
        if projections.windows(2).all(|w| w[0] == w[1]) {
            Ok(projections
                .into_iter()
                .next()
                .expect("projections must be non-empty when windows returned true"))
        } else {
            // Different projections per branch - need to merge
            self.merge_local_types(projections)
        }
    }

    /// Merge multiple local types using the merge algorithm.
    ///
    /// This implements the merge operation from multiparty session type theory.
    /// When a role is not involved in a choice, the projections of different
    /// branches must be merged.
    fn merge_local_types(&self, projections: Vec<LocalType>) -> Result<LocalType, ProjectionError> {
        if projections.is_empty() {
            return Ok(LocalType::End);
        }

        // Filter out End types as they're neutral for merging
        let non_end: Vec<_> = projections
            .into_iter()
            .filter(|p| p != &LocalType::End)
            .collect();

        if non_end.is_empty() {
            return Ok(LocalType::End);
        }

        // Fold the merge operation over all projections
        let mut iter = non_end.into_iter();
        let mut result = iter.next().unwrap();

        for next in iter {
            result = merge_local_types(&result, &next)?;
        }

        Ok(result)
    }
}

/// Merge two LocalTypes for projection.
///
/// This is a simplified merge operation for the extended LocalType.
/// For the full merge algorithm, see the `merge` module which works with `LocalTypeR`.
pub fn merge_local_types(t1: &LocalType, t2: &LocalType) -> Result<LocalType, ProjectionError> {
    // Fast path: identical types
    if t1 == t2 {
        return Ok(t1.clone());
    }

    match (t1, t2) {
        // End merges with End
        (LocalType::End, LocalType::End) => Ok(LocalType::End),

        // End can merge with any type (End is neutral)
        // This is lenient - strict mode would reject this
        (LocalType::End, other) | (other, LocalType::End) => Ok(other.clone()),

        // Send with same target - merge into Select if messages differ
        (
            LocalType::Send {
                to: to1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Send {
                to: to2,
                message: msg2,
                continuation: cont2,
            },
        ) if to1 == to2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LocalType::Send {
                    to: to1.clone(),
                    message: msg1.clone(),
                    continuation: Box::new(merged_cont),
                })
            } else {
                // Different messages - create a Select with both options
                Ok(LocalType::Select {
                    to: to1.clone(),
                    branches: vec![
                        (msg1.name.clone(), *cont1.clone()),
                        (msg2.name.clone(), *cont2.clone()),
                    ],
                })
            }
        }

        // Receive with same source - merge into Branch if messages differ
        (
            LocalType::Receive {
                from: from1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Receive {
                from: from2,
                message: msg2,
                continuation: cont2,
            },
        ) if from1 == from2 => {
            if msg1.name == msg2.name {
                // Same message - merge continuations
                let merged_cont = merge_local_types(cont1, cont2)?;
                Ok(LocalType::Receive {
                    from: from1.clone(),
                    message: msg1.clone(),
                    continuation: Box::new(merged_cont),
                })
            } else {
                // Different messages - create a Branch with both options
                Ok(LocalType::Branch {
                    from: from1.clone(),
                    branches: vec![
                        (msg1.name.clone(), *cont1.clone()),
                        (msg2.name.clone(), *cont2.clone()),
                    ],
                })
            }
        }

        // Merge Receive into existing Branch from same source
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Receive {
                from: from2,
                message: msg2,
                continuation: cont2,
            },
        ) if from1 == from2 => {
            let mut new_branches = br1.clone();
            let msg_name = &msg2.name;
            // Check if label already exists
            if let Some((_, existing_cont)) = new_branches.iter_mut().find(|(l, _)| l == msg_name) {
                *existing_cont = merge_local_types(existing_cont, cont2)?;
            } else {
                new_branches.push((msg2.name.clone(), *cont2.clone()));
            }
            Ok(LocalType::Branch {
                from: from1.clone(),
                branches: new_branches,
            })
        }

        // Merge Branch with Branch from same source
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let merged_branches = merge_branches(br1, br2)?;
            Ok(LocalType::Branch {
                from: from1.clone(),
                branches: merged_branches,
            })
        }

        // Symmetric case: Receive into Branch
        (
            LocalType::Receive {
                from: from1,
                message: msg1,
                continuation: cont1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let mut new_branches = br2.clone();
            let msg_name = &msg1.name;
            // Check if label already exists
            if let Some((_, existing_cont)) = new_branches.iter_mut().find(|(l, _)| l == msg_name) {
                *existing_cont = merge_local_types(existing_cont, cont1)?;
            } else {
                new_branches.push((msg1.name.clone(), *cont1.clone()));
            }
            Ok(LocalType::Branch {
                from: from1.clone(),
                branches: new_branches,
            })
        }

        // Select with same target - merge branches
        (
            LocalType::Select {
                to: to1,
                branches: br1,
            },
            LocalType::Select {
                to: to2,
                branches: br2,
            },
        ) if to1 == to2 => {
            let merged_branches = merge_branches(br1, br2)?;
            Ok(LocalType::Select {
                to: to1.clone(),
                branches: merged_branches,
            })
        }

        // Branch with same source - merge branches
        (
            LocalType::Branch {
                from: from1,
                branches: br1,
            },
            LocalType::Branch {
                from: from2,
                branches: br2,
            },
        ) if from1 == from2 => {
            let merged_branches = merge_branches(br1, br2)?;
            Ok(LocalType::Branch {
                from: from1.clone(),
                branches: merged_branches,
            })
        }

        // Rec with same label
        (
            LocalType::Rec {
                label: l1,
                body: b1,
            },
            LocalType::Rec {
                label: l2,
                body: b2,
            },
        ) if l1 == l2 => {
            let merged_body = merge_local_types(b1, b2)?;
            Ok(LocalType::Rec {
                label: l1.clone(),
                body: Box::new(merged_body),
            })
        }

        // Var with same label
        (LocalType::Var(v1), LocalType::Var(v2)) if v1 == v2 => Ok(LocalType::Var(v1.clone())),

        // Loop with same condition
        (
            LocalType::Loop {
                condition: c1,
                body: b1,
            },
            LocalType::Loop {
                condition: c2,
                body: b2,
            },
        ) if conditions_equal(c1, c2) => {
            let merged_body = merge_local_types(b1, b2)?;
            Ok(LocalType::Loop {
                condition: c1.clone(),
                body: Box::new(merged_body),
            })
        }

        // All other combinations are incompatible
        _ => Err(ProjectionError::MergeFailure(
            "incompatible local types in merge".to_string(),
        )),
    }
}

/// Merge two sets of labeled branches.
fn merge_branches(
    branches1: &[(proc_macro2::Ident, LocalType)],
    branches2: &[(proc_macro2::Ident, LocalType)],
) -> Result<Vec<(proc_macro2::Ident, LocalType)>, ProjectionError> {
    use std::collections::HashMap;

    let mut result: HashMap<String, (proc_macro2::Ident, LocalType)> = HashMap::new();

    // Add all branches from the first set
    for (label, cont) in branches1 {
        result.insert(label.to_string(), (label.clone(), cont.clone()));
    }

    // Merge with branches from the second set
    for (label, cont) in branches2 {
        let label_str = label.to_string();
        if let Some((_, existing_cont)) = result.get(&label_str) {
            // Label exists - merge continuations
            let merged_cont = merge_local_types(existing_cont, cont)?;
            result.insert(label_str, (label.clone(), merged_cont));
        } else {
            // New label - add it
            result.insert(label_str, (label.clone(), cont.clone()));
        }
    }

    // Convert back to vector, sorted by label name for determinism
    let mut branches: Vec<_> = result.into_values().collect();
    branches.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));

    Ok(branches)
}

/// Compare two optional conditions for equality.
///
/// Since `Condition::Custom` contains `TokenStream` which doesn't implement
/// `PartialEq`, we compare Custom conditions conservatively (always different).
fn conditions_equal(
    c1: &Option<crate::ast::protocol::Condition>,
    c2: &Option<crate::ast::protocol::Condition>,
) -> bool {
    use crate::ast::protocol::Condition;

    match (c1, c2) {
        (None, None) => true,
        (Some(Condition::Count(n1)), Some(Condition::Count(n2))) => n1 == n2,
        (Some(Condition::RoleDecides(r1)), Some(Condition::RoleDecides(r2))) => r1 == r2,
        // Custom conditions are incomparable (TokenStream doesn't impl PartialEq)
        (Some(Condition::Custom(_)), Some(Condition::Custom(_))) => false,
        _ => false,
    }
}

// Helper to compare LocalTypes for equality
impl PartialEq for LocalType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LocalType::End, LocalType::End) => true,
            (LocalType::Var(a), LocalType::Var(b)) => a == b,
            (
                LocalType::Send {
                    to: to1,
                    message: msg1,
                    continuation: cont1,
                },
                LocalType::Send {
                    to: to2,
                    message: msg2,
                    continuation: cont2,
                },
            ) => to1 == to2 && msg1.name == msg2.name && cont1 == cont2,
            (
                LocalType::Receive {
                    from: from1,
                    message: msg1,
                    continuation: cont1,
                },
                LocalType::Receive {
                    from: from2,
                    message: msg2,
                    continuation: cont2,
                },
            ) => from1 == from2 && msg1.name == msg2.name && cont1 == cont2,
            (
                LocalType::Select {
                    to: to1,
                    branches: br1,
                },
                LocalType::Select {
                    to: to2,
                    branches: br2,
                },
            ) => {
                to1 == to2
                    && br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::Branch {
                    from: from1,
                    branches: br1,
                },
                LocalType::Branch {
                    from: from2,
                    branches: br2,
                },
            ) => {
                from1 == from2
                    && br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::LocalChoice { branches: br1 },
                LocalType::LocalChoice { branches: br2 },
            ) => {
                br1.len() == br2.len()
                    && br1
                        .iter()
                        .zip(br2.iter())
                        .all(|((l1, t1), (l2, t2))| l1 == l2 && t1 == t2)
            }
            (
                LocalType::Loop {
                    condition: c1,
                    body: b1,
                },
                LocalType::Loop {
                    condition: c2,
                    body: b2,
                },
            ) => {
                // For conditions, we compare structurally
                let cond_eq = match (c1, c2) {
                    (None, None) => true,
                    (
                        Some(crate::ast::protocol::Condition::Count(n1)),
                        Some(crate::ast::protocol::Condition::Count(n2)),
                    ) => n1 == n2,
                    (
                        Some(crate::ast::protocol::Condition::RoleDecides(r1)),
                        Some(crate::ast::protocol::Condition::RoleDecides(r2)),
                    ) => r1 == r2,
                    _ => false,
                };
                cond_eq && b1 == b2
            }
            (
                LocalType::Rec {
                    label: l1,
                    body: b1,
                },
                LocalType::Rec {
                    label: l2,
                    body: b2,
                },
            ) => l1 == l2 && b1 == b2,
            _ => false,
        }
    }
}

impl Eq for LocalType {}
