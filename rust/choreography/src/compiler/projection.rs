// Projection from global choreographies to local session types

mod merge;
mod ops;

use crate::ast::{Branch, Choreography, LocalType, MessageType, Protocol, Role, RoleParam};
use std::collections::HashMap;

pub use merge::merge_local_types;

/// Project a choreography to a local session type for a specific role
pub fn project(choreography: &Choreography, role: &Role) -> Result<LocalType, ProjectionError> {
    let mut context = ProjectionContext::new(choreography, role);
    context.project_protocol(&choreography.protocol)
}

/// Errors that can occur during projection
#[derive(Debug, thiserror::Error)]
pub enum ProjectionError {
    #[error("cannot project choice for non-participant role")]
    NonParticipantChoice,

    #[error("parallel composition not supported for role {0}")]
    UnsupportedParallel(String),

    #[error("inconsistent projections in parallel branches")]
    InconsistentParallel,

    #[error("recursive variable {0} not in scope")]
    UnboundVariable(String),

    #[error("dynamic role {role} requires runtime context for projection")]
    DynamicRoleProjection { role: String },

    #[error("symbolic role parameter '{param}' not bound in context")]
    UnboundSymbolic { param: String },

    #[error("range role index cannot be projected to concrete local type")]
    RangeProjection,

    #[error("wildcard role index requires specialized projection context")]
    WildcardProjection,

    #[error("cannot merge branches: {0}")]
    MergeFailure(String),
}

/// Context for projection algorithm
struct ProjectionContext<'a> {
    role: &'a Role,
    /// Bindings for symbolic role parameters (e.g., N -> 5)
    role_bindings: HashMap<String, u32>,
}

impl<'a> ProjectionContext<'a> {
    fn new(_choreography: &'a Choreography, role: &'a Role) -> Self {
        ProjectionContext {
            role,
            role_bindings: HashMap::new(),
        }
    }

    /// Check if this projection role matches the given protocol role
    fn role_matches(&self, protocol_role: &Role) -> Result<bool, ProjectionError> {
        // First check for exact name match
        if self.role.name() != protocol_role.name() {
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
        match (self.role.param(), protocol_role.param()) {
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
                    role: protocol_role.name().to_string(),
                })
            }
            // One parameterized, one not: no match
            (Some(_), None) | (None, Some(_)) => Ok(false),
            // Both None: already handled above
            (None, None) => Ok(true),
        }
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
                continuation,
                annotations: _,
            } => {
                // Preserve continuation structure for extension nodes.
                // Extension-local projection can be layered later once LocalType models it.
                self.project_protocol(continuation)
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
                // The Select represents the choice, and each branch's Send is part of
                // the continuation (not skipped). This matches MPST semantics where
                // the choice maker selects a branch AND sends the corresponding message.
                let mut local_branches = Vec::new();

                for branch in branches {
                    // Project the entire branch protocol including the Send
                    let local_type = self.project_protocol(&branch.protocol)?;
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

}
