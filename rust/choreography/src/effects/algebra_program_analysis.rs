use super::{Effect, Program};
use crate::effects::RoleId;
use std::collections::HashSet;

/// Program analysis utilities
impl<R: RoleId, M> Program<R, M> {
    /// Get all roles involved in this program
    #[must_use]
    pub fn roles_involved(&self) -> HashSet<R> {
        let mut roles = HashSet::new();
        self.collect_roles(&mut roles);
        roles
    }

    fn collect_roles(&self, roles: &mut HashSet<R>) {
        for effect in &self.effects {
            match effect {
                Effect::Send { to, .. } => {
                    roles.insert(*to);
                }
                Effect::Recv { from, .. } => {
                    roles.insert(*from);
                }
                Effect::Choose { at, .. } => {
                    roles.insert(*at);
                }
                Effect::Offer { from } => {
                    roles.insert(*from);
                }
                Effect::Branch {
                    choosing_role,
                    branches,
                } => {
                    roles.insert(*choosing_role);
                    for (_, prog) in branches {
                        prog.collect_roles(roles);
                    }
                }
                Effect::Loop { body, .. } => {
                    body.collect_roles(roles);
                }
                Effect::Timeout {
                    at,
                    body,
                    on_timeout,
                    ..
                } => {
                    roles.insert(*at);
                    body.collect_roles(roles);
                    if let Some(timeout_body) = on_timeout {
                        timeout_body.collect_roles(roles);
                    }
                }
                Effect::Parallel { programs } => {
                    for prog in programs {
                        prog.collect_roles(roles);
                    }
                }
                Effect::Extension(ext) => {
                    for role in ext.participating_roles() {
                        roles.insert(role);
                    }
                }
                Effect::End => {}
            }
        }
    }

    /// Count the number of send operations
    #[must_use]
    pub fn send_count(&self) -> usize {
        self.effects
            .iter()
            .map(|e| match e {
                Effect::Send { .. } => 1,
                Effect::Branch { branches, .. } => branches
                    .iter()
                    .map(|(_, p)| p.send_count())
                    .max()
                    .unwrap_or(0),
                Effect::Loop { body, .. } => body.send_count(),
                Effect::Timeout {
                    body, on_timeout, ..
                } => {
                    let body_count = body.send_count();
                    let timeout_count = on_timeout.as_ref().map_or(0, |p| p.send_count());
                    body_count.max(timeout_count)
                }
                Effect::Parallel { programs } => programs.iter().map(Program::send_count).sum(),
                _ => 0,
            })
            .sum()
    }

    /// Count the number of receive operations
    #[must_use]
    pub fn recv_count(&self) -> usize {
        self.effects
            .iter()
            .map(|e| match e {
                Effect::Recv { .. } => 1,
                Effect::Branch { branches, .. } => branches
                    .iter()
                    .map(|(_, p)| p.recv_count())
                    .max()
                    .unwrap_or(0),
                Effect::Loop { body, .. } => body.recv_count(),
                Effect::Timeout {
                    body, on_timeout, ..
                } => {
                    let body_count = body.recv_count();
                    let timeout_count = on_timeout.as_ref().map_or(0, |p| p.recv_count());
                    body_count.max(timeout_count)
                }
                Effect::Parallel { programs } => programs.iter().map(Program::recv_count).sum(),
                _ => 0,
            })
            .sum()
    }

    /// Check if the program has any timeout effects
    #[must_use]
    pub fn has_timeouts(&self) -> bool {
        self.effects
            .iter()
            .any(|e| matches!(e, Effect::Timeout { .. }))
    }

    /// Check if the program has any parallel effects
    #[must_use]
    pub fn has_parallel(&self) -> bool {
        self.effects
            .iter()
            .any(|e| matches!(e, Effect::Parallel { .. }))
    }

    /// Validate that the program is well-formed
    pub fn validate(&self) -> Result<(), ProgramError> {
        for (idx, effect) in self.effects.iter().enumerate() {
            match effect {
                Effect::Branch { branches, .. } => {
                    if branches.is_empty() {
                        return Err(ProgramError::InvalidStructure(
                            "Branch must have at least one branch".to_string(),
                        ));
                    }
                    for (_, prog) in branches {
                        prog.validate()?;
                    }
                }
                Effect::Loop { body, .. } => body.validate()?,
                Effect::Timeout {
                    body, on_timeout, ..
                } => {
                    body.validate()?;
                    if let Some(timeout_body) = on_timeout {
                        timeout_body.validate()?;
                    }
                }
                Effect::Parallel { programs } => {
                    if programs.is_empty() {
                        return Err(ProgramError::InvalidStructure(
                            "Parallel must contain at least one program".to_string(),
                        ));
                    }
                    for prog in programs {
                        prog.validate()?;
                    }
                }
                Effect::Extension(_) => {
                    // Extensions are always valid - validation happens at runtime
                }
                Effect::End => {
                    if idx + 1 != self.effects.len() {
                        return Err(ProgramError::InvalidStructure(
                            "End must be the final effect".to_string(),
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

/// Errors that can occur during program construction or analysis
#[derive(Debug, Clone, PartialEq)]
pub enum ProgramError {
    /// Program contains invalid structure
    InvalidStructure(String),

    /// Program has unbalanced send/receive operations
    UnbalancedCommunication,

    /// Program contains unreachable effects
    UnreachableCode,
}

impl std::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProgramError::InvalidStructure(msg) => write!(f, "Invalid program structure: {msg}"),
            ProgramError::UnbalancedCommunication => {
                write!(f, "Unbalanced send/receive operations")
            }
            ProgramError::UnreachableCode => write!(f, "Program contains unreachable code"),
        }
    }
}

impl std::error::Error for ProgramError {}

/// Result of interpreting a program
#[derive(Debug, Clone)]
pub struct InterpretResult<M> {
    /// Messages received during execution
    pub received_values: Vec<M>,

    /// Final state of the interpreter
    pub final_state: InterpreterState,
}

/// State of the program interpreter
#[derive(Debug, Clone, PartialEq)]
pub enum InterpreterState {
    /// Program completed successfully
    Completed,

    /// Program was interrupted by timeout
    Timeout,

    /// Program failed with an error
    Failed(String),
}

/// Type alias for any message type that can be used in programs
pub trait ProgramMessage: Clone + Send + Sync + std::fmt::Debug {}
impl<T: Clone + Send + Sync + std::fmt::Debug> ProgramMessage for T {}
