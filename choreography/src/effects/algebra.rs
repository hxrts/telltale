// Free algebra for choreographic effects
//
// This module provides a data representation of choreographic programs
// that can be analyzed, transformed, and interpreted separately from execution.

use crate::effects::{Label, RoleId};
use std::collections::HashSet;
use std::time::Duration;

/// A choreographic effect that can be performed by a role
#[derive(Debug, Clone, PartialEq)]
pub enum Effect<R: RoleId, M> {
    /// Send a message to another role
    Send { to: R, msg: M },

    /// Receive a message from another role
    Recv { from: R, msg_type: &'static str },

    /// Make an internal choice and broadcast the label
    Choose { at: R, label: Label },

    /// Wait for an external choice from another role
    Offer { from: R },

    /// Branch based on a choice - includes all possible continuations
    /// The choosing role has already selected via Choose effect
    /// Other roles use Offer to receive the label, then select matching branch
    Branch {
        choosing_role: R,
        branches: Vec<(Label, Program<R, M>)>,
    },

    /// Loop that executes body a fixed number of times or until a condition
    Loop {
        /// Number of iterations (None = infinite/until break)
        iterations: Option<usize>,
        body: Box<Program<R, M>>,
    },

    /// Execute a sub-program with a timeout
    Timeout {
        at: R,
        dur: Duration,
        body: Box<Program<R, M>>,
    },

    /// Execute multiple programs in parallel
    Parallel { programs: Vec<Program<R, M>> },

    /// End of program
    End,
}

/// A choreographic program as a sequence of effects
#[derive(Debug, Clone, PartialEq)]
pub struct Program<R: RoleId, M> {
    pub effects: Vec<Effect<R, M>>,
}

impl<R: RoleId, M> Program<R, M> {
    /// Create a new empty program
    #[must_use] 
    pub fn new() -> Self {
        Self {
            effects: Vec::new(),
        }
    }

    /// Add a send effect
    pub fn send(mut self, to: R, msg: M) -> Self {
        self.effects.push(Effect::Send { to, msg });
        self
    }

    /// Add a receive effect
    pub fn recv<T: 'static>(mut self, from: R) -> Self {
        self.effects.push(Effect::Recv {
            from,
            msg_type: std::any::type_name::<T>(),
        });
        self
    }

    /// Add a choice effect
    pub fn choose(mut self, at: R, label: Label) -> Self {
        self.effects.push(Effect::Choose { at, label });
        self
    }

    /// Add an offer effect
    pub fn offer(mut self, from: R) -> Self {
        self.effects.push(Effect::Offer { from });
        self
    }

    /// Add a timeout effect
    pub fn with_timeout(mut self, at: R, dur: Duration, body: Program<R, M>) -> Self {
        self.effects.push(Effect::Timeout {
            at,
            dur,
            body: Box::new(body),
        });
        self
    }

    /// Add a parallel composition effect
    #[must_use] 
    pub fn parallel(mut self, programs: Vec<Program<R, M>>) -> Self {
        self.effects.push(Effect::Parallel { programs });
        self
    }

    /// Add a branch effect with multiple labeled continuations
    pub fn branch(mut self, choosing_role: R, branches: Vec<(Label, Program<R, M>)>) -> Self {
        self.effects.push(Effect::Branch {
            choosing_role,
            branches,
        });
        self
    }

    /// Add a loop effect
    #[must_use] 
    pub fn loop_n(mut self, iterations: usize, body: Program<R, M>) -> Self {
        self.effects.push(Effect::Loop {
            iterations: Some(iterations),
            body: Box::new(body),
        });
        self
    }

    /// Add an infinite loop effect (or until break)
    #[must_use] 
    pub fn loop_inf(mut self, body: Program<R, M>) -> Self {
        self.effects.push(Effect::Loop {
            iterations: None,
            body: Box::new(body),
        });
        self
    }

    /// Mark the end of the program
    pub fn end(mut self) -> Self {
        self.effects.push(Effect::End);
        self
    }

    /// Extend this program with another program
    #[must_use] 
    pub fn then(mut self, other: Program<R, M>) -> Self {
        self.effects.extend(other.effects);
        self
    }

    /// Create a program that executes multiple programs in parallel
    #[must_use] 
    pub fn par(programs: Vec<Program<R, M>>) -> Self {
        Self::new().parallel(programs)
    }

    /// Check if the program is empty
    #[must_use] 
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    /// Get the length of the program (number of effects)
    #[must_use] 
    pub fn len(&self) -> usize {
        self.effects.len()
    }
}

impl<R: RoleId, M> Default for Program<R, M> {
    fn default() -> Self {
        Self::new()
    }
}

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
                Effect::Timeout { at, body, .. } => {
                    roles.insert(*at);
                    body.collect_roles(roles);
                }
                Effect::Parallel { programs } => {
                    for prog in programs {
                        prog.collect_roles(roles);
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
                Effect::Timeout { body, .. } => body.send_count(),
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
                Effect::Timeout { body, .. } => body.recv_count(),
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
        for effect in &self.effects {
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
                Effect::Timeout { body, .. } => body.validate()?,
                Effect::Parallel { programs } => {
                    for prog in programs {
                        prog.validate()?;
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
