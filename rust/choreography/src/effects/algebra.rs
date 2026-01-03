// Free algebra for choreographic effects
//
// This module provides a data representation of choreographic programs
// that can be analyzed, transformed, and interpreted separately from execution.

use crate::effects::extension::ExtensionEffect;
use crate::effects::{MessageTag, RoleId};
use std::any::TypeId;
use std::collections::HashSet;
use std::time::Duration;

/// A choreographic effect that can be performed by a role
#[derive(Debug)]
pub enum Effect<R: RoleId, M> {
    /// Send a message to another role
    Send { to: R, msg: M },

    /// Receive a message from another role
    Recv { from: R, msg_tag: MessageTag },

    /// Make an internal choice and broadcast the label
    Choose {
        at: R,
        label: <R as RoleId>::Label,
    },

    /// Wait for an external choice from another role
    Offer { from: R },

    /// Branch based on a choice - includes all possible continuations
    /// The choosing role has already selected via Choose effect
    /// Other roles use Offer to receive the label, then select matching branch
    Branch {
        choosing_role: R,
        branches: Vec<(<R as RoleId>::Label, Program<R, M>)>,
    },

    /// Loop that executes body a fixed number of times or until a condition
    Loop {
        /// Number of iterations (None = infinite/until break)
        iterations: Option<usize>,
        body: Box<Program<R, M>>,
    },

    /// Execute a sub-program with a timeout
    ///
    /// If `on_timeout` is Some, executes that program when timeout occurs.
    /// Otherwise, the handler decides what to do on timeout (typically error).
    Timeout {
        at: R,
        dur: Duration,
        body: Box<Program<R, M>>,
        /// Optional fallback program to execute if timeout occurs
        on_timeout: Option<Box<Program<R, M>>>,
    },

    /// Execute multiple programs in parallel
    Parallel { programs: Vec<Program<R, M>> },

    /// Extension effect for domain-specific operations
    ///
    /// Extensions are boxed trait objects that implement `ExtensionEffect`.
    /// Use `Effect::ext()` or `Program::ext()` for construction.
    ///
    /// # Type Safety
    ///
    /// Extensions are identified by `TypeId` and use trait object downcasting
    /// for type-safe access. Unknown extensions cause runtime errors (fail-fast).
    ///
    /// # Projection
    ///
    /// Extensions project based on `participating_roles()`:
    /// - Empty roles → appears in all projections
    /// - Non-empty → appears only in specified role projections
    Extension(Box<dyn ExtensionEffect<R>>),

    /// End of program
    End,
}

impl<R: RoleId, M: Clone> Clone for Effect<R, M> {
    fn clone(&self) -> Self {
        match self {
            Effect::Send { to, msg } => Effect::Send {
                to: *to,
                msg: msg.clone(),
            },
            Effect::Recv { from, msg_tag } => Effect::Recv {
                from: *from,
                msg_tag: *msg_tag,
            },
            Effect::Choose { at, label } => Effect::Choose {
                at: *at,
                label: *label,
            },
            Effect::Offer { from } => Effect::Offer { from: *from },
            Effect::Branch {
                choosing_role,
                branches,
            } => Effect::Branch {
                choosing_role: *choosing_role,
                branches: branches.clone(),
            },
            Effect::Loop { iterations, body } => Effect::Loop {
                iterations: *iterations,
                body: body.clone(),
            },
            Effect::Timeout {
                at,
                dur,
                body,
                on_timeout,
            } => Effect::Timeout {
                at: *at,
                dur: *dur,
                body: body.clone(),
                on_timeout: on_timeout.clone(),
            },
            Effect::Parallel { programs } => Effect::Parallel {
                programs: programs.clone(),
            },
            Effect::Extension(ext) => Effect::Extension(ext.clone_box()),
            Effect::End => Effect::End,
        }
    }
}

/// A choreographic program as a sequence of effects
#[derive(Debug, Clone)]
pub struct Program<R: RoleId, M> {
    effects: Vec<Effect<R, M>>,
}

/// Builder for choreographic programs that enforces structural invariants.
#[derive(Debug, Clone)]
pub struct ProgramBuilder<R: RoleId, M> {
    effects: Vec<Effect<R, M>>,
    ended: bool,
}

impl<R: RoleId, M> Program<R, M> {
    /// Create a new program builder.
    #[must_use]
    pub fn new() -> ProgramBuilder<R, M> {
        ProgramBuilder::new()
    }

    /// Create a new program builder.
    #[must_use]
    pub fn builder() -> ProgramBuilder<R, M> {
        ProgramBuilder::new()
    }

    /// Construct a program from effects after validation.
    fn from_effects(effects: Vec<Effect<R, M>>) -> Result<Self, ProgramError> {
        let program = Self { effects };
        program.validate()?;
        Ok(program)
    }

    /// Borrow the program's effects.
    #[must_use]
    pub fn effects(&self) -> &[Effect<R, M>] {
        &self.effects
    }

    /// Consume the program and return its effects.
    #[must_use]
    pub fn into_effects(self) -> Vec<Effect<R, M>> {
        self.effects
    }

    /// Extend this program with another program.
    ///
    /// # Panics
    ///
    /// Panics if the composed program violates structural invariants (e.g., End
    /// not at the final position). Use `try_then` for fallible composition.
    #[must_use]
    pub fn then(self, other: Program<R, M>) -> Program<R, M> {
        let mut effects = self.effects;
        effects.extend(other.effects);
        Program::from_effects(effects)
            .unwrap_or_else(|err| panic!("invalid program composition: {err}"))
    }

    /// Check if the program is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    /// Get the length of the program (number of effects).
    #[must_use]
    pub fn len(&self) -> usize {
        self.effects.len()
    }
}

impl<R: RoleId, M> ProgramBuilder<R, M> {
    /// Create a new empty builder.
    #[must_use]
    pub fn new() -> Self {
        Self {
            effects: Vec::new(),
            ended: false,
        }
    }

    /// Push an effect onto the builder.
    ///
    /// # Panics
    ///
    /// Panics if called after `end()` has been called, as no effects can
    /// follow the End effect.
    fn push(&mut self, effect: Effect<R, M>) {
        if self.ended {
            panic!("cannot add effects after end");
        }
        if matches!(effect, Effect::End) {
            self.ended = true;
        }
        self.effects.push(effect);
    }

    /// Add a send effect.
    pub fn send(mut self, to: R, msg: M) -> Self {
        self.push(Effect::Send { to, msg });
        self
    }

    /// Add a receive effect.
    pub fn recv<T: 'static>(mut self, from: R) -> Self {
        self.push(Effect::Recv {
            from,
            msg_tag: MessageTag::of::<T>(),
        });
        self
    }

    /// Add a choice effect.
    pub fn choose(mut self, at: R, label: <R as RoleId>::Label) -> Self {
        self.push(Effect::Choose { at, label });
        self
    }

    /// Add an offer effect.
    pub fn offer(mut self, from: R) -> Self {
        self.push(Effect::Offer { from });
        self
    }

    /// Add a timeout effect.
    pub fn with_timeout(mut self, at: R, dur: Duration, body: Program<R, M>) -> Self {
        self.push(Effect::Timeout {
            at,
            dur,
            body: Box::new(body),
            on_timeout: None,
        });
        self
    }

    /// Add a timed choice effect - races body against timeout.
    ///
    /// If body completes before timeout, executes body.
    /// If timeout fires first, executes on_timeout instead.
    /// This is the effect-level representation of timed_choice syntax.
    pub fn with_timed_choice(
        mut self,
        at: R,
        dur: Duration,
        body: Program<R, M>,
        on_timeout: Program<R, M>,
    ) -> Self {
        self.push(Effect::Timeout {
            at,
            dur,
            body: Box::new(body),
            on_timeout: Some(Box::new(on_timeout)),
        });
        self
    }

    /// Add a parallel composition effect.
    #[must_use]
    pub fn parallel(mut self, programs: Vec<Program<R, M>>) -> Self {
        self.push(Effect::Parallel { programs });
        self
    }

    /// Add a branch effect with multiple labeled continuations.
    pub fn branch(
        mut self,
        choosing_role: R,
        branches: Vec<(<R as RoleId>::Label, Program<R, M>)>,
    ) -> Self {
        self.push(Effect::Branch {
            choosing_role,
            branches,
        });
        self
    }

    /// Add a loop effect.
    #[must_use]
    pub fn loop_n(mut self, iterations: usize, body: Program<R, M>) -> Self {
        self.push(Effect::Loop {
            iterations: Some(iterations),
            body: Box::new(body),
        });
        self
    }

    /// Add an infinite loop effect (or until break).
    #[must_use]
    pub fn loop_inf(mut self, body: Program<R, M>) -> Self {
        self.push(Effect::Loop {
            iterations: None,
            body: Box::new(body),
        });
        self
    }

    /// Add a domain-specific extension effect.
    pub fn ext<E: ExtensionEffect<R> + 'static>(mut self, extension: E) -> Self {
        self.push(Effect::Extension(Box::new(extension)));
        self
    }

    /// Add multiple extension effects.
    pub fn exts<E: ExtensionEffect<R> + 'static>(
        mut self,
        extensions: impl IntoIterator<Item = E>,
    ) -> Self {
        for ext in extensions {
            self.push(Effect::Extension(Box::new(ext)));
        }
        self
    }

    /// Mark the end of the program and finalize it.
    ///
    /// # Panics
    ///
    /// Panics if the program violates structural invariants. This should not
    /// happen with normal builder usage. Use `build()` for fallible construction.
    pub fn end(mut self) -> Program<R, M> {
        self.push(Effect::End);
        self.build()
            .unwrap_or_else(|err| panic!("invalid program: {err}"))
    }

    /// Validate and build the program without appending `End`.
    pub fn build(self) -> Result<Program<R, M>, ProgramError> {
        Program::from_effects(self.effects)
    }
}

impl<R: RoleId, M> Default for Program<R, M> {
    /// Returns an empty program with no effects.
    ///
    /// An empty program is always valid, so this cannot fail.
    fn default() -> Self {
        // Empty program is always valid - no panic possible
        Self {
            effects: Vec::new(),
        }
    }
}

/// Extension effect helper methods
impl<R: RoleId, M> Effect<R, M> {
    /// Create an extension effect from any type implementing `ExtensionEffect`
    pub fn ext<E: ExtensionEffect<R> + 'static>(extension: E) -> Self {
        Effect::Extension(Box::new(extension))
    }

    /// Check if this is an extension effect of a specific type
    pub fn is_extension<E: ExtensionEffect<R> + 'static>(&self) -> bool {
        match self {
            Effect::Extension(ext) => ext.type_id() == TypeId::of::<E>(),
            _ => false,
        }
    }

    /// Extract extension data with type checking
    ///
    /// Returns `Some(&E)` if this is an extension of type `E`, `None` otherwise.
    pub fn as_extension<E: ExtensionEffect<R> + 'static>(&self) -> Option<&E> {
        match self {
            Effect::Extension(ext) => ext.as_any().downcast_ref::<E>(),
            _ => None,
        }
    }

    /// Extract mutable extension data with type checking
    pub fn as_extension_mut<E: ExtensionEffect<R> + 'static>(&mut self) -> Option<&mut E> {
        match self {
            Effect::Extension(ext) => ext.as_any_mut().downcast_mut::<E>(),
            _ => None,
        }
    }

    /// Get the TypeId of an extension effect
    pub fn extension_type_id(&self) -> Option<TypeId> {
        match self {
            Effect::Extension(ext) => Some(ext.type_id()),
            _ => None,
        }
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
