// Free algebra for choreographic effects
//
// This module provides a data representation of choreographic programs
// that can be analyzed, transformed, and interpreted separately from execution.

use crate::effects::extension::ExtensionEffect;
use crate::effects::{MessageTag, RoleId};
use std::any::TypeId;
use std::time::Duration;

#[path = "algebra_program_analysis.rs"]
mod program_analysis;
pub use program_analysis::{InterpretResult, InterpreterState, ProgramError, ProgramMessage};

/// A choreographic effect that can be performed by a role
#[derive(Debug)]
pub enum Effect<R: RoleId, M> {
    /// Send a message to another role
    Send { to: R, msg: M },

    /// Receive a message from another role
    Recv { from: R, msg_tag: MessageTag },

    /// Make an internal choice and broadcast the label
    Choose { at: R, label: <R as RoleId>::Label },

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

    /// Execute multiple programs using deterministic normalized ordering.
    ///
    /// The interpreter executes sub-programs in declaration order. This keeps
    /// behavior reproducible across runtimes while preserving the high-level
    /// "parallel composition" intent.
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
    #[allow(clippy::new_ret_no_self)]
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
    /// If `self` ends with `Effect::End`, that terminal marker is removed before
    /// appending `other`, so composition preserves the single-terminal-`End`
    /// invariant.
    ///
    /// # Panics
    ///
    /// Panics only if the composed program violates structural invariants. Use
    /// `try_then` for fallible composition.
    #[must_use]
    pub fn then(self, other: Program<R, M>) -> Program<R, M> {
        self.try_then(other)
            .unwrap_or_else(|err| panic!("invalid program composition: {err}"))
    }

    /// Fallible version of [`Program::then`].
    pub fn try_then(self, other: Program<R, M>) -> Result<Program<R, M>, ProgramError> {
        let mut effects = self.effects;
        if matches!(effects.last(), Some(Effect::End)) {
            effects.pop();
        }
        effects.extend(other.effects);
        Program::from_effects(effects)
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

impl<R: RoleId, M> Default for ProgramBuilder<R, M> {
    fn default() -> Self {
        Self::new()
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
    fn try_push(&mut self, effect: Effect<R, M>) -> Result<(), ProgramError> {
        if self.ended {
            return Err(ProgramError::InvalidStructure(
                "cannot add effects after end".to_string(),
            ));
        }
        if matches!(effect, Effect::End) {
            self.ended = true;
        }
        self.effects.push(effect);
        Ok(())
    }

    /// Fallible `send`.
    pub fn try_send(mut self, to: R, msg: M) -> Result<Self, ProgramError> {
        self.try_push(Effect::Send { to, msg })?;
        Ok(self)
    }

    /// Add a send effect.
    pub fn send(mut self, to: R, msg: M) -> Self {
        self = self
            .try_send(to, msg)
            .unwrap_or_else(|err| panic!("invalid send composition: {err}"));
        self
    }

    /// Fallible `recv`.
    pub fn try_recv<T: 'static>(mut self, from: R) -> Result<Self, ProgramError> {
        self.try_push(Effect::Recv {
            from,
            msg_tag: MessageTag::of::<T>(),
        })?;
        Ok(self)
    }

    /// Add a receive effect.
    pub fn recv<T: 'static>(mut self, from: R) -> Self {
        self = self
            .try_recv::<T>(from)
            .unwrap_or_else(|err| panic!("invalid recv composition: {err}"));
        self
    }

    /// Fallible `choose`.
    pub fn try_choose(mut self, at: R, label: <R as RoleId>::Label) -> Result<Self, ProgramError> {
        self.try_push(Effect::Choose { at, label })?;
        Ok(self)
    }

    /// Add a choice effect.
    pub fn choose(mut self, at: R, label: <R as RoleId>::Label) -> Self {
        self = self
            .try_choose(at, label)
            .unwrap_or_else(|err| panic!("invalid choose composition: {err}"));
        self
    }

    /// Fallible `offer`.
    pub fn try_offer(mut self, from: R) -> Result<Self, ProgramError> {
        self.try_push(Effect::Offer { from })?;
        Ok(self)
    }

    /// Add an offer effect.
    pub fn offer(mut self, from: R) -> Self {
        self = self
            .try_offer(from)
            .unwrap_or_else(|err| panic!("invalid offer composition: {err}"));
        self
    }

    /// Fallible `with_timeout`.
    pub fn try_with_timeout(
        mut self,
        at: R,
        dur: Duration,
        body: Program<R, M>,
    ) -> Result<Self, ProgramError> {
        self.try_push(Effect::Timeout {
            at,
            dur,
            body: Box::new(body),
            on_timeout: None,
        })?;
        Ok(self)
    }

    /// Add a timeout effect.
    pub fn with_timeout(mut self, at: R, dur: Duration, body: Program<R, M>) -> Self {
        self = self
            .try_with_timeout(at, dur, body)
            .unwrap_or_else(|err| panic!("invalid timeout composition: {err}"));
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
        self.try_push(Effect::Timeout {
            at,
            dur,
            body: Box::new(body),
            on_timeout: Some(Box::new(on_timeout)),
        })
        .unwrap_or_else(|err| panic!("invalid timed choice composition: {err}"));
        self
    }

    /// Add a parallel composition effect.
    pub fn try_parallel(mut self, programs: Vec<Program<R, M>>) -> Result<Self, ProgramError> {
        self.try_push(Effect::Parallel { programs })?;
        Ok(self)
    }

    /// Add a parallel composition effect.
    #[must_use]
    pub fn parallel(mut self, programs: Vec<Program<R, M>>) -> Self {
        self = self
            .try_parallel(programs)
            .unwrap_or_else(|err| panic!("invalid parallel composition: {err}"));
        self
    }

    /// Add a branch effect with multiple labeled continuations.
    pub fn try_branch(
        mut self,
        choosing_role: R,
        branches: Vec<(<R as RoleId>::Label, Program<R, M>)>,
    ) -> Result<Self, ProgramError> {
        self.try_push(Effect::Branch {
            choosing_role,
            branches,
        })?;
        Ok(self)
    }

    /// Add a branch effect with multiple labeled continuations.
    pub fn branch(
        mut self,
        choosing_role: R,
        branches: Vec<(<R as RoleId>::Label, Program<R, M>)>,
    ) -> Self {
        self = self
            .try_branch(choosing_role, branches)
            .unwrap_or_else(|err| panic!("invalid branch composition: {err}"));
        self
    }

    /// Add a loop effect.
    pub fn try_loop_n(
        mut self,
        iterations: usize,
        body: Program<R, M>,
    ) -> Result<Self, ProgramError> {
        self.try_push(Effect::Loop {
            iterations: Some(iterations),
            body: Box::new(body),
        })?;
        Ok(self)
    }

    /// Add a loop effect.
    #[must_use]
    pub fn loop_n(mut self, iterations: usize, body: Program<R, M>) -> Self {
        self = self
            .try_loop_n(iterations, body)
            .unwrap_or_else(|err| panic!("invalid loop composition: {err}"));
        self
    }

    /// Add an infinite loop effect (or until break).
    pub fn try_loop_inf(mut self, body: Program<R, M>) -> Result<Self, ProgramError> {
        self.try_push(Effect::Loop {
            iterations: None,
            body: Box::new(body),
        })?;
        Ok(self)
    }

    /// Add an infinite loop effect (or until break).
    #[must_use]
    pub fn loop_inf(mut self, body: Program<R, M>) -> Self {
        self = self
            .try_loop_inf(body)
            .unwrap_or_else(|err| panic!("invalid infinite loop composition: {err}"));
        self
    }

    /// Add a domain-specific extension effect.
    pub fn try_ext<E: ExtensionEffect<R> + 'static>(
        mut self,
        extension: E,
    ) -> Result<Self, ProgramError> {
        self.try_push(Effect::Extension(Box::new(extension)))?;
        Ok(self)
    }

    /// Add a domain-specific extension effect.
    pub fn ext<E: ExtensionEffect<R> + 'static>(mut self, extension: E) -> Self {
        self = self
            .try_ext(extension)
            .unwrap_or_else(|err| panic!("invalid extension composition: {err}"));
        self
    }

    /// Add multiple extension effects.
    pub fn try_exts<E: ExtensionEffect<R> + 'static>(
        mut self,
        extensions: impl IntoIterator<Item = E>,
    ) -> Result<Self, ProgramError> {
        for ext in extensions {
            self.try_push(Effect::Extension(Box::new(ext)))?;
        }
        Ok(self)
    }

    /// Add multiple extension effects.
    pub fn exts<E: ExtensionEffect<R> + 'static>(
        mut self,
        extensions: impl IntoIterator<Item = E>,
    ) -> Self {
        self = self
            .try_exts(extensions)
            .unwrap_or_else(|err| panic!("invalid extension sequence composition: {err}"));
        self
    }

    /// Mark the end of the program and finalize it.
    ///
    /// Prefer [`ProgramBuilder::try_end`] for fallible construction.
    pub fn end(self) -> Program<R, M> {
        self.try_end()
            .unwrap_or_else(|err| panic!("invalid program: {err}"))
    }

    /// Fallible variant of [`ProgramBuilder::end`].
    pub fn try_end(mut self) -> Result<Program<R, M>, ProgramError> {
        self.try_push(Effect::End)?;
        self.build()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identifiers::RoleName;
    use cfg_if::cfg_if;

    cfg_if! {
        if #[cfg(not(target_arch = "wasm32"))] {
            use proptest::prelude::*;
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum TestRole {
        Alice,
        Bob,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    enum TestLabel {
        L0,
    }

    impl crate::effects::LabelId for TestLabel {
        fn as_str(&self) -> &'static str {
            "L0"
        }

        fn from_str(label: &str) -> Option<Self> {
            (label == "L0").then_some(Self::L0)
        }
    }

    impl RoleId for TestRole {
        type Label = TestLabel;

        fn role_name(&self) -> RoleName {
            match self {
                Self::Alice => RoleName::from_static("Alice"),
                Self::Bob => RoleName::from_static("Bob"),
            }
        }
    }

    #[test]
    fn then_composes_ended_programs_without_panic() {
        let left = Program::<TestRole, String>::new()
            .send(TestRole::Bob, "hello".to_string())
            .end();
        let right = Program::<TestRole, String>::new()
            .recv::<String>(TestRole::Alice)
            .end();
        let composed = left.then(right);
        assert!(matches!(composed.effects().last(), Some(Effect::End)));
        assert_eq!(
            composed
                .effects()
                .iter()
                .filter(|effect| matches!(effect, Effect::End))
                .count(),
            1
        );
    }

    #[test]
    fn try_builder_apis_reject_effects_after_end() {
        let builder = ProgramBuilder::<TestRole, String> {
            effects: vec![Effect::End],
            ended: true,
        };
        let err = builder
            .try_send(TestRole::Bob, "late-msg".to_string())
            .expect_err("try_send must reject effects after end");
        assert!(matches!(err, ProgramError::InvalidStructure(_)));
    }

    #[test]
    fn try_end_is_fallible_and_builds_valid_program() {
        let program = Program::<TestRole, String>::builder()
            .try_send(TestRole::Bob, "hello".to_string())
            .expect("try_send should succeed")
            .try_end()
            .expect("try_end should succeed");
        assert!(matches!(program.effects().last(), Some(Effect::End)));
    }

    #[test]
    fn try_then_rejects_invalid_composition_shapes() {
        let left = Program::<TestRole, String>::builder()
            .try_end()
            .expect("left");
        let invalid_right = Program::<TestRole, String> {
            effects: vec![
                Effect::End,
                Effect::Send {
                    to: TestRole::Bob,
                    msg: "invalid".to_string(),
                },
            ],
        };

        let err = left
            .try_then(invalid_right)
            .expect_err("try_then must reject invalid end placement");
        assert!(matches!(err, ProgramError::InvalidStructure(_)));
    }

    cfg_if! {
        if #[cfg(not(target_arch = "wasm32"))] {
            proptest! {
                #[test]
                fn try_then_keeps_single_terminal_end(include_left_send in any::<bool>(), include_right_recv in any::<bool>()) {
                    let left_builder = Program::<TestRole, String>::builder();
                    let left_builder = if include_left_send {
                        left_builder.send(TestRole::Bob, "msg".to_string())
                    } else {
                        left_builder
                    };
                    let left = left_builder.end();

                    let right_builder = Program::<TestRole, String>::builder();
                    let right_builder = if include_right_recv {
                        right_builder.recv::<String>(TestRole::Alice)
                    } else {
                        right_builder
                    };
                    let right = right_builder.end();

                    let composed = left
                        .try_then(right)
                        .expect("composition should be structurally valid");
                    let end_count = composed
                        .effects()
                        .iter()
                        .filter(|effect| matches!(effect, Effect::End))
                        .count();
                    prop_assert_eq!(end_count, 1);
                    prop_assert!(matches!(composed.effects().last(), Some(Effect::End)));
                }
            }
        }
    }
}
