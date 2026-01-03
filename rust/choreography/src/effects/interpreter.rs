// Program interpreter for free algebra choreographic effects
//
// This module provides the interpreter that executes effect programs
// by translating them to concrete handler operations.

use async_recursion::async_recursion;
use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};

use crate::effects::algebra::{Effect, InterpretResult, InterpreterState, Program, ProgramMessage};
use crate::effects::registry::ExtensibleHandler;
use crate::effects::{ChoreoHandler, ChoreoResult, ChoreographyError, RoleId};

/// Interpret a choreographic program using a concrete handler
pub async fn interpret<H, R, M>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<R, M>,
) -> ChoreoResult<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R> + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
{
    let mut interpreter: Interpreter<M, R> = Interpreter::new();
    interpreter.run(handler, endpoint, program).await
}

/// Interpret a choreographic program using an extensible handler
///
/// This version supports handlers that implement `ExtensibleHandler` and can
/// dispatch extension effects to registered handlers.
pub async fn interpret_extensible<H, R, M>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<R, M>,
) -> ChoreoResult<InterpretResult<M>>
where
    H: ExtensibleHandler<Role = R> + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
{
    let mut interpreter: ExtensibleInterpreter<M, R> = ExtensibleInterpreter::new();
    interpreter.run(handler, endpoint, program).await
}

/// Internal interpreter state
struct Interpreter<M, R: RoleId> {
    received_values: Vec<M>,
    /// Track the last received label from an Offer effect
    last_label: Option<<R as RoleId>::Label>,
}

impl<M, R: RoleId> Interpreter<M, R> {
    fn new() -> Self {
        Self {
            received_values: Vec::new(),
            last_label: None,
        }
    }

    #[async_recursion]
    async fn run<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        program: Program<R, M>,
    ) -> ChoreoResult<InterpretResult<M>>
    where
        H: ChoreoHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        for effect in program.into_effects() {
            match self.execute_effect(handler, endpoint, effect).await {
                Ok(()) => continue,
                Err(ChoreographyError::Timeout(_)) => {
                    return Ok(InterpretResult {
                        received_values: self.received_values.clone(),
                        final_state: InterpreterState::Timeout,
                    });
                }
                Err(e) => {
                    return Ok(InterpretResult {
                        received_values: self.received_values.clone(),
                        final_state: InterpreterState::Failed(e.to_string()),
                    });
                }
            }
        }

        Ok(InterpretResult {
            received_values: self.received_values.clone(),
            final_state: InterpreterState::Completed,
        })
    }

    #[async_recursion]
    async fn execute_effect<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        effect: Effect<R, M>,
    ) -> ChoreoResult<()>
    where
        H: ChoreoHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        match effect {
            Effect::Send { to, msg } => {
                handler.send(endpoint, to, &msg).await?;
            }

            Effect::Recv { from, msg_tag } => {
                // Type-erased receive: attempt to receive as expected type M
                // Type-specific interpreters or sophisticated type registry needed for full polymorphism
                tracing::debug!(
                    ?from,
                    msg_type = msg_tag.type_name(),
                    "recv effect - type casting required"
                );

                // Attempt to receive as the expected type M
                match self
                    .try_recv_as_type::<H, M>(handler, endpoint, from)
                    .await
                {
                    Ok(value) => {
                        self.received_values.push(value);
                    }
                    Err(e) => return Err(e),
                }
            }

            Effect::Choose { at, label } => {
                handler.choose(endpoint, at, label).await?;
                // Store the chosen label for subsequent Branch effects
                self.last_label = Some(label);
            }

            Effect::Offer { from } => {
                let label = handler.offer(endpoint, from).await?;
                // Store the received label for control flow decisions in subsequent Branch effects
                tracing::debug!(?from, ?label, "Received offer label");
                self.last_label = Some(label);
            }

            Effect::Branch {
                choosing_role,
                branches,
            } => {
                // Handle branching based on choice
                // The choosing role has already executed Choose effect to select a branch
                // Other roles use Offer effect to receive the label
                tracing::debug!(
                    ?choosing_role,
                    branch_count = branches.len(),
                    "Executing branch effect"
                );

                // Get the label from the last Choose/Offer effect
                let label = self.last_label.ok_or_else(|| {
                    ChoreographyError::ProtocolViolation(
                        "Branch effect requires a preceding Choose or Offer effect".to_string(),
                    )
                })?;

                // Find the matching branch by label
                let selected_branch = branches
                    .iter()
                    .find(|(branch_label, _)| branch_label == &label)
                    .ok_or_else(|| {
                        ChoreographyError::ProtocolViolation(format!(
                            "No branch found for label {label:?}"
                        ))
                    })?;

                tracing::debug!(selected_label = ?label, "Executing selected branch");

                // Execute the selected branch
                let result = self
                    .run(handler, endpoint, selected_branch.1.clone())
                    .await?;
                self.received_values.extend(result.received_values);

                // Clear the label after use
                self.last_label = None;

                if !matches!(result.final_state, InterpreterState::Completed) {
                    match result.final_state {
                        InterpreterState::Failed(msg) => {
                            return Err(ChoreographyError::Transport(msg));
                        }
                        InterpreterState::Timeout => {
                            return Err(ChoreographyError::Timeout(
                                std::time::Duration::from_secs(0),
                            ));
                        }
                        InterpreterState::Completed => {}
                    }
                }
            }

            Effect::Loop { iterations, body } => {
                // Execute loop body specified number of times
                tracing::debug!(?iterations, "Executing loop effect");

                let count = iterations.unwrap_or(1); // Default to 1 iteration if None
                for iteration in 0..count {
                    tracing::debug!(iteration, "Loop iteration");
                    let result = self.run(handler, endpoint, (*body).clone()).await?;
                    self.received_values.extend(result.received_values);

                    if !matches!(result.final_state, InterpreterState::Completed) {
                        match result.final_state {
                            InterpreterState::Failed(msg) => {
                                return Err(ChoreographyError::Transport(msg));
                            }
                            InterpreterState::Timeout => {
                                return Err(ChoreographyError::Timeout(
                                    std::time::Duration::from_secs(0),
                                ));
                            }
                            InterpreterState::Completed => {}
                        }
                    }
                }
            }

            Effect::Timeout {
                at,
                dur,
                body,
                on_timeout,
            } => {
                // Execute the body with a timeout
                tracing::debug!(?at, ?dur, has_fallback = on_timeout.is_some(), "Executing timeout effect");

                #[cfg(not(target_arch = "wasm32"))]
                let timeout_result = {
                    tokio::time::timeout(dur, Box::pin(self.run(handler, endpoint, *body))).await
                };

                #[cfg(target_arch = "wasm32")]
                let timeout_result = {
                    use futures::future::{select, Either};
                    use futures::pin_mut;
                    use wasm_timer::Delay;

                    let body_future = Box::pin(self.run(handler, endpoint, *body));
                    let timeout = Delay::new(dur);
                    pin_mut!(body_future);
                    pin_mut!(timeout);

                    match select(body_future, timeout).await {
                        Either::Left((result, _)) => Ok(result),
                        Either::Right(_) => Err(()),
                    }
                };

                match timeout_result {
                    Ok(Ok(result)) => {
                        // Success - merge the results
                        self.received_values.extend(result.received_values);
                        if !matches!(result.final_state, InterpreterState::Completed) {
                            // Propagate non-completed state by updating our state
                            // and returning an error for Failed/Timeout
                            match result.final_state {
                                InterpreterState::Failed(msg) => {
                                    return Err(ChoreographyError::Transport(msg));
                                }
                                InterpreterState::Timeout => {
                                    return Err(ChoreographyError::Timeout(dur));
                                }
                                InterpreterState::Completed => {}
                            }
                        }
                    }
                    Ok(Err(e)) => return Err(e),
                    Err(_) => {
                        // Timeout occurred
                        if let Some(timeout_body) = on_timeout {
                            // Execute the fallback program (timed choice)
                            tracing::debug!("Timeout fired, executing fallback program");
                            let result = self.run(handler, endpoint, *timeout_body).await?;
                            self.received_values.extend(result.received_values);
                            if !matches!(result.final_state, InterpreterState::Completed) {
                                match result.final_state {
                                    InterpreterState::Failed(msg) => {
                                        return Err(ChoreographyError::Transport(msg));
                                    }
                                    InterpreterState::Timeout => {
                                        return Err(ChoreographyError::Timeout(dur));
                                    }
                                    InterpreterState::Completed => {}
                                }
                            }
                        } else {
                            // No fallback - return timeout error
                            return Err(ChoreographyError::Timeout(dur));
                        }
                    }
                }
            }

            Effect::Parallel { programs } => {
                // Execute programs in parallel using tokio::spawn
                // Note: This requires cloning handler state which may not always be possible
                // For handlers that don't support concurrent access, execute sequentially
                tracing::debug!(program_count = programs.len(), "Executing parallel effect");

                // Try to execute in parallel, fall back to sequential if needed
                // Sequential execution is still correct, just less performant
                for program in programs {
                    let result = self.run(handler, endpoint, program).await?;
                    self.received_values.extend(result.received_values);

                    match result.final_state {
                        InterpreterState::Failed(msg) => {
                            return Err(ChoreographyError::Transport(msg));
                        }
                        InterpreterState::Timeout => {
                            return Err(ChoreographyError::Timeout(
                                std::time::Duration::from_secs(0),
                            ));
                        }
                        InterpreterState::Completed => {}
                    }
                }
            }

            Effect::Extension(ext) => {
                // Dispatch extension to registered handler
                // This requires the handler to implement ExtensibleHandler
                tracing::debug!(
                    type_name = ext.type_name(),
                    type_id = ?ext.type_id(),
                    "Executing extension effect"
                );

                // We need to check if handler implements ExtensibleHandler
                // For now, we'll add a separate interpret function for extensible handlers
                // and keep this one for backward compatibility
                tracing::warn!(
                    "Extension effect encountered but handler does not support extensions. \
                     Use interpret_extensible() for handlers with extension support."
                );
            }

            Effect::End => {
                // Nothing to do for end effect
            }
        }

        Ok(())
    }

    async fn try_recv_as_type<H, T>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        from: R,
    ) -> ChoreoResult<T>
    where
        H: ChoreoHandler<Role = R>,
        T: DeserializeOwned + Send,
    {
        handler.recv(endpoint, from).await
    }
}

/// Extensible interpreter that supports extension effects
struct ExtensibleInterpreter<M, R: RoleId> {
    base: Interpreter<M, R>,
}

impl<M, R: RoleId> ExtensibleInterpreter<M, R> {
    fn new() -> Self {
        Self {
            base: Interpreter::new(),
        }
    }

    #[async_recursion]
    async fn run<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        program: Program<R, M>,
    ) -> ChoreoResult<InterpretResult<M>>
    where
        H: ExtensibleHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        for effect in program.into_effects() {
            match self.execute_effect(handler, endpoint, effect).await {
                Ok(()) => continue,
                Err(ChoreographyError::Timeout(_)) => {
                    return Ok(InterpretResult {
                        received_values: self.base.received_values.clone(),
                        final_state: InterpreterState::Timeout,
                    });
                }
                Err(e) => {
                    return Ok(InterpretResult {
                        received_values: self.base.received_values.clone(),
                        final_state: InterpreterState::Failed(e.to_string()),
                    });
                }
            }
        }

        Ok(InterpretResult {
            received_values: self.base.received_values.clone(),
            final_state: InterpreterState::Completed,
        })
    }

    #[async_recursion]
    async fn execute_effect<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        effect: Effect<R, M>,
    ) -> ChoreoResult<()>
    where
        H: ExtensibleHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        // Handle extension effects
        if let Effect::Extension(ref ext) = effect {
            tracing::debug!(
                type_name = ext.type_name(),
                type_id = ?ext.type_id(),
                "Dispatching extension effect to handler"
            );

            handler
                .extension_registry()
                .handle(endpoint, ext.as_ref())
                .await
                .map_err(|e| ChoreographyError::Transport(e.to_string()))?;

            return Ok(());
        }

        // Delegate all non-extension effects to the base interpreter
        self.base.execute_effect(handler, endpoint, effect).await
    }
}

/// Extension trait to add program interpretation to handlers
#[async_trait]
pub trait ChoreoHandlerExt: ChoreoHandler + Sized {
    /// Run a choreographic program using this handler
    async fn run_program<M>(
        &mut self,
        endpoint: &mut Self::Endpoint,
        program: Program<Self::Role, M>,
    ) -> ChoreoResult<InterpretResult<M>>
    where
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
        Self: Send,
    {
        interpret(self, endpoint, program).await
    }
}

// Blanket implementation for all ChoreoHandlers
impl<T: ChoreoHandler> ChoreoHandlerExt for T {}

/// Utilities for testing and simulation
pub mod testing {
    use super::{
        async_trait, ChoreoHandler, ChoreoResult, ChoreographyError, DeserializeOwned, RoleId, Serialize,
    };
    use std::collections::VecDeque;

    /// A mock handler that records operations and provides scripted responses
    pub struct MockHandler<R: RoleId> {
        /// The role this handler represents (kept for debugging/future use)
        _role: R,
        recorded_operations: Vec<MockOperation<R>>,
        scripted_responses: VecDeque<MockResponse<<R as RoleId>::Label>>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum MockOperation<R: RoleId> {
        Send { to: R, msg_type: String },
        Recv { from: R },
        Choose {
            at: R,
            label: <R as RoleId>::Label,
        },
        Offer { from: R },
    }

    #[derive(Debug, Clone)]
    pub enum MockResponse<L> {
        Message(Vec<u8>),
        Label(L),
        Error(String),
    }

    impl<R: RoleId> MockHandler<R> {
        pub fn new(role: R) -> Self {
            Self {
                _role: role,
                recorded_operations: Vec::new(),
                scripted_responses: VecDeque::new(),
            }
        }

        pub fn add_response(&mut self, response: MockResponse<<R as RoleId>::Label>) {
            self.scripted_responses.push_back(response);
        }

        pub fn operations(&self) -> &[MockOperation<R>] {
            &self.recorded_operations
        }

        pub fn clear_operations(&mut self) {
            self.recorded_operations.clear();
        }
    }

    #[async_trait]
    impl<R: RoleId + 'static> ChoreoHandler for MockHandler<R> {
        type Role = R;
        type Endpoint = ();

        async fn send<M: Serialize + Send + Sync>(
            &mut self,
            _ep: &mut Self::Endpoint,
            to: Self::Role,
            _msg: &M,
        ) -> ChoreoResult<()> {
            self.recorded_operations.push(MockOperation::Send {
                to,
                msg_type: std::any::type_name::<M>().to_string(),
            });
            Ok(())
        }

        async fn recv<M: DeserializeOwned + Send>(
            &mut self,
            _ep: &mut Self::Endpoint,
            from: Self::Role,
        ) -> ChoreoResult<M> {
            self.recorded_operations.push(MockOperation::Recv { from });

            if let Some(MockResponse::Message(bytes)) = self.scripted_responses.pop_front() {
                bincode::deserialize(&bytes)
                    .map_err(|e| ChoreographyError::Serialization(e.to_string()))
            } else {
                Err(ChoreographyError::Transport(
                    "No scripted response available".into(),
                ))
            }
        }

        async fn choose(
            &mut self,
            _ep: &mut Self::Endpoint,
            at: Self::Role,
            label: <Self::Role as RoleId>::Label,
        ) -> ChoreoResult<()> {
            self.recorded_operations
                .push(MockOperation::Choose { at, label });
            Ok(())
        }

        async fn offer(
            &mut self,
            _ep: &mut Self::Endpoint,
            from: Self::Role,
        ) -> ChoreoResult<<Self::Role as RoleId>::Label> {
            self.recorded_operations.push(MockOperation::Offer { from });

            if let Some(MockResponse::Label(label)) = self.scripted_responses.pop_front() {
                Ok(label)
            } else {
                Err(ChoreographyError::Transport(
                    "No scripted label available".into(),
                ))
            }
        }

        async fn with_timeout<F, T>(
            &mut self,
            _ep: &mut Self::Endpoint,
            _at: Self::Role,
            _dur: std::time::Duration,
            body: F,
        ) -> ChoreoResult<T>
        where
            F: std::future::Future<Output = ChoreoResult<T>> + Send,
        {
            body.await
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::{LabelId, RoleId};
    use crate::identifiers::RoleName;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestRole {
        Alice,
        Bob,
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestLabel {
        Continue,
    }

    impl LabelId for TestLabel {
        fn as_str(&self) -> &'static str {
            match self {
                TestLabel::Continue => "continue",
            }
        }

        fn from_str(label: &str) -> Option<Self> {
            match label {
                "continue" => Some(TestLabel::Continue),
                _ => None,
            }
        }
    }

    impl RoleId for TestRole {
        type Label = TestLabel;

        fn role_name(&self) -> RoleName {
            match self {
                TestRole::Alice => RoleName::from_static("Alice"),
                TestRole::Bob => RoleName::from_static("Bob"),
            }
        }
    }

    #[derive(Clone, Debug, PartialEq, Serialize, serde::Deserialize)]
    struct TestMessage(String);

    #[tokio::test]
    async fn test_simple_program() {
        let program = Program::new()
            .send(TestRole::Bob, TestMessage("hello".into()))
            .recv::<TestMessage>(TestRole::Bob)
            .end();

        let mut handler = testing::MockHandler::new(TestRole::Alice);
        handler.add_response(testing::MockResponse::Message(
            bincode::serialize(&TestMessage("reply".into())).unwrap(),
        ));

        let mut endpoint = ();
        let result = interpret(&mut handler, &mut endpoint, program)
            .await
            .unwrap();

        assert_eq!(result.final_state, InterpreterState::Completed);
        assert_eq!(result.received_values.len(), 1);
    }

    #[test]
    fn test_program_analysis() {
        let program = Program::new()
            .send(TestRole::Bob, TestMessage("hello".into()))
            .recv::<TestMessage>(TestRole::Bob)
            .choose(TestRole::Alice, TestLabel::Continue)
            .end();

        assert_eq!(program.send_count(), 1);
        assert_eq!(program.recv_count(), 1);
        assert!(!program.has_timeouts());
        assert!(!program.has_parallel());

        let roles = program.roles_involved();
        assert!(roles.contains(&TestRole::Alice));
        assert!(roles.contains(&TestRole::Bob));
    }
}
