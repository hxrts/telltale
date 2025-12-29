// Program interpreter for free algebra choreographic effects
//
// This module provides the interpreter that executes effect programs
// by translating them to concrete handler operations.

use async_recursion::async_recursion;
use async_trait::async_trait;
use serde::{de::DeserializeOwned, Serialize};
use std::any::TypeId;
use std::collections::HashMap;

use crate::effects::algebra::{Effect, InterpretResult, InterpreterState, Program, ProgramMessage};
use crate::effects::registry::ExtensibleHandler;
use crate::effects::{ChoreoHandler, ChoreographyError, Result, RoleId};

/// Interpret a choreographic program using a concrete handler
pub async fn interpret<H, R, M>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<R, M>,
) -> Result<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R> + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
{
    let mut interpreter = Interpreter::new();
    interpreter.run(handler, endpoint, program).await
}

/// Interpret a choreographic program using an extensible handler
///
/// This version supports handlers that implement `ExtensibleHandler` and can
/// dispatch extension effects to registered handlers.
pub async fn interpret_extensible<H, R, M>(
    handler: &mut H,
    endpoint: &mut <H as ExtensibleHandler>::Endpoint,
    program: Program<R, M>,
) -> Result<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R, Endpoint = <H as ExtensibleHandler>::Endpoint>
        + ExtensibleHandler
        + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
{
    let mut interpreter = ExtensibleInterpreter::new();
    interpreter.run(handler, endpoint, program).await
}

/// Internal interpreter state
struct Interpreter<M> {
    received_values: Vec<M>,
    #[allow(dead_code)]
    type_registry: HashMap<TypeId, String>,
    /// Track the last received label from an Offer effect
    last_label: Option<crate::effects::Label>,
}

impl<M> Interpreter<M> {
    fn new() -> Self {
        Self {
            received_values: Vec::new(),
            type_registry: HashMap::new(),
            last_label: None,
        }
    }

    #[async_recursion]
    async fn run<H, R>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        program: Program<R, M>,
    ) -> Result<InterpretResult<M>>
    where
        H: ChoreoHandler<Role = R> + Send,
        R: RoleId,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        for effect in program.effects {
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
    async fn execute_effect<H, R>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        effect: Effect<R, M>,
    ) -> Result<()>
    where
        H: ChoreoHandler<Role = R> + Send,
        R: RoleId,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        match effect {
            Effect::Send { to, msg } => {
                handler.send(endpoint, to, &msg).await?;
            }

            Effect::Recv { from, msg_type } => {
                // Type-erased receive: attempt to receive as expected type M
                // Type-specific interpreters or sophisticated type registry needed for full polymorphism
                tracing::debug!(?from, ?msg_type, "recv effect - type casting required");

                // Attempt to receive as the expected type M
                match self
                    .try_recv_as_type::<H, R, M>(handler, endpoint, from)
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

            Effect::Timeout { at, dur, body } => {
                // Execute the body with a timeout
                tracing::debug!(?at, ?dur, "Executing timeout effect");

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
                        return Err(ChoreographyError::Timeout(dur));
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

    async fn try_recv_as_type<H, R, T>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        from: R,
    ) -> Result<T>
    where
        H: ChoreoHandler<Role = R>,
        R: RoleId,
        T: DeserializeOwned + Send,
    {
        handler.recv(endpoint, from).await
    }
}

/// Extensible interpreter that supports extension effects
struct ExtensibleInterpreter<M> {
    base: Interpreter<M>,
}

impl<M> ExtensibleInterpreter<M> {
    fn new() -> Self {
        Self {
            base: Interpreter::new(),
        }
    }

    #[async_recursion]
    async fn run<H, R>(
        &mut self,
        handler: &mut H,
        endpoint: &mut <H as ExtensibleHandler>::Endpoint,
        program: Program<R, M>,
    ) -> Result<InterpretResult<M>>
    where
        H: ChoreoHandler<Role = R, Endpoint = <H as ExtensibleHandler>::Endpoint>
            + ExtensibleHandler
            + Send,
        R: RoleId,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        for effect in program.effects {
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
    async fn execute_effect<H, R>(
        &mut self,
        handler: &mut H,
        endpoint: &mut <H as ExtensibleHandler>::Endpoint,
        effect: Effect<R, M>,
    ) -> Result<()>
    where
        H: ChoreoHandler<Role = R, Endpoint = <H as ExtensibleHandler>::Endpoint>
            + ExtensibleHandler
            + Send,
        R: RoleId,
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
    ) -> Result<InterpretResult<M>>
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
        async_trait, ChoreoHandler, ChoreographyError, DeserializeOwned, Result, RoleId, Serialize,
    };
    use std::collections::VecDeque;

    /// A mock handler that records operations and provides scripted responses
    pub struct MockHandler<R: RoleId> {
        #[allow(dead_code)]
        role: R,
        recorded_operations: Vec<MockOperation<R>>,
        scripted_responses: VecDeque<MockResponse>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub enum MockOperation<R: RoleId> {
        Send { to: R, msg_type: String },
        Recv { from: R },
        Choose { at: R, label: String },
        Offer { from: R },
    }

    #[derive(Debug, Clone)]
    pub enum MockResponse {
        Message(Vec<u8>),
        Label(String),
        Error(String),
    }

    impl<R: RoleId> MockHandler<R> {
        pub fn new(role: R) -> Self {
            Self {
                role,
                recorded_operations: Vec::new(),
                scripted_responses: VecDeque::new(),
            }
        }

        pub fn add_response(&mut self, response: MockResponse) {
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
        ) -> Result<()> {
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
        ) -> Result<M> {
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
            label: crate::effects::Label,
        ) -> Result<()> {
            self.recorded_operations.push(MockOperation::Choose {
                at,
                label: label.0.to_string(),
            });
            Ok(())
        }

        async fn offer(
            &mut self,
            _ep: &mut Self::Endpoint,
            from: Self::Role,
        ) -> Result<crate::effects::Label> {
            self.recorded_operations.push(MockOperation::Offer { from });

            if let Some(MockResponse::Label(label)) = self.scripted_responses.pop_front() {
                Ok(crate::effects::Label(Box::leak(label.into_boxed_str())))
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
        ) -> Result<T>
        where
            F: std::future::Future<Output = Result<T>> + Send,
        {
            body.await
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effects::Label;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
    enum TestRole {
        Alice,
        Bob,
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
            .choose(TestRole::Alice, Label("continue"))
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
