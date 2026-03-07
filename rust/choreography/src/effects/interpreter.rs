// Program interpreter for free algebra choreographic effects
//
// This module provides the interpreter that executes effect programs
// by translating them to concrete handler operations.

use async_recursion::async_recursion;
use async_trait::async_trait;
use cfg_if::cfg_if;
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
    interpreter.run(handler, endpoint, &program).await
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
    interpreter.run(handler, endpoint, &program).await
}

/// Internal interpreter state
struct Interpreter<M, R: RoleId> {
    received_values: Vec<M>,
    /// Track the last received label from an Offer effect
    last_label: Option<<R as RoleId>::Label>,
}

enum ControlFrame<'a, R: RoleId, M> {
    Effects {
        effects: &'a [Effect<R, M>],
        index: usize,
    },
    SequentialPrograms {
        programs: &'a [Program<R, M>],
        index: usize,
    },
    Repeat {
        body: &'a Program<R, M>,
        remaining: usize,
    },
    ClearLastLabel,
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
        program: &Program<R, M>,
    ) -> ChoreoResult<InterpretResult<M>>
    where
        H: ChoreoHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        let start_len = self.received_values.len();
        let final_state = match self.execute_program(handler, endpoint, program).await {
            Ok(()) => InterpreterState::Completed,
            Err(ChoreographyError::Timeout(_)) => InterpreterState::Timeout,
            Err(e) => InterpreterState::Failed(e.to_string()),
        };

        Ok(InterpretResult {
            received_values: self.received_values_since(start_len),
            final_state,
        })
    }

    async fn execute_program<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        program: &Program<R, M>,
    ) -> ChoreoResult<()>
    where
        H: ChoreoHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        let mut stack = vec![ControlFrame::Effects {
            effects: program.effects(),
            index: 0,
        }];

        while let Some(frame) = stack.pop() {
            match frame {
                ControlFrame::Effects { effects, index } => {
                    if index >= effects.len() {
                        continue;
                    }

                    stack.push(ControlFrame::Effects {
                        effects,
                        index: index + 1,
                    });
                    self.execute_base_effect(handler, endpoint, &effects[index], &mut stack)
                        .await?;
                }
                ControlFrame::SequentialPrograms { programs, index } => {
                    if let Some(program) = programs.get(index) {
                        stack.push(ControlFrame::SequentialPrograms {
                            programs,
                            index: index + 1,
                        });
                        stack.push(ControlFrame::Effects {
                            effects: program.effects(),
                            index: 0,
                        });
                    }
                }
                ControlFrame::Repeat { body, remaining } => {
                    if remaining > 0 {
                        stack.push(ControlFrame::Repeat {
                            body,
                            remaining: remaining - 1,
                        });
                        stack.push(ControlFrame::Effects {
                            effects: body.effects(),
                            index: 0,
                        });
                    }
                }
                ControlFrame::ClearLastLabel => {
                    self.last_label = None;
                }
            }
        }

        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    async fn execute_base_effect<'a, H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        effect: &'a Effect<R, M>,
        stack: &mut Vec<ControlFrame<'a, R, M>>,
    ) -> ChoreoResult<()>
    where
        H: ChoreoHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        match effect {
            Effect::Send { to, msg } => {
                handler.send(endpoint, *to, msg).await?;
            }
            Effect::Recv { from, msg_tag } => {
                tracing::debug!(
                    ?from,
                    msg_type = msg_tag.type_name(),
                    "recv effect - type casting required"
                );
                let value = self
                    .try_recv_as_type::<H, M>(handler, endpoint, *from)
                    .await?;
                self.received_values.push(value);
            }
            Effect::Choose { at, label } => {
                handler.choose(endpoint, *at, *label).await?;
                self.last_label = Some(*label);
            }
            Effect::Offer { from } => {
                let label = handler.offer(endpoint, *from).await?;
                tracing::debug!(?from, ?label, "Received offer label");
                self.last_label = Some(label);
            }
            Effect::Branch {
                choosing_role,
                branches,
            } => {
                tracing::debug!(
                    ?choosing_role,
                    branch_count = branches.len(),
                    "Executing branch effect"
                );

                let label = self.last_label.ok_or_else(|| {
                    ChoreographyError::ProtocolViolation(
                        "Branch effect requires a preceding Choose or Offer effect".to_string(),
                    )
                })?;

                let (_, selected_branch) = branches
                    .iter()
                    .find(|(branch_label, _)| branch_label == &label)
                    .ok_or_else(|| {
                        ChoreographyError::ProtocolViolation(format!(
                            "No branch found for label {label:?}"
                        ))
                    })?;

                tracing::debug!(selected_label = ?label, "Executing selected branch");
                stack.push(ControlFrame::ClearLastLabel);
                stack.push(ControlFrame::Effects {
                    effects: selected_branch.effects(),
                    index: 0,
                });
            }
            Effect::Loop { iterations, body } => {
                tracing::debug!(?iterations, "Executing loop effect");
                stack.push(ControlFrame::Repeat {
                    body,
                    remaining: iterations.unwrap_or(1),
                });
            }
            Effect::Timeout {
                at,
                dur,
                body,
                on_timeout,
            } => {
                tracing::debug!(
                    ?at,
                    ?dur,
                    has_fallback = on_timeout.is_some(),
                    "Executing timeout effect"
                );

                cfg_if! {
                    if #[cfg(target_arch = "wasm32")] {
                        let timeout_result = {
                            use futures::future::{select, Either};
                            use futures::pin_mut;
                            use wasm_timer::Delay;

                            let body_future = self.run(handler, endpoint, body);
                            let timeout = Delay::new(*dur);
                            pin_mut!(body_future);
                            pin_mut!(timeout);

                            match select(body_future, timeout).await {
                                Either::Left((result, _)) => Ok(result),
                                Either::Right(_) => Err(()),
                            }
                        };
                    } else {
                        let timeout_result =
                            tokio::time::timeout(*dur, self.run(handler, endpoint, body)).await;
                    }
                }

                match timeout_result {
                    Ok(Ok(result)) => self.propagate_nested_result(result, *dur)?,
                    Ok(Err(err)) => return Err(err),
                    Err(_) => {
                        if let Some(timeout_body) = on_timeout {
                            tracing::debug!("Timeout fired, executing fallback program");
                            let result = self.run(handler, endpoint, timeout_body).await?;
                            self.propagate_nested_result(result, *dur)?;
                        } else {
                            return Err(ChoreographyError::Timeout(*dur));
                        }
                    }
                }
            }
            Effect::Parallel { programs } => {
                tracing::debug!(program_count = programs.len(), "Executing parallel effect");
                stack.push(ControlFrame::SequentialPrograms { programs, index: 0 });
            }
            Effect::Extension(ext) => {
                tracing::debug!(
                    type_name = ext.type_name(),
                    type_id = ?ext.type_id(),
                    "Executing extension effect"
                );
                tracing::warn!(
                    "Extension effect encountered but handler does not support extensions. \
                     Use interpret_extensible() for handlers with extension support."
                );
            }
            Effect::End => {}
        }

        Ok(())
    }

    fn received_values_since(&self, start_len: usize) -> Vec<M>
    where
        M: ProgramMessage,
    {
        self.received_values[start_len..].to_vec()
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

    fn propagate_nested_result(
        &self,
        result: InterpretResult<M>,
        timeout: std::time::Duration,
    ) -> ChoreoResult<()>
    where
        M: ProgramMessage,
    {
        match result.final_state {
            InterpreterState::Completed => Ok(()),
            InterpreterState::Failed(msg) => Err(ChoreographyError::Transport(msg)),
            InterpreterState::Timeout => Err(ChoreographyError::Timeout(timeout)),
        }
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
        program: &Program<R, M>,
    ) -> ChoreoResult<InterpretResult<M>>
    where
        H: ExtensibleHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        let start_len = self.base.received_values.len();
        let final_state = match self.execute_program(handler, endpoint, program).await {
            Ok(()) => InterpreterState::Completed,
            Err(ChoreographyError::Timeout(_)) => InterpreterState::Timeout,
            Err(e) => InterpreterState::Failed(e.to_string()),
        };

        Ok(InterpretResult {
            received_values: self.base.received_values_since(start_len),
            final_state,
        })
    }

    async fn execute_program<H>(
        &mut self,
        handler: &mut H,
        endpoint: &mut H::Endpoint,
        program: &Program<R, M>,
    ) -> ChoreoResult<()>
    where
        H: ExtensibleHandler<Role = R> + Send,
        M: ProgramMessage + Serialize + DeserializeOwned + 'static,
    {
        let mut stack = vec![ControlFrame::Effects {
            effects: program.effects(),
            index: 0,
        }];

        while let Some(frame) = stack.pop() {
            match frame {
                ControlFrame::Effects { effects, index } => {
                    if index >= effects.len() {
                        continue;
                    }

                    stack.push(ControlFrame::Effects {
                        effects,
                        index: index + 1,
                    });
                    match &effects[index] {
                        Effect::Extension(ext) => {
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
                        }
                        effect => {
                            self.base
                                .execute_base_effect(handler, endpoint, effect, &mut stack)
                                .await?;
                        }
                    }
                }
                ControlFrame::SequentialPrograms { programs, index } => {
                    if let Some(program) = programs.get(index) {
                        stack.push(ControlFrame::SequentialPrograms {
                            programs,
                            index: index + 1,
                        });
                        stack.push(ControlFrame::Effects {
                            effects: program.effects(),
                            index: 0,
                        });
                    }
                }
                ControlFrame::Repeat { body, remaining } => {
                    if remaining > 0 {
                        stack.push(ControlFrame::Repeat {
                            body,
                            remaining: remaining - 1,
                        });
                        stack.push(ControlFrame::Effects {
                            effects: body.effects(),
                            index: 0,
                        });
                    }
                }
                ControlFrame::ClearLastLabel => {
                    self.base.last_label = None;
                }
            }
        }

        Ok(())
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
#[path = "interpreter_testing.rs"]
pub mod testing;

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    include!("../../tests/unit/effects/interpreter_tests.rs");
}
