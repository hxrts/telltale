// Existing cooperative owner adapts its actual canonical storage to the shared
// source-operation transition. It never consults a diagnostic trace's last row.
impl ProtocolMachine {
    fn commit_operation_lifecycle(
        &mut self,
        coro_idx: usize,
        action: crate::operation_lifecycle::OperationAction,
    ) -> Result<(), Fault> {
        use crate::operation_lifecycle::{
            execute_operation_action, transition_fault, OperationExecution,
        };
        let sid = self.coroutines[coro_idx].session_id;
        let session = self.sessions.get(sid).ok_or_else(|| Fault::Invoke {
            failure: EffectFailure::contract_violation("original operation session is absent"),
        })?;
        let execution = execute_operation_action(
            &mut self.coroutines[coro_idx],
            session,
            self.operation_instances.as_mut_slice(),
            self.progress_contracts.as_mut_slice(),
            self.outstanding_effects.as_mut_slice(),
            self.clock.tick,
            action,
        )
        .map_err(transition_fault)?;
        let advance = match execution {
            OperationExecution::Advance => true,
            OperationExecution::AwaitPending => {
                let operation_id = self.coroutines[coro_idx]
                    .operation_continuation
                    .as_ref()
                    .expect("validated original operation")
                    .operation_id
                    .clone();
                self.coroutines[coro_idx].status =
                    CoroStatus::Blocked(BlockReason::OperationAwait { operation_id });
                false
            }
            OperationExecution::Begun(record, progress) => {
                self.operation_instances
                    .push_canonical(record, &self.config.observability_retention);
                self.progress_contracts
                    .push_canonical(progress, &self.config.observability_retention);
                true
            }
        };
        if advance {
            self.coroutines[coro_idx].pc += 1;
            self.coroutines[coro_idx].status = CoroStatus::Ready;
        }
        Ok(())
    }
}

impl ProtocolMachine {
    fn try_unblock_operations(&mut self) {
        for id in self.sched.blocked_ids() {
            let Some(BlockReason::OperationAwait { operation_id }) =
                self.sched.block_reason(id).cloned()
            else {
                continue;
            };
            let wake = self
                .coroutines
                .iter()
                .find(|coroutine| coroutine.id == id)
                .is_none_or(|coroutine| {
                    crate::operation_lifecycle::await_should_wake(
                        coroutine.operation_continuation.as_ref(),
                        &operation_id,
                        self.outstanding_effects.as_slice(),
                        self.clock.tick,
                    )
                });
            if wake {
                self.sched.unblock(id);
            }
        }
    }
}

impl ProtocolMachine {
    fn validate_source_operation_context(&self, coro_idx: usize) -> Result<(), Fault> {
        let coroutine = &self.coroutines[coro_idx];
        let required = self
            .programs
            .get(coroutine.program_id)
            .is_some_and(|program| {
                crate::operation_lifecycle::requires_operation_context(program, coroutine.pc)
            });
        if required
            && coroutine
                .operation_continuation
                .as_ref()
                .is_none_or(|original| original.resolved || original.invalidated)
        {
            return Err(Fault::Invoke {
                failure: EffectFailure::contract_violation(
                    "source child has no actual original enclosing continuation",
                ),
            });
        }
        let session = self
            .sessions
            .get(coroutine.session_id)
            .ok_or_else(|| Fault::Invoke {
                failure: EffectFailure::contract_violation("original source session is absent"),
            })?;
        crate::operation_lifecycle::validate_enclosing_operation(
            coroutine,
            session,
            self.operation_instances.as_slice(),
            self.progress_contracts.as_slice(),
            self.clock.tick,
        )
        .map_err(crate::operation_lifecycle::transition_fault)
    }
}
