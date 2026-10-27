// Source operation waits use the existing scheduler; no callback is invoked by
// a wake observation and no new operation/window is constructed on retry.
impl ThreadedProtocolMachine {
    fn try_unblock_operations(&mut self) {
        for id in self.scheduler.blocked_ids() {
            let Some(BlockReason::OperationAwait { operation_id }) =
                self.scheduler.block_reason(id).cloned()
            else {
                continue;
            };
            let wake = self.coroutine_by_id(id).map_or(true, |coroutine| {
                let original = coroutine
                    .lock()
                    .expect("threaded ProtocolMachine lock poisoned");
                crate::operation_lifecycle::await_should_wake(
                    original.operation_continuation.as_ref(),
                    &operation_id,
                    &self.outstanding_effects,
                    self.clock.tick,
                )
            });
            if wake {
                self.scheduler.unblock(id);
            }
        }
    }
}
