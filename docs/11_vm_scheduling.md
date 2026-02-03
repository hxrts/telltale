# VM Scheduling

This document explains the VM concurrency model and N-invariance guarantees.

## Concurrency Parameter N

The VM is parameterized by a concurrency level N that controls how many coroutines advance per scheduling round.

When N equals 1, execution is sequential. The scheduler picks one coroutine, executes one instruction, and re-picks. This mode is used for deterministic replay and debugging.

When N equals some value k, the scheduler picks up to k ready coroutines per round. Each executes one instruction before any re-picking occurs. Observable events are appended in pick order within each round.

When N equals infinity (or exceeds the ready queue size), all ready coroutines advance before any re-picking. This mode provides maximum parallelism within scheduler rounds.

## Scheduler Policies

The scheduler supports multiple policies for selecting coroutines from the ready queue.

The `Cooperative` policy is single-threaded round-robin with explicit `Yield` points. It works well for WASM where true parallelism is unavailable.

The `RoundRobin` policy cycles through ready coroutines in order. Each coroutine gets one instruction per round before the next is selected. This provides fair scheduling across all coroutines.

The `ProgressAware` policy is intended to prefer coroutines holding progress tokens. The current Rust scheduler treats it the same as round robin, matching the placeholder implementation.

```rust
pub enum SchedPolicy {
    Cooperative,
    RoundRobin,
    ProgressAware,
}
```

The policy enum defines the available scheduling strategies.

## Scheduling Round

Each scheduling round consists of distinct phases.

The `try_unblock_receivers` helper moves blocked receivers to the ready queue when their session buffers have messages. This function runs once per round before coroutine selection.

```rust
fn try_unblock_receivers(vm: &mut VM) {
    for coro_id in vm.scheduler.blocked_ids() {
        if let Some(BlockReason::RecvWait { endpoint }) = vm.scheduler.block_reason(coro_id).cloned()
        {
            if let Some(session) = vm.sessions.get(endpoint.sid) {
                let has_msg = session
                    .roles
                    .iter()
                    .any(|sender| sender != &endpoint.role && session.has_message(sender, &endpoint.role));
                if has_msg {
                    vm.scheduler.unblock(coro_id);
                }
            }
        }
    }
}
```

The implementation checks each blocked coroutine and moves those with available messages.

The `schedRound` function executes one round with concurrency N.

```rust
fn step_round(vm: &mut VM, handler: &dyn EffectHandler, n: usize) {
    vm.try_unblock_receivers();
    for _ in 0..n {
        if let Some(coro_id) = vm.scheduler.schedule() {
            let result = vm.exec_instr(coro_id, handler);
            vm.handle_result(coro_id, result);
        }
    }
}
```

The function picks up to N ready coroutines, executes one instruction each, and handles the results.

## Block Reasons

Coroutines block for several reasons during execution.

```rust
pub enum BlockReason {
    RecvWait { endpoint: Endpoint },
    SendWait { endpoint: Endpoint },
    InvokeWait,
    CloseWait { sid: SessionId },
}
```

The `RecvWait` reason indicates the coroutine is waiting for a message on the given endpoint. The `SendWait` reason indicates the buffer is full and backpressure is blocking the send. The `InvokeWait` reason indicates the coroutine is waiting for an effect handler response. The `CloseWait` reason indicates the coroutine is waiting for a session close to complete.

## N-Invariance

The key correctness property is that per-session traces are invariant over N and scheduling policy.

Within a single session, the concurrency parameter N does not affect correctness. Intra-session coroutines have causal dependencies that enforce ordering. A send must complete before the corresponding receive can succeed.

Across sessions, N changes the interleaving of events but not the per-session observable trace. The `cross_session_diamond` theorem states that coroutines from different sessions can execute in either order with the same result.

```rust
// Per-session trace extraction
fn filter_by_session(trace: &ObsTrace, sid: SessionId) -> ObsTrace {
    trace.iter().filter(|e| e.session_id == sid).collect()
}

// Normalize by dropping tick fields
fn normalize_trace(trace: &ObsTrace) -> ObsTrace {
    trace.iter().map(|e| e.without_tick()).collect()
}
```

The `normalizeTrace` function erases tick fields for comparison. Two runs with different N values produce equivalent normalized per-session traces.

The handler contract is required for N-invariance. The effect handler must be deterministic and session-local. It may depend on session state, role, label, and payload. It must not read global time, random state, or cross-session mutable state.

## WASM Compatibility

WASM targets use single-threaded cooperative execution.

The `wasm` feature configures the VM for browser environments. The default `VMConfig` uses `SchedPolicy::Cooperative` and the `getrandom` crate for JavaScript-compatible randomness. The N-invariance theorem guarantees that cooperative execution produces the same per-session traces as concurrent execution. Testing on native targets with higher N values validates correctness for WASM deployment.
