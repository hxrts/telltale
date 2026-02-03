# VM Scheduling

This document explains the VM concurrency model and N-invariance guarantees.

## Concurrency Parameter N

The VM is parameterized by a concurrency level N that controls how many coroutines advance per scheduling round.

When N equals 1, execution is sequential. The scheduler picks one coroutine, executes one instruction, and re-picks. This mode is used for deterministic replay and debugging.

When N equals some value k, the scheduler picks up to k ready coroutines per round. Each executes one instruction before any re-picking occurs. Observable events are appended in pick order within each round.

When N equals infinity (or exceeds the ready queue size), all ready coroutines advance before any re-picking. This mode provides maximum parallelism within scheduler rounds.

## Scheduler Policies

The scheduler supports multiple policies for selecting coroutines from the ready queue.

The `Cooperative` policy executes coroutines until they yield. Coroutines must explicitly return control to the scheduler. This policy works well for WASM where true parallelism is unavailable.

The `RoundRobin` policy cycles through ready coroutines in order. Each coroutine gets one instruction per round before the next is selected. This provides fair scheduling across all coroutines.

The `ProgressAware` policy prefers coroutines holding progress tokens. These tokens guarantee that the associated session will eventually advance. This policy prevents starvation for coroutines with liveness guarantees.

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

The `tryUnblockReceivers` function moves blocked receivers to the ready queue when their buffer has a message. This function runs once per round before coroutine selection.

```rust
fn try_unblock_receivers(state: &mut VMState) {
    for (coro_id, reason) in state.scheduler.blocked.iter() {
        if let BlockReason::RecvWait(edge) = reason {
            if state.sessions.buffer_has_message(edge) {
                state.scheduler.ready.push(*coro_id);
            }
        }
    }
}
```

The implementation checks each blocked coroutine and moves those with available messages.

The `schedRound` function executes one round with concurrency N.

```rust
fn sched_round(n: usize, state: &mut VMState) {
    let ready = state.scheduler.pick_ready(n);
    for coro_id in ready {
        let result = exec_instr(state, coro_id);
        handle_result(state, coro_id, result);
    }
}
```

The function picks up to N ready coroutines, executes one instruction each, and handles the results.

## Block Reasons

Coroutines block for several reasons during execution.

```rust
pub enum BlockReason {
    RecvWait(Edge),
    SendWait(Edge),
    InvokeWait(HandlerId),
    CloseWait(SessionId),
}
```

The `RecvWait` reason indicates the coroutine is waiting for a message on the given edge. The `SendWait` reason indicates the buffer is full and backpressure is blocking the send. The `InvokeWait` reason indicates the coroutine is waiting for an effect handler response. The `CloseWait` reason indicates the coroutine is waiting for a session to drain.

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

The `wasm` feature configures the VM for browser environments. The cooperative backend executes all coroutines in a single thread using manual yielding. Random number generation uses the `getrandom` crate with JavaScript compatibility.

```rust
#[cfg(feature = "wasm")]
impl VMBackend for CooperativeBackend {
    fn run(&mut self, vm: &mut VM, handler: &dyn EffectHandler, fuel: usize) -> RunResult {
        for _ in 0..fuel {
            if vm.all_terminal() {
                return RunResult::Complete;
            }
            vm.sched_round(1);
        }
        RunResult::FuelExhausted
    }
}
```

The cooperative backend runs rounds with N equals 1 until completion or fuel exhaustion.

The N-invariance theorem guarantees that cooperative execution produces the same per-session traces as concurrent execution. Testing on native targets with higher N values validates correctness for WASM deployment.
