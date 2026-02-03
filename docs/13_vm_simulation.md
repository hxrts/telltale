# VM Simulation

This document covers observable events, trace collection, and simulation integration.

## Observable Events

The VM records observable events during execution for debugging and verification.

```rust
pub enum ObsEvent {
    Sent { tick: u64, session: SessionId, from: Role, to: Role, label: Label },
    Received { tick: u64, session: SessionId, from: Role, to: Role, label: Label },
    Opened { tick: u64, session: SessionId, roles: Vec<Role> },
    Closed { tick: u64, session: SessionId },
    Invoked { tick: u64, session: SessionId, role: Role, action: String },
    Halted { tick: u64, coro: usize },
    Faulted { tick: u64, coro: usize, error: Fault },
}
```

Every event carries a `tick` field from the simulation clock. The `Sent` and `Received` events record message passing. The `Opened` and `Closed` events mark session lifecycle boundaries. The `Invoked` event logs effect handler calls. The `Halted` and `Faulted` events indicate coroutine termination.

## Simulation Clock

The VM carries a deterministic simulation clock for timing.

```rust
pub struct SimClock {
    pub tick: u64,
    pub time: Duration,
    pub tick_duration: Duration,
}

impl SimClock {
    pub fn advance(&mut self) {
        self.tick += 1;
        self.time += self.tick_duration;
    }
}
```

The clock advances once per scheduling round. The `tick` field is a monotonic counter. The `time` field tracks simulated duration.

All observable events receive the current tick at emission time. This provides a total ordering of events within a simulation run. The tick values enable reasoning about event sequencing.

## Trace Collection

The VM collects events into an observable trace during execution.

```rust
impl VM {
    pub fn trace(&self) -> &Vec<ObsEvent> {
        &self.obs_trace
    }

    pub fn filter_by_session(&self, sid: SessionId) -> Vec<&ObsEvent> {
        self.obs_trace
            .iter()
            .filter(|e| e.session_id() == Some(sid))
            .collect()
    }
}
```

The `trace` method returns the complete event log. The `filter_by_session` method extracts events for a specific session.

Per-session filtering is essential for N-invariance verification. Different concurrency levels produce different global interleavings. The per-session subsequence remains identical across all N values.

## Trace Normalization

Trace normalization enables comparison across different execution runs.

```rust
pub fn normalize_trace(trace: &[ObsEvent]) -> Vec<NormalizedEvent> {
    trace.iter().map(|e| e.without_tick()).collect()
}
```

The function erases tick fields from all events. The resulting trace captures only the event sequence without timing information.

Two runs with different N values or scheduling policies produce equivalent normalized per-session traces. This property is the N-invariance theorem. Tests verify invariance by comparing normalized traces from multiple runs.

## VM Runner Integration

The `telltale-simulator` crate wraps the VM for simulation and testing.

```rust
pub struct ChoreographySpec {
    pub local_types: Vec<(Role, LocalTypeR)>,
    pub global_type: GlobalType,
    pub initial_states: HashMap<Role, Value>,
}

pub fn run_vm(
    spec: &ChoreographySpec,
    handler: &dyn EffectHandler,
    fuel: usize,
) -> Result<Trace, SimError>
```

The `ChoreographySpec` struct packages a choreography for simulation. The `run_vm` function executes the spec and returns the collected trace.

Multiple choreographies can execute concurrently in the same VM.

```rust
pub fn run_vm_concurrent(
    specs: &[ChoreographySpec],
    handler: &dyn EffectHandler,
    fuel: usize,
) -> Result<Vec<Trace>, SimError>
```

The concurrent runner loads all specs into a single VM instance. Sessions from different specs remain isolated. The function returns per-spec traces after execution.

## Testing Patterns

Several patterns support reliable simulation testing.

Deterministic replay requires seeded random number generation. Effect handlers that need randomness accept an explicit seed. The same seed produces the same execution trace.

```rust
let handler = SeededHandler::new(42);
let trace1 = run_vm(&spec, &handler, 1000)?;

let handler = SeededHandler::new(42);
let trace2 = run_vm(&spec, &handler, 1000)?;

assert_eq!(normalize_trace(&trace1), normalize_trace(&trace2));
```

The test verifies that identical seeds produce identical traces.

N-invariance testing compares traces from different concurrency levels.

```rust
let trace_n1 = run_with_concurrency(&spec, 1)?;
let trace_n4 = run_with_concurrency(&spec, 4)?;
let trace_ninf = run_with_concurrency(&spec, usize::MAX)?;

assert_eq!(
    normalize_by_session(&trace_n1, sid),
    normalize_by_session(&trace_n4, sid)
);
assert_eq!(
    normalize_by_session(&trace_n1, sid),
    normalize_by_session(&trace_ninf, sid)
);
```

The test verifies that per-session traces are invariant over N.

See [Effect Handlers](07_effect_handlers.md) for handler implementation. See [VM Scheduling](11_vm_scheduling.md) for concurrency details.
