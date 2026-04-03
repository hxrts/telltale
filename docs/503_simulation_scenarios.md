# Protocol-Machine Simulation Scenarios

This page documents scenario configuration and middleware behavior.
It covers the TOML schema, fault injection, network modeling, properties, checkpointing, and current limits.

## Scenario Schema

`Scenario` is parsed from TOML and drives `run_with_scenario(...)`.
`seed` defaults to `0`.
`material` is optional and is only required by built-in material-driven surfaces such as `MaterialAdapter::from_scenario(...)`, `derive_initial_states(&Scenario)`, and the simulator CLI binaries.
Execution defaults are resolved through `Scenario.execution`.
`backend = "auto"` resolves to the authoritative canonical lane with `scheduler_concurrency = 1` and `worker_threads = 1`.
Theorem-facing interpretation is configured separately through `Scenario.theorem`.

```rust
pub struct Scenario {
    pub name: String,
    pub roles: Vec<String>,
    pub steps: u64,
    pub execution: ExecutionSpec,
    pub seed: u64,
    pub network: Option<NetworkSpec>,
    pub material: Option<MaterialParams>,
    pub events: Vec<EventSpec>,
    pub properties: Option<PropertiesSpec>,
    pub checkpoint_interval: Option<u64>,
    pub theorem: TheoremProfileSpec,
}
```

`network`, `material`, `events`, `properties`, and `checkpoint_interval` are optional.

```rust
pub struct ExecutionSpec {
    pub backend: ExecutionBackend,
    pub scheduler_concurrency: Option<u64>,
    pub worker_threads: Option<u64>,
}
```

`scheduler_concurrency` controls how much scheduler work one simulator round may admit.
`worker_threads` controls physical parallelism for the threaded backend only.
Canonical execution requires both values to resolve to `1`.
Threaded execution with `scheduler_concurrency = 1` remains exact with respect to the canonical lane, while `scheduler_concurrency > 1` is only authoritative modulo the declared concurrency envelope.

```rust
pub struct TheoremProfileSpec {
    pub scheduler_profile: TheoremSchedulerProfile,
    pub envelope_profile: TheoremEnvelopeProfile,
    pub assumption_bundle: TheoremAssumptionBundle,
}
```

The theorem block does not change runtime execution.
It declares which theorem-side contract the caller wants the run to be interpreted under.
The simulator resolves that declaration against the actual execution regime and reports eligibility in `ScenarioStats.theorem_profile` and `ScenarioReplayArtifact.theorem_profile`.

## Scenario Example

```toml
name = "mean_field_fault_window"
roles = ["A", "B"]
steps = 200
seed = 42
checkpoint_interval = 25

[execution]
backend = "threaded"
scheduler_concurrency = 2
worker_threads = 4

[material]
layer = "mean_field"

[material.params]
beta = "1.5"
species = ["up", "down"]
initial_state = ["0.6", "0.4"]
step_size = "0.01"

[network]
base_latency_ms = 20
latency_variance = "0.10"
loss_probability = "0.02"

[[events]]
trigger = { at_tick = 50 }
action = { type = "message_drop", probability = "0.25" }

[properties]
invariants = ["no_faults", "simplex", "buffer_bound(0,16)"]
```

Quoted decimal strings are the safest TOML form for `FixedQ32` values.
The parser also accepts compatible numeric representations.

## Fault Middleware

`FaultInjector` wraps the inner handler.
It manages activation, expiry, random triggers, delayed delivery, corruption, and crash state.

Supported actions are `MessageDrop`, `MessageDelay`, `MessageCorruption`, `NodeCrash`, and `NetworkPartition`.
Supported triggers are `Immediate`, `AtTick`, `AfterStep`, `Random`, and `OnEvent`.
If a trigger declaration sets no trigger field, it defaults to `Immediate`.

An event must not set more than one trigger field at once.
The parser rejects multi-trigger declarations.
`Trigger::AfterStep` is evaluated against logical round count rather than raw tick count.

## Network Middleware

`NetworkModel` wraps `FaultInjector` when network simulation is enabled.
It applies partition checks, link overrides, latency sampling, loss sampling, and deferred delivery.

Per-link policies match directed `(from, to)` pairs.
A link policy is active only inside its optional tick window.
When multiple link policies match, the last matching entry wins.

Loss is evaluated before latency scheduling.
Dropped messages never enter the in-flight queue.
Zero effective latency produces immediate delivery.

## Property Monitoring

`PropertyMonitor` performs online checks by scanning newly appended observable events and machine state.
Built-in checks include `NoFaults`, `Simplex`, `SendRecvLiveness`, `TypeMonotonicity`, `BufferBound`, and `Liveness`.

Invariant strings are parsed by `parse_property`.
Predicate strings are parsed by `parse_predicate`.
`SendRecvLiveness` uses session-local event counters rather than raw global ticks.

## Checkpointing and Replay

`CheckpointStore` snapshots protocol-machine state as JSON bytes at configured intervals.
When `checkpoint_interval` is set, `run_with_scenario(...)` writes checkpoint files under `artifacts/<scenario.name>/`.
Replay loads a checkpoint and re-executes the same shared middleware loop used by fresh scenario runs.

Checkpoint snapshots currently require the canonical backend.
Threaded scenario runs still emit replay artifacts such as observable events, effect traces, and semantic objects, but checkpoint serialization remains canonical-only.

Checkpoint persistence is best-effort.
Serialization or file-write failures do not fail the run.
`CheckpointStore::last_persist_error()` exposes the last recorded persistence error.

## Current Limits

Generated effect-family helpers (e.g. `record_return()`, `with_delay_ms()`, `record_stale_late_result()`) are separate programmatic APIs.
They are not a TOML scenario feature.
They are also not yet wired into `SimulationHarness`.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Runner](502_simulation_runner.md)
- [Protocol-Machine Simulation Materials](504_simulation_materials.md)
