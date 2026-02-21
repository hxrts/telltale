# VM Simulation

This document defines the current `telltale-simulator` runtime surface.
It describes how the simulator drives `telltale-vm`, records state traces, applies middleware, and checks runtime properties.

## Scope

The simulator crate is split into focused modules.
The primary modules are `runner`, `scenario`, `trace`, `fault`, `network`, `property`, `checkpoint`, `distributed`, `analysis`, `material`, `ising`, `hamiltonian`, `continuum`, `rng`, and `value_conv`.

This page documents behavior that is implemented in `rust/simulator/src` and `rust/vm/src/vm.rs`.
It does not restate instruction-level VM semantics.

## Core Data Types

The simulator output type is `Trace`.
Each entry is a per-role snapshot of numeric registers at a sampled step.

```rust
pub struct StepRecord {
    pub step: u64,
    pub role: String,
    pub state: Vec<FixedQ32>,
}

pub struct Trace {
    pub records: Vec<StepRecord>,
}
```

`step` is a simulator sampling index, not a raw VM instruction count.
`state` is fixed-point numeric state extracted from VM registers.

`Trace` helpers include `record()`, `records_for_role()`, and `final_state()`.
These helpers are read-only conveniences over `records`.

## VM Observable Events Used by the Simulator

The simulator reads VM `ObsEvent` values from `vm.trace()`.
All `ObsEvent` variants carry a `tick` field.

Current variants are listed here.

- `Sent`
- `Received`
- `Offered`
- `Chose`
- `Opened`
- `Closed`
- `EpochAdvanced`
- `Halted`
- `Invoked`
- `Acquired`
- `Released`
- `Transferred`
- `Forked`
- `Joined`
- `Aborted`
- `Tagged`
- `Checked`
- `Faulted`
- `OutputConditionChecked`

The runner sampling logic keys on `Invoked` counts.
Fault trigger matching uses a subset that includes `sent`, `received`, `opened`, `closed`, `invoked`, `halted`, and `faulted`.

## Numeric Encoding and Register Layout

Simulator numeric state uses `FixedQ32`.
The simulator converts between `FixedQ32` and VM `Value` through `value_conv`.

State values are written into register slots starting at index `2`.
Registers `0` and `1` stay reserved for VM runtime conventions.

```text
q32:<fixed_bits>
q32vec:<fixed_bits,fixed_bits,...>
```

`FixedQ32` values are encoded as `Value::Str` with these prefixes.
`registers_to_f64s()` skips the first two registers and decodes numeric payloads from the remainder.

## Runner APIs

The simulator exposes three public run entrypoints.
The signatures use `BTreeMap<String, Vec<FixedQ32>>` for deterministic role ordering.

```rust
pub struct ChoreographySpec {
    pub local_types: BTreeMap<String, LocalTypeR>,
    pub global_type: GlobalType,
    pub initial_states: BTreeMap<String, Vec<FixedQ32>>,
}

pub fn run(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Trace, String>

pub fn run_concurrent(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Vec<Trace>, String>

pub fn run_with_scenario(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String>
```

`run()` executes one choreography and returns one `Trace`.
`run_concurrent()` loads multiple choreographies into one VM and returns traces in input order.
`run_with_scenario()` adds fault and network middleware, optional checkpointing, and property monitoring.

`run()` and `run_concurrent()` call `vm.step()` repeatedly.
`run_with_scenario()` calls `vm.step_round(..., scenario.concurrency as usize)`.

`ScenarioResult` also includes replay and observability payloads.
The replay payload includes `obs_trace`, `effect_trace`, and `output_condition_trace`.
The stats payload includes seed, concurrency, executed rounds, final tick, and checkpoint write count.

## Sampling Model and Step Mapping

The simulator does not record after every VM instruction.
It records when `Invoked` counts reach role-based thresholds.

Each run computes `num_roles` from session coroutines.
The runner increments an `invoke_count` from new `ObsEvent::Invoked` events.
When `invoke_count >= num_roles`, one simulator step record is emitted for every role.
A secondary counter tracks active nodes per role through `active_per_role()`.
This function traverses the local type and follows the first branch at each `Send` or `Recv` node.
When the active counter reaches that value, the runner inserts an additional sample that represents a Mu-step boundary.

Both `run()` and `run_concurrent()` pre-record an initial sample at `step = 0` when `steps > 0`.
All runners keep a guard bound of `steps * num_roles * 10` VM iterations to prevent unbounded loops.
If no sample was emitted, the runner records one final fallback sample.

## Scenario Format

`Scenario` is parsed from TOML.
Default values are `concurrency = 1`, `seed = 0`, and `output.format = "json"`.

```rust
pub struct Scenario {
    pub name: String,
    pub roles: Vec<String>,
    pub steps: u64,
    pub concurrency: u64,
    pub seed: u64,
    pub network: Option<NetworkSpec>,
    pub material: MaterialParams,
    pub events: Vec<EventSpec>,
    pub properties: Option<PropertiesSpec>,
    pub checkpoint_interval: Option<u64>,
    pub output: OutputConfig,
}
```

`network` defines latency, variance, probabilistic loss, static partition windows, and role-to-role link overrides.
`events` defines fault injection triggers and actions.
`properties` defines invariants and liveness checks.

`material` is required and selects one of `mean_field`, `hamiltonian`, or `continuum_field`.
`output.file` and `output.format` are parsed, but trace writing is handled by caller tooling rather than `run_with_scenario()`.

### Scenario Example

```toml
name = "mean_field_fault_window"
roles = ["A", "B"]
steps = 200
concurrency = 2
seed = 42
checkpoint_interval = 25

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

[[network.links]]
from = "A"
to = "B"
start_tick = 30
end_tick = 120
enabled = true
base_latency_ms = 40
latency_variance = "0.15"
loss_probability = "0.05"

[[network.links]]
from = "B"
to = "A"
enabled = false

[[events]]
trigger = { at_tick = 50 }
action = { type = "message_drop", probability = "0.25" }

[properties]
invariants = ["no_faults", "simplex", "buffer_bound(0,16)"]
```

Quoted decimal strings are the safest TOML form for `FixedQ32` values.
The parser also supports compatible numeric forms through `FixedQ32` deserialization.

## Fault Middleware

`FaultInjector` wraps an inner `EffectHandler`.
It manages scheduled activation, expiry, random triggering, delay queues, message corruption, and node crash state.
Supported fault actions are `MessageDrop`, `MessageDelay`, `MessageCorruption`, `NodeCrash`, and `NetworkPartition`.
Supported triggers are `Immediate`, `AtTick`, `AfterStep`, `Random`, and `OnEvent`.

`crashed_roles()` is used by the runner through `vm.set_paused_roles(...)`.
Delayed messages are retried when `inject_message` returns `WouldBlock` or `Full`.
`Scenario::fault_schedule()` maps scenario events to `FaultSchedule` with `max_concurrent = usize::MAX`.
Scenario trigger declarations must contain exactly one condition.

## Network Middleware

`NetworkModel` wraps an inner handler, which is usually `FaultInjector` in scenario runs.
It applies partition checks, per-link overrides, loss probability, sampled latency, and deferred delivery queues.

Per-link policies are matched by `(from_role,to_role)` and active tick window.
Per-link `enabled = false` drops traffic for that directed link while active.
Per-link latency and loss override global defaults when set.
Loss is evaluated before latency scheduling after link policy resolution.
When latency resolves to zero ticks, send decisions remain immediate delivery.
When latency is nonzero, the message is queued and `SendDecision::Defer` is returned.

`NetworkModel::deliver()` injects due messages and retries blocked injections one tick later.
The same retry rule is used by the fault injector delivery queue.

## Scenario Execution Order

`run_with_scenario()` uses this per-round order.
The order matters for deterministic behavior.

1. Compute `next_tick` from `vm.clock().tick + 1`.
2. Advance fault schedule by passing new VM trace events into `tick(...)`.
3. Deliver due delayed messages into VM buffers with `vm.inject_message(...)`.
4. If network is configured, run both inner fault delivery and outer network delivery.
5. Update paused roles from active crash faults.
6. Execute `vm.step_round(handler, scenario.concurrency as usize)`.
7. Update simulator trace sampling from new `Invoked` events.
8. Run property checks with `PropertyMonitor::check(...)`.
9. Optionally checkpoint VM state.

This order is mirrored by the replay CLI in `rust/simulator/src/bin/replay.rs`.
That tool resumes from a serialized VM checkpoint and re-applies scenario middleware.

## Property Monitoring

`PropertyMonitor` performs online checks during simulation.
The monitor only scans newly appended events on each call.

- `NoFaults`
- `Simplex`
- `SendRecvLiveness { sid, bound }`
- `TypeMonotonicity { sid }`
- `BufferBound { sid, max }`
- `Liveness { name, precondition, goal, bound }`

- `no_faults`
- `simplex`
- `tick < N`, `tick <= N`, `tick > N`, `tick >= N`, `tick == N`
- `distance_to_equilibrium < X` and related comparison operators

`SendRecvLiveness` uses session-local event counters, not raw global clock ticks.
`TypeMonotonicity` ignores recursive local types that contain `Var`.

### Property Example

```toml
[properties]
invariants = [
  "no_faults",
  "simplex",
  "send_recv_liveness(0,20)",
  "type_monotonicity(0)",
  "buffer_bound(0,32)",
]

[[properties.liveness]]
name = "equilibrium_reached"
precondition = "tick >= 50"
goal = "distance_to_equilibrium < 0.05"
bound = 200
```

Invariant names are parsed by `parse_invariant()`.
Liveness expressions are parsed by `parse_predicate()`.

## Checkpointing and Replay

`CheckpointStore` snapshots VM state as JSON bytes at configured intervals.
`run_with_scenario()` creates `artifacts/<scenario.name>/checkpoint_<tick>.json` when checkpointing is enabled.

Checkpoint persistence is best effort.
In-memory checkpoint records remain available through `restore()` and `nearest_before()`.

The replay binary reads one checkpoint plus one scenario.
It then runs the same middleware and property loop for a selected number of rounds.

## Distributed Simulation

`DistributedSimBuilder` constructs an outer VM plus nested per-site inner VMs through `NestedVMHandler`.
Each site owns a set of `CodeImage` protocols and its own effect handler instance.

The builder requires exact set equality between site names and outer protocol roles.
Build fails if the inter-site protocol is missing or role sets differ.
The builder also supports `outer_concurrency(...)` and `inner_rounds_per_step(...)`.

`DistributedSimulation::run(max_rounds)` drives the outer VM at configured outer concurrency.
Inner VM progress is triggered through the nested handler integration.
`NestedVMHandler` executes configured rounds-per-step for each site callback.

## Material Handlers

The simulator includes three effect handlers that update state in `step(...)`.
All handlers read and write state via fixed-point conversion helpers.

- `IsingHandler` advances a two-species mean-field state with Euler integration.
- `IsingHandler` preserves simplex constraints through clamp and renormalization.
- `HamiltonianHandler` tracks peer position and force data in mutex maps.
- `HamiltonianHandler` applies leapfrog integration once per four-phase message cycle.
- `ContinuumFieldHandler` tracks peer field values and runs a two-phase diffusion update.
- `ContinuumFieldHandler` integrates only on the receive-complete phase.

## Post-run Analysis

`analysis` provides trace checks for physics and numerical invariants.
Checks return structured pass status with readable messages.

Available checks include `check_conservation`, `check_simplex`, `check_convergence`, and `check_energy_conservation`.
`validate()` runs standard conservation, simplex, and per-role convergence checks.

These checks are post-hoc utilities.
They do not modify VM state or middleware behavior.

## Determinism and Reproducibility

Simulator randomness is isolated in `SimRng`.
`SimRng` is seeded from scenario seed and supports deterministic `fork()` for independent middleware streams.

The VM core remains deterministic with respect to effect outcomes.
Random behavior enters only through simulator middleware decisions.

Record ordering is stable for role snapshots within each recording pass.
Cross-session snapshot timing in `run_concurrent()` depends on `Invoked` events and session mapping order.

## Test and Conformance Coverage

The simulator test suite includes `end_to_end.rs`, `regression.rs`, and `distributed.rs`.
These tests exercise Lean projection integration, trace equivalence, analysis checks, and nested VM behavior.

`regression.rs` compares Lean-projected and Rust-projected traces for mean-field and Hamiltonian scenarios.
The comparisons use fixed-point tolerance and step plus role indexing.
`end_to_end.rs` validates full pipeline behavior from global type to projection to simulation to analysis.
`distributed.rs` validates nested site traces and outer plus inner integration behavior.

## Current Limits and Sharp Edges

`run_with_scenario()` returns in-memory trace artifacts and stats.
It still does not write scenario output files by itself.

`active_per_role()` follows the first branch when estimating active node count.
This is intentional in current runner logic.

`Trigger::AfterStep` is evaluated against current tick in the fault injector.
It is not a separate per-session step counter.

## Related Docs

- [Choreography Effect Handlers](08_effect_handlers.md)
- [Effect Handlers and Session Types](10_effect_session_bridge.md)
- [VM Architecture](11_vm_architecture.md)
- [VM Parity](15_vm_parity.md)
