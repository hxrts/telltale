# VM Simulation Scenarios

This page documents scenario configuration and middleware behavior.
It covers scenario TOML shape, fault injection, network modeling, and property monitoring.

## Scenario Schema

`Scenario` is parsed from TOML and drives scenario runs.
Core defaults are `concurrency = 1`, `seed = 0`, and `output.format = "json"`.

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

`material` is required.
`network`, `events`, and `properties` are optional.

## Scenario Example

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

[[events]]
trigger = { at_tick = 50 }
action = { type = "message_drop", probability = "0.25" }

[properties]
invariants = ["no_faults", "simplex", "buffer_bound(0,16)"]
```

Quoted decimal strings are the safest TOML form for `FixedQ32` values.
The parser also accepts compatible numeric representations.

## Fault Middleware

`FaultInjector` wraps an inner `EffectHandler`.
It handles activation, expiry, random triggers, delay queues, corruption, and crash state.

Supported actions are `MessageDrop`, `MessageDelay`, `MessageCorruption`, `NodeCrash`, and `NetworkPartition`.
Supported triggers are `Immediate`, `AtTick`, `AfterStep`, `Random`, and `OnEvent`.
Scenario trigger declarations must contain exactly one trigger condition.

## Network Middleware

`NetworkModel` typically wraps `FaultInjector` in scenario runs.
It applies partition checks, link overrides, latency sampling, loss sampling, and deferred delivery.

Per-link policies are matched by `(from_role, to_role)` plus optional active tick windows.
Loss is evaluated before latency scheduling.
Latency of zero produces immediate delivery.

## Property Monitoring

`PropertyMonitor` performs online checks by scanning newly appended events.
Built-in checks include `NoFaults`, `Simplex`, `SendRecvLiveness`, `TypeMonotonicity`, `BufferBound`, and `Liveness`.

Invariant strings are parsed by `parse_invariant`.
Predicate strings are parsed by `parse_predicate`.
`SendRecvLiveness` uses session-local event counters rather than raw global ticks.

## Checkpointing and Replay

`CheckpointStore` snapshots VM state as JSON bytes at configured intervals.
`run_with_scenario` writes checkpoint files under `artifacts/<scenario.name>/`.

Replay loads one checkpoint and one scenario.
It then runs the same middleware and property loop for selected rounds.

## Related Docs

- [VM Simulation](15_vm_simulation_overview.md)
- [VM Simulation Runner](16_vm_simulation_runner.md)
- [VM Simulation Materials](18_vm_simulation_materials.md)
