# Protocol-Machine Simulation Runner

This page documents runner behavior in `telltale-simulator`.
It covers traces, runner entry points, harness behavior, and scenario round order.

## Core Data Types

`Trace` is the sampled role-state output container.
Each `StepRecord` stores one role snapshot at one sampled step.
`ScenarioResult` adds property violations, replay artifacts, and run statistics.

```rust
pub struct StepRecord {
    pub step: u64,
    pub role: String,
    pub state: Vec<FixedQ32>,
}

pub struct Trace {
    pub records: Vec<StepRecord>,
}

pub struct ScenarioResult {
    pub trace: Trace,
    pub violations: Vec<PropertyViolation>,
    pub replay: ScenarioReplayArtifact,
    pub stats: ScenarioStats,
}
```

`step` is a simulator sampling index.
`state` contains the numeric portion of the coroutine register file.
The runner skips the first two reserved registers and samples material state starting at register `2`.

`ScenarioReplayArtifact` contains observable events, effect traces, output-condition checks, semantic audit records, and `ProtocolMachineSemanticObjects`.
These artifacts support deterministic replay and post-run validation.

## Runner Entry Points

The runner exposes three main entry points.

- `run(...)` executes one choreography and returns one sampled trace.
- `run_concurrent(...)` executes multiple choreographies on one protocol machine and returns one trace per input choreography.
- `run_with_scenario(...)` executes one choreography with scenario middleware and returns `ScenarioResult`.

Use `run_with_scenario(...)` when faults, network behavior, properties, checkpoints, or replay artifacts are required.
Use the smaller entry points when only sampled state traces are needed.

## Harness API

`SimulationHarness` is the stable integration path for external projects.
It runs `HarnessSpec` or `HarnessConfig` through a `HostAdapter`.

```rust
pub trait HostAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler;
    fn initial_states(&self, scenario: &Scenario)
        -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String>;
    fn validate_result(&self, scenario: &Scenario, result: &ScenarioResult)
        -> Result<(), String>;
}
```

`DirectAdapter` wraps an existing `EffectHandler`.
`MaterialAdapter` derives initial states from scenario material parameters and constructs the handler from `material`.
The harness does not currently consume `GeneratedEffectScenario` directly.

## Initial State Derivation

`derive_initial_states(&Scenario)` builds default per-role state vectors from `material`.
`mean_field` broadcasts one concentration vector to every role.
`hamiltonian` maps each role index to `[position, momentum]`.
`continuum_field` assigns one scalar field value per role.

The runner writes these state vectors into coroutine registers starting at register `2`.
The sampled trace reads the same numeric suffix back out.

## Sampling and Step Mapping

The simulator records samples on invocation boundaries.
It does not record after every protocol-machine instruction.

For each round, the runner counts newly appended `ObsEvent::Invoked` events.
When invoke count reaches role count, the runner records one sample for each role.
It also inserts a Mu-step sample at active-node boundaries derived from the local types.

If `steps > 0`, the runner records an initial sample at step `0` before the main loop.
If no samples were produced during execution, the runner emits one fallback sample at the last requested step index.

## Scenario Execution Order

Scenario runs use a fixed per-round order for determinism.

1. Compute `next_tick` from the protocol-machine clock.
2. Advance the fault schedule from newly visible observable events in `machine.trace()`.
3. Deliver due delayed fault messages into protocol-machine buffers.
4. Deliver network middleware queues when network simulation is enabled.
5. Update paused roles from active crash faults.
6. Execute one protocol-machine round with the selected handler domain.
7. Update trace samples from new `Invoked` events.
8. Run online property checks.
9. Attempt checkpoint persistence when the interval policy triggers.

Checkpoint persistence is best-effort.
Serialization and file-write failures do not fail the run.
`CheckpointStore` records the last persistence error internally.

## Determinism and Reproducibility

Simulator randomness is scoped to `SimRng`.
`SimRng` is seeded from `scenario.seed` and currently uses `ChaCha8`.
The protocol machine remains deterministic given the same handler outcomes and scheduler inputs.

Record ordering is stable within each sampling pass.
Replay artifacts preserve the observable and semantic data needed for deterministic post-run inspection.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Protocol-Machine Simulation Materials](504_simulation_materials.md)
- [Rust-Lean Parity](703_rust_lean_parity.md)
