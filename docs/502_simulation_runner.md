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

`ScenarioReplayArtifact` contains observable events, effect traces, output-condition checks, semantic audit records, `ProtocolMachineSemanticObjects`, and a canonical simulator reconfiguration trace.
These artifacts support deterministic replay and post-run validation.

## Runner Entry Points

The runner exposes three main entry points.

- `run(...)` executes one choreography and returns one sampled trace.
- `run_multi_session_canonical(...)` executes multiple choreographies on one canonical protocol machine and returns one trace per input choreography.
- `run_with_scenario(...)` executes one choreography with scenario middleware and returns `ScenarioResult`.

Use `run_with_scenario(...)` when faults, network behavior, properties, checkpoints, or replay artifacts are required.
Use the smaller entry points when only sampled state traces are needed.

`run_with_scenario(...)` resolves execution through `Scenario.execution`.
That resolution decides:

- which machine backend to use
- how many scheduler lanes one round may use
- how many worker threads the threaded backend may use

`Scenario.execution.backend = "auto"` now resolves to the authoritative canonical backend.
That means `scheduler_concurrency = 1` and `worker_threads = 1` unless the scenario explicitly requests a different backend.

`ScenarioStats.execution_regime` records the proof-side concurrency class for the resolved run:

- `canonical_exact`
- `threaded_exact`
- `threaded_envelope_bounded`

`scheduler_concurrency` may change semantics.
`worker_threads` must not change authoritative outputs for a fixed threaded scheduler configuration.

`Scenario.theorem` is resolved separately from `Scenario.execution`.
It carries:

- `scheduler_profile`
- `envelope_profile`
- `assumption_bundle`

The resolved theorem profile is emitted in both `ScenarioStats` and `ScenarioReplayArtifact`.
Its `eligibility` reports whether the run admits exact theorem-backed reporting, only envelope-bounded reporting, or no theorem-backed reporting under the declared profile.

`ScenarioStats.theorem_progress` adds the theorem-native quantitative summary:

- `initial_weighted_measure`
- `initial_depth_budget`
- `productive_step_count`
- `remaining_weighted_measure`
- `weighted_measure_consumed`
- `scheduler_lift`
- `critical_capacity`

These values are intentionally distinct from raw counters such as queue length, message count, or observable-event count.
They summarize the run in the vocabulary of the weighted-measure and scheduling-bound proofs instead.

`ScenarioStats.reconfiguration_summary` is separate again.
It reports:

- `applied_operations`
- `pure_operations`
- `transition_operations`
- `transition_budget_consumed`

This keeps semantic topology/authority cutover accounting distinct from theorem-native descent and productive-step reporting.

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
`MaterialAdapter` derives initial states from built-in scenario material parameters and constructs the handler from `material`.
The harness does not currently consume `GeneratedEffectScenario` directly.

`SimulationHarness::run_batch(...)` and `run_batch_with(...)` run many `HarnessSpec` values concurrently.
Batch results remain in the same order as the input slice.
The default batch worker count is host parallelism outside CI and `1` in CI.
`BatchRunResult.manifest` records one resolved theorem-profile entry per input spec, even when an individual run later fails.

Distributed simulation uses a different execution vocabulary.
`DistributedSimBuilder::execution_contract(...)` accepts a `NestedExecutionContract` for outer scheduler concurrency plus inner rounds-per-step.
That outer/inner VM contract is part of simulation semantics, not just a worker-pool tuning knob.

## Initial State Derivation

`derive_initial_states(&Scenario)` builds default per-role state vectors from built-in `material` when present.
`mean_field` broadcasts one concentration vector to every role.
`hamiltonian` maps each role index to `[position, momentum]`.
`continuum_field` assigns one scalar field value per role.

The generic harness path does not require scenario materials.
If a `HostAdapter` returns explicit initial states, the simulator never consults the built-in material catalog.

The runner writes these state vectors into coroutine registers starting at register `2`.
The sampled trace reads the same numeric suffix back out.

## Sampling and Step Mapping

The simulator now uses explicit round-based sampling.
It does not infer round boundaries from `ObsEvent::Invoked` counts.

If `steps > 0`, the runner records an initial sample at step `0` before the first protocol-machine round.
Each subsequent completed round records one additional sample.
If no samples were produced during execution, the runner emits one fallback sample at the last requested step index.

## Scenario Execution Order

Scenario runs and replay now share the same execution core and use a fixed per-round order for determinism.

1. Compute `next_tick` from the protocol-machine clock.
2. Activate due simulator reconfiguration operations from newly visible observable events in `machine.trace()`.
3. Advance the fault schedule from newly visible observable events in `machine.trace()`.
4. Deliver due delayed fault messages.
5. When network middleware is active, route those due fault-delayed messages back through the network policy stage before they enter protocol-machine buffers.
6. Deliver due network middleware queues.
7. Update paused roles from active crash faults.
8. Execute one protocol-machine round with the selected handler domain.
9. Record one round-based trace sample when sampling is enabled.
10. Run online property checks.
11. Attempt checkpoint persistence when the interval policy triggers.

Checkpoint persistence is best-effort.
Serialization and file-write failures do not fail the run.
`CheckpointStore` records the last persistence error internally.

Checkpoint snapshots currently require the canonical backend.
Threaded scenario runs still emit observable/effect replay artifacts, but checkpoint serialization remains a canonical-only lane.

## Determinism and Reproducibility

Simulator randomness is scoped to `SimRng`.
`SimRng` is seeded from `scenario.seed` and currently uses `ChaCha8`.
The protocol machine remains deterministic given the same handler outcomes and scheduler inputs.

`scheduler_concurrency` may change simulation behavior because it changes how much work one round can admit.
`worker_threads` must not change authoritative outputs for a fixed threaded execution setting.
The canonical backend remains the authoritative replay and debugging lane.

Record ordering is stable within each sampling pass.
Replay artifacts preserve the observable, semantic, and reconfiguration data needed for deterministic post-run inspection.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Protocol-Machine Simulation Materials](504_simulation_materials.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
