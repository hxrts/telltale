# Simulation Runner

This page documents runner behavior in `telltale-simulator`.
It covers traces, runner entry points, stats, harness API, and scenario round order.

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
The runner skips the first two reserved registers and samples field-backed state starting at register `2`.

`ScenarioReplayArtifact` contains the resolved adversary schedule, observable events, effect traces, semantic audit records, `ProtocolMachineSemanticObjects`, the canonical reconfiguration trace, and the canonical `EnvironmentTrace`.
These artifacts support deterministic replay and post-run validation.

## Runner Entry Points

The runner exposes three main entry points.

- `run(...)` executes one choreography and returns one sampled trace.
- `run_multi_session_canonical(...)` executes multiple choreographies on one canonical protocol machine and returns one trace per input choreography.
- `run_with_scenario(...)` executes one choreography with scenario middleware and returns `ScenarioResult`.

Use `run_with_scenario(...)` when adversaries, network behavior, properties, checkpoints, or replay artifacts are required.
Use the smaller entry points when only sampled state traces are needed.

`ScenarioStats.execution_regime` records the proof-side concurrency class for the resolved run.
`canonical_exact` means single-step cooperative execution.
`threaded_exact` means threaded execution at concurrency 1, which is theorem-equal to canonical.
`threaded_envelope_bounded` means threaded execution at concurrency greater than 1, which is only authoritative modulo the declared envelope.

## Stats and Summaries

### Theorem Progress

`ScenarioStats.theorem_progress` reports theorem-native quantities that summarize the run in terms of the weighted-measure and scheduling-bound proofs.
Depth is the sum of remaining session-type steps to `end` across all active sessions.
Buffer is the total pending message count across all session buffers.
The weighted measure is `W = 2 * depth + buffer`, a composite termination metric that strictly decreases on productive steps.

The reported fields are `initial_weighted_measure`, `initial_depth_budget`, `productive_step_count`, `remaining_weighted_measure`, `weighted_measure_consumed`, and `critical_capacity`.
Critical-capacity phase classifies whether productive steps stayed below, at, or above the initial depth budget.
This classification is unsupported for recursive protocols.

### Other Summaries

`ScenarioStats.scheduler_profile` records the scheduler-facing report including implementation policy, productive exactness, total-step mode, and envelope status.
`ScenarioStats.reconfiguration_summary` reports applied, pure, and transition operations with transition budget consumed.
`ScenarioStats.adversary_summary` and `ScenarioStats.assumption_diagnostics` report adversary activation, budget consumption, and theorem-side assumption failures.

### Observability Comparison

`compare_observability(...)` reports one of three relations: `exact_raw_match`, `equivalent_under_normalization`, or `safety_visible_divergence`.
Normalization is order-insensitive over session-normalized observable events and canonical reconfiguration footprints.

## Harness API

`SimulationHarness` is the stable integration path for external projects.
It runs `HarnessSpec` or `HarnessConfig` through a `HostAdapter`.
`HostAdapter` provides an `EffectHandler`, optional initial states, optional environment models, and a result validation callback.

`DirectAdapter` wraps an existing `EffectHandler`.
`FieldAdapter` derives initial states and constructs the handler from scenario field parameters.
See [Simulation Fields](504_simulation_fields.md) for field adapter variants and custom `FieldModel` integration.

### Batch and Sweep

`run_batch(...)` and `run_batch_with(...)` run many `HarnessSpec` values concurrently while preserving result order.
`BatchRunResult.manifest` records one resolved theorem-profile entry per input spec.

`run_sweep(...)` extends batch execution into deterministic parameter sweeps over `seed`, `capacity_budget`, `scheduler_profile`, `reconfiguration_program`, and `adversary_budget`.
`SweepRunResult.manifest` records parameter bindings, theorem profiles, eligibility witnesses, and capacity-predicate reports per expanded run.
Use `compare_sweep_results(...)` to diff experiment families by theorem eligibility and productive-step deltas.

### Distributed Simulation

`DistributedSimBuilder::execution_contract(...)` accepts a `NestedExecutionContract` for outer scheduler concurrency plus inner rounds-per-step.
That outer/inner VM contract is part of simulation semantics, not a worker-pool tuning knob.

## Sampling and Step Mapping

The simulator uses explicit round-based sampling.
If `steps > 0`, the runner records an initial sample at step `0` before the first protocol-machine round.
Each subsequent completed round records one additional sample.
If no samples were produced during execution, the runner emits one fallback sample at the last requested step index.

## Scenario Execution Order

Scenario runs and replay share the same execution core and use a fixed per-round order for determinism.

1. Compute `next_tick` from the protocol-machine clock.
2. Activate due simulator reconfiguration operations from newly visible observable events.
3. Advance the adversary program from newly visible observable events.
4. Deliver due delayed adversary messages.
5. When network middleware is active, route adversary-delayed messages through the network policy stage before they enter protocol-machine buffers.
6. Deliver due network middleware queues.
7. Update paused roles from active crash adversaries.
8. Execute one protocol-machine round with the selected handler domain.
9. Record one round-based trace sample when sampling is enabled.
10. Run online property checks.
11. Attempt checkpoint persistence when the interval policy triggers.

Checkpoint persistence is best-effort.
Serialization and file-write failures do not fail the run.

## Determinism and Reproducibility

Simulator randomness is scoped to `SimRng`, seeded from `scenario.seed` and currently backed by `ChaCha8`.
The protocol machine remains deterministic given the same handler outcomes and scheduler inputs.
The canonical backend remains the authoritative replay and debugging lane.

Record ordering is stable within each sampling pass.
Replay artifacts preserve the observable, semantic, and reconfiguration data needed for deterministic post-run inspection.

## Related Docs

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Scenarios](503_simulation_scenarios.md)
- [Simulation Fields](504_simulation_fields.md)
- [Rust-Lean Bridge and Parity](802_rust_lean_parity.md)
