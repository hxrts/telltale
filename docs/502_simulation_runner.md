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
The runner skips the first two reserved registers and samples field-backed state starting at register `2`.

`ScenarioReplayArtifact` contains the resolved adversary schedule, adversary budget-consumption history, assumption diagnostics, observable events, effect traces, output-condition checks, semantic audit records, `ProtocolMachineSemanticObjects`, a canonical simulator reconfiguration trace, and a canonical `EnvironmentTrace`.
These artifacts support deterministic replay and post-run validation.

`ScenarioResult.analysis.normalized_observability` is the companion analysis view.
It is derived from replay-visible raw traces, but it is not itself the authoritative replay surface.
That separation keeps debugging and replay pinned to the canonical raw event stream.

## Runner Entry Points

The runner exposes three main entry points.

- `run(...)` executes one choreography and returns one sampled trace.
- `run_multi_session_canonical(...)` executes multiple choreographies on one canonical protocol machine and returns one trace per input choreography.
- `run_with_scenario(...)` executes one choreography with scenario middleware and returns `ScenarioResult`.

Use `run_with_scenario(...)` when budgeted adversaries, network behavior, properties, checkpoints, or replay artifacts are required.
Use the smaller entry points when only sampled state traces are needed.

`run_with_scenario(...)` resolves execution through `Scenario.execution`.
That resolution decides:

- which machine backend to use
- which scheduler policy the protocol machine runs under
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
- `critical_capacity`

These values are intentionally distinct from raw counters such as queue length, message count, or observable-event count.
They summarize the run in the vocabulary of the weighted-measure and scheduling-bound proofs instead.

`ScenarioStats.scheduler_profile` is the scheduler-facing companion report.
It records:

- `implementation_policy`
- `theorem_profile`
- `productive_exactness`
- `total_step_mode`
- `total_step_upper_bound`
- `fairness_requirement`
- `envelope_status`

`ScenarioStats.reconfiguration_summary` is separate again.
It reports:

- `applied_operations`
- `pure_operations`
- `transition_operations`
- `transition_budget_consumed`

This keeps semantic topology/authority cutover accounting distinct from theorem-native descent and productive-step reporting.

`ScenarioStats.adversary_summary` and `ScenarioStats.assumption_diagnostics` are separate again.
They report:

- how many adversaries were declared and activated
- how much declared disturbance budget was consumed
- which adversary budgets exhausted
- which theorem-side assumption clauses failed, if any

The raw replay artifact retains the full adversary program plus one budget-history record per activation, consumption, and exhaustion event.

The analysis layer also exposes `compare_observability(...)`.
That comparison reports one of three relations:

- `exact_raw_match`
- `equivalent_under_normalization`
- `safety_visible_divergence`

Normalization is order-insensitive over session-normalized observable events and canonical reconfiguration footprints.
If two runs only differ by admissible exchange ordering or equivalent footprint-normalized cutover ordering, the report upgrades them to `equivalent_under_normalization`.
If the normalized classes still differ, the comparison remains a safety-visible divergence.

Offline theorem-facing checks live in the `decision` module rather than in the runner itself.
Use that module for:

- global well-formedness and coherence checks
- async- and sync-subtyping checks
- productive-step capacity predicates
- theorem-profile eligibility before running the simulator

These decision procedures return structured `DecisionReport` values with either a certificate or a counterexample object.
They are distinct from empirical run analysis such as `theorem_progress`, `reconfiguration_summary`, or normalized observability comparison.
The one intentional bridge is theorem eligibility: the same witness format is available both offline (`decide_theorem_eligibility(...)`) and from an executed run (`theorem_eligibility_from_result(...)`).

## Approximation Artifacts

Approximation runs are now explicit and separate from `ScenarioResult`.
Use `run_approximation(...)` with an `ApproximationSpec` when the caller wants a non-authoritative artifact for `batched_stochastic`, `mean_field`, or `continuum_field` analysis.

Approximation artifacts retain:

- an `ApproximationManifest`
- the sampled state `Trace`
- `NormalizedObservability`
- shared observables such as final per-role states and productive-step counts

They intentionally do not pretend to be canonical replay artifacts.
Instead the manifest declares:

- the approximation family
- the theorem-side scope
- explicit non-goals
- whether the approximation is theorem-backed, empirical-only, or unsupported for this scenario/profile pair

Use `compare_exact_and_approximate(...)` to compare an authoritative `ScenarioResult` against one approximation artifact.
That report compares normalized observability, productive-step counts, and final-state error without blurring the authoritative replay lane.

## Harness API

`SimulationHarness` is the stable integration path for external projects.
It runs `HarnessSpec` or `HarnessConfig` through a `HostAdapter`.

```rust
pub trait HostAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler;
    fn initial_states(&self, scenario: &Scenario)
        -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String>;
    fn environment_models(&self, scenario: &Scenario)
        -> Result<Option<EnvironmentModels<'_>>, String>;
    fn validate_result(&self, scenario: &Scenario, result: &ScenarioResult)
        -> Result<(), String>;
}
```

`DirectAdapter` wraps an existing `EffectHandler`.
`FieldAdapter` derives initial states from built-in scenario field parameters and constructs the handler from `field`.
The harness does not currently consume `GeneratedEffectScenario` directly.

`SimulationHarness::run_batch(...)` and `run_batch_with(...)` run many `HarnessSpec` values concurrently.
Batch results remain in the same order as the input slice.
The default batch worker count is host parallelism outside CI and `1` in CI.
`BatchRunResult.manifest` records one resolved theorem-profile entry per input spec, even when an individual run later fails.
`SimulationHarness::run_sweep(...)` extends that batch lane into deterministic parameter sweeps.
Current sweep axes include:

- `seed`
- `capacity_budget`
- `scheduler_profile`
- `reconfiguration_program`
- `adversary_budget`

Sweep expansion preserves deterministic input order.
`SweepRunResult.manifest` records, per expanded run:

- explicit parameter bindings
- resolved theorem profiles
- resolved scheduler profiles when execution succeeded
- theorem-eligibility witnesses
- capacity-predicate reports when a capacity budget axis is present
- per-run execution errors without collapsing the manifest layout

Use `compare_sweep_results(...)` to diff two experiment families by theorem eligibility, productive-step deltas, and assumption-diagnostic changes rather than comparing ad hoc logs.

Distributed simulation uses a different execution vocabulary.
`DistributedSimBuilder::execution_contract(...)` accepts a `NestedExecutionContract` for outer scheduler concurrency plus inner rounds-per-step.
That outer/inner VM contract is part of simulation semantics, not just a worker-pool tuning knob.

## Initial State Derivation

`derive_initial_states(&Scenario)` builds default per-role state vectors from built-in `field` when present.
`mean_field` broadcasts one concentration vector to every role.
`hamiltonian` maps each role index to `[position, momentum]`.
`continuum_field` assigns one scalar field value per role.

The generic harness path does not require scenario field data.
If a `HostAdapter` returns explicit initial states, the simulator never consults the built-in field catalog.

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
3. Advance the adversary program from newly visible observable events in `machine.trace()`.
4. Deliver due delayed adversary messages.
5. When network middleware is active, route those due adversary-delayed messages back through the network policy stage before they enter protocol-machine buffers.
6. Deliver due network middleware queues.
7. Update paused roles from active crash adversaries.
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
Normalized observability classes are for comparison and analysis only.
They do not replace canonical replay traces.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Protocol-Machine Simulation Fields](504_simulation_fields.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
