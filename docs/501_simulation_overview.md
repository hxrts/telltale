# Simulation Overview

This page is the top-level guide for `telltale-simulator`.
It describes the supported simulator surface at a high level.
Detailed behavior lives in the focused pages linked below.

## Scope

The simulator runs projected local types on `telltale-machine`.
It adds deterministic middleware for budgeted adversaries, network behavior, property monitoring, checkpointing, and replay artifacts.
It also provides a harness API for external integration testing.

### Field and Environment Models

Fields are the simulator's abstraction for deterministic environment-dynamics evolution.
A field model defines how role-local numeric state changes when the protocol machine invokes `EffectHandler::step`, how an effect handler is constructed, and how default per-role initial states are derived.
This keeps protocol structure separate from model-specific dynamics.

The simulator-facing abstraction is `FieldModel` in `rust/simulator/src/field.rs`.
`FieldSpec` is the built-in serde-tagged catalog for shipped field families.
Custom Rust integrations may implement `FieldModel` directly without modifying the scenario schema.

Topology, medium behavior, mobility, capability limits, and link admission live beside the field layer as separate environment hooks.
The shared execution core consumes `EnvironmentSnapshot`, emits `EnvironmentTrace`, and accepts external model implementations without baking domain-specific naming into core `Scenario`.

### Execution and Theorem Profiles

The primary integration path is `SimulationHarness` with either `DirectAdapter` or `FieldAdapter`.
Execution policy is explicit through `Scenario.execution`, which separates backend choice from scheduler policy, scheduler concurrency, and worker-thread count.
The default `auto` policy resolves to the authoritative canonical execution lane with `scheduler_concurrency = 1` and `worker_threads = 1`.

The simulator also exposes a separate theorem/profile layer through `Scenario.theorem`.
This layer records scheduler profile, envelope profile, and transport/adversary assumption bundle independently of raw execution settings.
That separation lets one execution be interpreted under different theorem-side contracts without changing the runtime behavior itself.

### Reporting and Analysis

`ScenarioStats` includes theorem-native progress, reconfiguration accounting, and adversary budget summaries as separate fields.
Replay artifacts retain the resolved adversary program and budget-consumption history so theorem-side assumption failures are inspectable after the fact.
`ScenarioResult.analysis.normalized_observability` provides the companion envelope-aware analysis view for order-insensitive and footprint-aware comparison.

### Decision and Approximation Modules

The `decision` module provides offline theorem-facing checks that return structured certificates and counterexamples for coherence, subtyping, capacity predicates, and theorem-profile eligibility.
The `approximation` module provides non-authoritative analysis runs for `batched_stochastic`, `mean_field`, and `continuum_field` families.
Approximation artifacts declare an approximation family, theorem-side scope, and explicit non-goals.

## Quick Start

Use `SimulationHarness` with a `HostAdapter` implementation and a `HarnessSpec`.

```rust
let adapter = FieldAdapter::from_scenario(&spec.scenario)?;
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
assert_contracts(&result, &ContractCheckConfig::default())?;
```

This path runs protocol-machine execution, scenario middleware, replay capture, and post-run contract checks.
It is the recommended integration lane for external projects.

Use `DirectAdapter` when the host already owns the `EffectHandler`.
Use `FieldAdapter::from_scenario(...)` when built-in scenario field parameters should construct the handler and initial states.
Use `FieldAdapter::new(...)` or `FieldAdapter::from_boxed_model(...)` when a Rust integration wants to supply a custom `FieldModel`.
If the host adapter supplies initial states directly, the base `Scenario` does not need built-in field params at all.

### Batch and Sweep Execution

`SimulationHarness` supports batched execution through `run_batch(...)` and `run_batch_with(...)`.
Batch execution parallelizes independent runs while preserving result order by input index.
Batch results carry a theorem-profile manifest so batch tooling can inspect resolved theorem classifications without unpacking each run.

`SimulationHarness::run_sweep(...)` expands one base `HarnessSpec` into a deterministic sweep over seeds, scheduler profiles, reconfiguration programs, adversary budgets, and capacity budgets.
Sweep results emit a manifest with parameter bindings, theorem eligibility witnesses, and capacity-predicate reports.

### Distributed Simulation

`DistributedSimBuilder` accepts one explicit `NestedExecutionContract` describing outer scheduler concurrency and inner rounds-per-step.
That nested-VM contract is distinct from worker-thread count and other performance-only parallelism controls.

## Generated Effect Helpers

The simulator also exposes generated effect-family helper types under `telltale_simulator::generated`, such as `GeneratedEffectScenario`.
Callers obtain a builder via `GeneratedEffectScenario::builder()` and chain outcome declarations before running.
These APIs currently sit beside the harness API rather than inside it.

Scenario replay artifacts retain a canonical `reconfiguration_trace` shared across fresh runs, replay, and post-run analysis.
The helper `compare_observability(...)` reports `exact_raw_match`, `equivalent_under_normalization`, or `safety_visible_divergence`.

## Document Map

Use these pages for detailed behavior.

- [Simulation Runner](502_simulation_runner.md)
- [Simulation Scenarios](503_simulation_scenarios.md)
- [Simulation Fields](504_simulation_fields.md)

## CLI

Use the simulator runner binary through `just` for CI-friendly JSON output.

```text
just sim-run artifacts/sim_integration.toml
```

This command runs one scenario through the simulator entrypoint and emits the same authoritative artifacts the harness APIs produce.

## Related Docs

- [Effect Handlers and Session Types](303_effect_session_bridge.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
