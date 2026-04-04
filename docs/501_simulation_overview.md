# Simulation Overview

This page is the top-level guide for `telltale-simulator`.
It describes the supported simulator surface at a high level.
Detailed behavior lives in the focused pages linked below.

## Scope

The simulator runs projected local types on `telltale-machine`.
It adds deterministic middleware for budgeted adversaries, network behavior, property monitoring, checkpointing, and replay artifacts.
It also provides a harness API for external integration testing.

## Key Concepts

The simulator wraps the protocol machine defined in `telltale-machine`.
The protocol machine owns scheduling and session-type enforcement.
The simulator adds middleware layers (adversaries, network, properties, checkpoints) and environment dynamics (fields) around that core.
See [Protocol Machine Architecture](401_protocol_machine_architecture.md) for the underlying execution model.

`ObsEvent` is the protocol machine's trace of communication actions such as sends, receives, choices, and offers.
Scenario execution order, property monitoring, and replay artifacts all operate over this event stream.

`FixedQ32` is the fixed-point numeric type (Q32.32) used for all simulator state values including field state, network parameters, and property thresholds.
Quoted decimal strings like `"1.5"` are the safest TOML representation.

`ProtocolMachineSemanticObjects` is the typed introspection snapshot the protocol machine exports after execution.
It contains operation instances, outstanding effects, semantic handoffs, authoritative reads, materialization proofs, canonical handles, publication events, and progress contracts.
Replay artifacts and post-run analysis consume this bundle directly.

### Field and Environment Models

Fields are the simulator's abstraction for deterministic environment-dynamics evolution.
A field model defines how role-local numeric state changes when the protocol machine invokes `EffectHandler::step`, how an effect handler is constructed, and how default per-role initial states are derived.
See [Simulation Fields](504_simulation_fields.md) for the `FieldModel` trait, built-in field families, and environment extension hooks.

Topology, medium behavior, mobility, capability limits, and link admission live beside the field layer as separate environment hooks.
The shared execution core consumes `EnvironmentSnapshot` and emits `EnvironmentTrace` without baking domain-specific naming into core `Scenario`.

### Execution and Theorem Profiles

Execution policy is explicit through `Scenario.execution`, which separates backend choice from scheduler policy, scheduler concurrency, and worker-thread count.
The simulator also exposes a separate theorem/profile layer through `Scenario.theorem`.
That separation lets one execution be interpreted under different theorem-side contracts without changing the runtime behavior itself.
See [Simulation Scenarios](503_simulation_scenarios.md) for the full schema and backend resolution rules.

### Reporting and Analysis

`ScenarioStats` includes theorem-native progress, reconfiguration accounting, and adversary budget summaries as separate fields.
Replay artifacts retain the resolved adversary program and budget-consumption history so theorem-side assumption failures are inspectable after the fact.
`ScenarioResult.analysis.normalized_observability` provides the companion envelope-aware analysis view for order-insensitive and footprint-aware comparison.

The shared viewer stack sits directly on top of those artifacts.
`telltale-viewer` owns the pure model/query/command layer, `telltale-ui` owns the portable Dioxus shell and reusable components, and `telltale-web` owns the browser packaging.
The preferred human-facing inspection path is now the shared viewer rather than ad hoc textual replay output.

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

`DirectAdapter` is for hosts that already own the `EffectHandler`.
`FieldAdapter::from_scenario(...)` constructs the handler and initial states from built-in scenario field parameters.
See [Simulation Fields](504_simulation_fields.md) for custom `FieldModel` integration via `FieldAdapter::new(...)` and `FieldAdapter::from_boxed_model(...)`.

## Generated Effect Helpers

The simulator exposes generated effect-family helper types under `telltale_simulator::generated`, such as `GeneratedEffectScenario`.
Callers obtain a builder via `GeneratedEffectScenario::builder()` and chain outcome declarations before running.
These APIs currently sit beside the harness API rather than inside it.

## Document Map

- [Simulation Runner](502_simulation_runner.md): execution mechanics, stats, harness API, batch/sweep, distributed simulation
- [Simulation Scenarios](503_simulation_scenarios.md): TOML schema, adversaries, reconfiguration, network, properties, checkpointing
- [Simulation Fields](504_simulation_fields.md): field model trait, built-in families, environment extension hooks
- [Simulation Viewer Model](505_simulation_viewer_model.md): pure artifact envelopes, query/command boundary, branch patch model
- [Simulation Viewer Webapp](506_simulation_viewer_webapp.md): Dioxus shell, global layout, ownership markers, testing split, local development

## CLI

Use the simulator runner binary through `just` for CI-friendly JSON output.

```text
just sim-run artifacts/sim_integration.toml
```

This command runs one scenario through the simulator entrypoint and emits the same authoritative artifacts the harness APIs produce.

## Related Docs

- [Effect Handlers and Session Types](303_effect_session_bridge.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Bridge and Parity](802_rust_lean_parity.md)
