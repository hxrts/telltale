# Protocol-Machine Simulation

This page is the top-level guide for `telltale-simulator`.
It describes the supported simulator surface at a high level.
Detailed behavior lives in the focused pages linked below.

## Scope

The simulator runs projected local types on `telltale-machine`.
It adds deterministic middleware for faults, network behavior, property monitoring, checkpointing, and replay artifacts.
It also provides a harness API for external integration testing.

Materials are the simulator's abstraction for domain state evolution.
A material model defines how role-local numeric state changes when the protocol machine invokes `EffectHandler::step`, how an effect handler is constructed, and how default per-role initial states are derived.
This keeps protocol structure separate from model-specific dynamics.

The simulator-facing abstraction is `MaterialModel` in `rust/simulator/src/material.rs`.
The scenario file format still uses the built-in `MaterialParams` enum as a serde-tagged catalog for shipped material families.
`MaterialParams` implements `MaterialModel`, but custom Rust integrations may implement `MaterialModel` directly without modifying the scenario schema.

The primary integration path today is `SimulationHarness` with either `DirectAdapter` or `MaterialAdapter`.
Generated effect-family helpers exist as adjacent APIs for integration layers and test fixtures.
They are not yet wired into the main harness execution path.

## Quick Start

Use `SimulationHarness` with a `HostAdapter` implementation and a `HarnessSpec`.

```rust
let adapter = MaterialAdapter::from_scenario(&spec.scenario);
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
assert_contracts(&result, &ContractCheckConfig::default())?;
```

This path runs protocol-machine execution, scenario middleware, replay capture, and post-run contract checks.
It is the recommended integration lane for external projects.

Use `DirectAdapter` when the host already owns the `EffectHandler`.
Use `MaterialAdapter::from_scenario(...)` when built-in scenario material parameters should construct the handler and initial states.
Use `MaterialAdapter::new(...)` or `MaterialAdapter::from_boxed_model(...)` when a Rust integration wants to supply a custom `MaterialModel`.

## Generated Effect Helpers

The simulator also exposes generated effect-family helper types such as `GeneratedEffectScenario`.
These APIs are useful when a project wants to script semantic outcomes for exported effect operations.
Callers obtain a builder via `GeneratedEffectScenario::builder()` and chain outcome declarations before running.
They currently sit beside the harness API rather than inside it.

Use this lane when a downstream integration layer needs effect-centric fixtures.
Do not document it as the default `SimulationHarness` workflow unless that wiring is added.

## Document Map

Use these pages for detailed behavior.

- [Protocol-Machine Simulation Runner](502_simulation_runner.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Protocol-Machine Simulation Materials](504_simulation_materials.md)

## CLI

Use the simulator runner binary through `just` for CI-friendly JSON output.

```text
just sim-run artifacts/sim_integration.toml
```

## Related Docs

- [Effect Handlers and Session Types](303_effect_session_bridge.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
