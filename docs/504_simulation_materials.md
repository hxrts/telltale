# Protocol-Machine Simulation Materials

This page documents material handlers, distributed simulation, post-run analysis, and simulator coverage.
It also records current implementation limits.

## Material Handlers

Telltale treats materials as a separate abstraction, keeping protocol structure and domain dynamics as different concerns.
The choreography and local types define who may communicate and in what order.
A material defines how role-local state evolves when protocol-visible effects occur.

This separation lets one simulator runner support multiple deterministic state-transition models.
It keeps replay, fault semantics, and analysis independent of any one domain model.
It also gives Rust and Lean parity checks a stable boundary for step semantics.

The simulator-facing Rust abstraction is `MaterialModel` in `rust/simulator/src/material.rs`.
A `MaterialModel` supplies three things:

- a stable layer name for diagnostics and registry-style dispatch
- a `Box<dyn EffectHandler>` via `build_handler()`
- default per-role initial states via `derive_initial_states(roles)`

This is the open extension point for custom Rust integrations.
Callers can implement `MaterialModel` for any deterministic mean-field, Hamiltonian, continuum-field, or other state-evolution family without editing the built-in simulator catalog.

Lean mirrors this executable boundary under `lean/Runtime/Simulation/Material.lean` and
includes a Lean-native `MaterialModel`, `MaterialHandler`, built-in `MaterialParams` catalog, and initial-state derivation for the shipped material families.
This is still an executable parity layer rather than a mirror of Rust trait objects or serde-driven scenario parsing.

The built-in scenario format remains intentionally narrower.
When a scenario uses built-in materials, `Scenario.material` deserializes into the serde-tagged `MaterialParams` enum, which currently ships:

- `mean_field`
- `hamiltonian`
- `continuum_field`

`MaterialParams` implements `MaterialModel`, so the built-in scenario path and the general Rust extension path share the same simulator boundary.
The base `Scenario` type does not require built-in material params when a host adapter owns handler creation and initial-state derivation.

Simulator material handlers implement deterministic `EffectHandler::step` updates over fixed-point state.
The runner stores material state in coroutine registers starting at register `2`.
The sampled trace reads that numeric suffix back out as `Vec<FixedQ32>`.

- `IsingHandler` advances a two-species mean-field state with Euler integration.
- `HamiltonianHandler` tracks peer position and force state with leapfrog integration.
- `ContinuumFieldHandler` tracks peer field values with a two-phase diffusion update.

Construct handlers directly, through `handler_from_model(...)`, or through `handler_from_material(...)` for the built-in config enum.
Use `MaterialAdapter::from_scenario(...)` when built-in scenario material parameters should drive both handler construction and initial state derivation.
Use `MaterialAdapter::new(...)` or `MaterialAdapter::from_boxed_model(...)` when a host integration wants the harness to own a custom `MaterialModel`.

The harness exposes both helper lanes:

- `derive_initial_states(&Scenario)` for the built-in scenario schema
- `derive_initial_states_for_model(&dyn MaterialModel, roles)` for arbitrary material-model implementations

## Distributed Simulation

`DistributedSimBuilder` constructs an outer protocol machine and per-site inner protocol machines through `NestedProtocolMachineHandler`.
Each site owns a local set of `CodeImage` protocols and one effect handler.
Site names must match outer protocol roles.

The builder also supports `outer_concurrency(...)` and `inner_rounds_per_step(...)`.
`DistributedSimulation::run(max_rounds)` advances outer and inner runtimes with the configured coupling.

## Post-run Analysis

The `analysis` module provides deterministic trace checks that do not mutate protocol-machine state.
Checks return structured pass and failure outputs.

Available checks include `check_conservation`, `check_simplex`, `check_convergence`, and `check_energy_conservation`.
`validate(...)` runs the standard bundle for conservation, simplex, and per-role convergence.

## Coverage and Conformance

The current simulator test suite includes:

- `end_to_end.rs` for projection and protocol-machine integration.
- `regression.rs` for behavior that must remain stable across refactors.
- `scenario_runner.rs` for scenario middleware and replay-facing results.
- `harness_contracts.rs` for `SimulationHarness` and contract-check workflows.
- `ownership_faults.rs` for ownership and failure-path fault behavior.
- `distributed.rs` for nested runtime behavior.
- `material_handler_parity.rs` for Rust material semantics against parity fixtures.
- `lean_reference_parity.rs` for Lean-facing simulator reference parity.

`material_handler_parity.rs` and `lean_reference_parity.rs` are the main parity lanes for simulator semantics.
They help keep Rust behavior synchronized with the Lean reference material where the project maintains that comparison.

## Current Limits

`run_with_scenario(...)` returns in-memory artifacts and statistics.
It does not write arbitrary scenario output files by itself.
The `run` binary controls JSON emission through CLI flags.

`GeneratedEffectScenario` remains an adjacent helper API under `telltale_simulator::generated` rather than a built-in `SimulationHarness` input.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Runner](502_simulation_runner.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
