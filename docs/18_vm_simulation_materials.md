# VM Simulation Materials

This page documents material handlers, distributed simulation, and post-run analysis.
It also records current limits and test coverage.

## Material Handlers

Simulator material handlers implement `EffectHandler::step` state updates with fixed-point conversions.
Each handler has deterministic update rules under fixed seed and scheduling.

- `IsingHandler` advances a two-species mean-field state with Euler integration.
- `HamiltonianHandler` tracks peer position and force state and applies leapfrog integration.
- `ContinuumFieldHandler` tracks peer field values and applies a two-phase diffusion update.

These handlers are constructed directly or through `handler_from_material`.

## Distributed Simulation

`DistributedSimBuilder` constructs an outer VM plus per-site inner VMs through `NestedVMHandler`.
Each site owns a local set of `CodeImage` protocols and one effect handler.

Build fails when site names do not match outer protocol roles.
The builder also supports `outer_concurrency(...)` and `inner_rounds_per_step(...)`.
`DistributedSimulation::run(max_rounds)` advances outer and inner runtimes with the configured coupling.

## Post-run Analysis

The `analysis` module provides deterministic trace checks that do not mutate VM state.
Checks return structured pass and failure outputs.

Available checks include `check_conservation`, `check_simplex`, `check_convergence`, and `check_energy_conservation`.
`validate` runs the standard analysis bundle for conservation, simplex, and per-role convergence.

## Coverage and Conformance

Simulator tests include `end_to_end.rs`, `regression.rs`, `distributed.rs`, and `material_handler_parity.rs`.
These tests cover projection integration, trace comparison, nested runtime behavior, and material parity fixtures.

`material_handler_parity.rs` is aligned with Lean mirror simulator tests.
This keeps material-step semantics synchronized across Lean and Rust lanes.

## Current Limits

`run_with_scenario` returns in-memory artifacts and stats.
It does not write arbitrary scenario output files by itself.

`active_per_role` follows the first branch when estimating active node count.
`Trigger::AfterStep` is evaluated against current tick in the fault injector.

## Related Docs

- [VM Simulation](15_vm_simulation_overview.md)
- [VM Simulation Runner](16_vm_simulation_runner.md)
- [VM Simulation Scenarios](17_vm_simulation_scenarios.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
