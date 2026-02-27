# VM Simulation

This page is the top-level guide for `telltale-simulator`.
Detailed behavior is split into focused pages to keep this entry concise.

## Scope

The simulator runs projected local types on `telltale-vm`.
It adds deterministic middleware for scenarios, faults, network behavior, and properties.
It also provides a harness API for external integration testing.

## Quick Start

Use `SimulationHarness` with a `HostAdapter` implementation.
Run the scenario and assert contracts in one path.

```rust
let adapter = DirectAdapter::new(&handler);
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
assert_contracts(&result, &ContractCheckConfig::default())?;
```

This path runs VM execution, scenario middleware, and post-run contract checks.
It is the recommended integration lane for host runtimes.

## Document Map

Use these pages for detailed behavior.

- [VM Simulation Runner](16_vm_simulation_runner.md): trace shape, runner entry points, harness APIs, sampling model, and round order.
- [VM Simulation Scenarios](17_vm_simulation_scenarios.md): scenario schema, TOML examples, fault and network middleware, properties, checkpointing, and replay.
- [VM Simulation Materials](18_vm_simulation_materials.md): material handlers, distributed simulation, post-run analysis, conformance lanes, and current limits.

## CLI

Use the simulator runner binary through `just` for CI-friendly JSON output.

```text
just sim-run work/sim_integration.toml
```

The process exits with code `2` when configured contract checks fail.

## Related Docs

- [Effect Handlers and Session Types](11_effect_session_bridge.md)
- [VM Architecture](12_vm_architecture.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
- [Lean-Rust Bridge](24_lean_rust_bridge.md)
