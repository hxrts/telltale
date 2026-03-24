# Protocol-Machine Simulation

This page is the top-level guide for `telltale-simulator`.
Detailed behavior is split into focused pages to keep this entry concise.

## Scope

The simulator runs projected local types on `telltale-vm`.
It adds deterministic middleware for scenarios, faults, network behavior, and properties.
It also provides a harness API for external integration testing.
For effect-heavy guest runtimes, it exposes generated effect-family scenario helpers written in terms of declared effect operations and their semantic outcomes.

## Quick Start

Use `SimulationHarness` with a `HostAdapter` implementation.
For generated effect interfaces, script semantic outcomes directly with
`GeneratedEffectScenario` and keep the host adapter thin.

```rust
let adapter = DirectAdapter::new(&handler);
let generated = GeneratedEffectScenario::builder()
    .record_return("Runtime", "acceptInvite", serde_json::json!({ "status": "ok" }))
    .record_timeout("Runtime", "watchPresence")
    .build();
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
assert_contracts(&result, &ContractCheckConfig::default())?;
```

This path runs protocol-machine execution, scenario middleware, generated
effect-family scripting, and post-run contract checks.
It is the recommended integration lane for host runtimes.

It is also the recommended lane for testing ownership handoff, stale-owner rejection, and owner-failure scenarios. The simulator can inject timing, crash, and replay conditions around the same protocol-machine ownership contract used in production runtimes.

When a project uses generated effect interfaces from `effect-scaffold`, the simulator should be treated as a first-class handler domain. Generated scenario builders cover success, timeout, cancellation, stale late result, blocked, and degraded outcomes by default.

## Document Map

Use these pages for detailed behavior.

- [Protocol-Machine Simulation Runner](16_vm_simulation_runner.md): trace shape, runner entry points, harness APIs, sampling model, and round order.
- [Protocol-Machine Simulation Scenarios](17_vm_simulation_scenarios.md): scenario schema, TOML examples, fault and network middleware, properties, checkpointing, and replay.
- [Protocol-Machine Simulation Materials](18_vm_simulation_materials.md): material handlers, distributed simulation, post-run analysis, conformance lanes, and current limits.

## CLI

Use the simulator runner binary through `just` for CI-friendly JSON output.

```text
just sim-run artifacts/sim_integration.toml
```

The process exits with code `2` when configured contract checks fail.

## Related Docs

- [Effect Handlers and Session Types](11_effect_session_bridge.md)
- [Protocol Machine Architecture](12_vm_architecture.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
- [Lean-Rust Bridge](24_lean_rust_bridge.md)
