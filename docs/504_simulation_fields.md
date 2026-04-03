# Protocol-Machine Simulation Fields

This page documents the simulator's field/environment-dynamics layer and the generic external environment boundary.

## Field Layer

Telltale now treats field dynamics as one layer inside a broader environment model.
The field layer is responsible for evolving shared fields, latent environment state, or node-local physical state when protocol-visible effects occur.
It does not by itself decide topology, medium contention, mobility, or admission.

The simulator-facing Rust abstraction is `FieldModel` in `rust/simulator/src/field.rs`.
A `FieldModel` supplies:

- a stable layer name
- a `Box<dyn EffectHandler>` via `build_handler()`
- default per-role initial states via `derive_initial_states(roles)`

The built-in scenario schema can use the narrower serde-tagged `FieldSpec` catalog through `Scenario.field`.
Current built-in families are:

- `mean_field`
- `hamiltonian`
- `continuum_field`

Use `FieldAdapter::from_scenario(...)` when built-in scenario field parameters should drive handler construction and default state derivation.
Use `FieldAdapter::new(...)` or `FieldAdapter::from_boxed_model(...)` when a host integration wants the harness to own a custom `FieldModel`.
The harness helpers are:

- `derive_initial_states(&Scenario)` for the built-in scenario schema
- `derive_initial_states_for_field_model(&dyn FieldModel, roles)` for arbitrary field-model implementations

Simulator field handlers still implement deterministic `EffectHandler::step` updates over fixed-point state.
The runner stores field state in coroutine registers starting at register `2`.

## Environment Boundary

External projects should extend the simulator through the domain-neutral environment hooks in `rust/simulator/src/environment.rs`.
The shared execution core now accepts:

- `TopologyModel`
- `MediumModel`
- `MobilityModel`
- `NodeCapabilityModel`
- `LinkAdmissionModel`

These hooks all receive the same `EnvironmentSnapshot` each round.
That snapshot exposes current tick, logical step, participating roles, current built-in field layer, field-backed node state, node poses, node capabilities, and potential links.
The shared execution core emits one canonical `EnvironmentTrace` of `EnvironmentArtifact` records for:

- mobility updates
- capability snapshots
- reachability decisions
- admission rejections or approvals
- medium outcomes such as delay, corruption, collision, contention, or drop

This is the supported extension seam for downstream domain models such as radio, geometry, or device-capability simulation.
Vertical-specific logic belongs in downstream crates/projects, not in the core simulator schema.

`Scenario.extensions` is the generic config hook for domain-owned environment configuration.
It is a namespaced map of arbitrary TOML values so external projects can carry their own environment config without adding Bluetooth-, QUIC-, or other vertical-specific fields to core `Scenario`.

The current crate boundary decision is to keep generic geometry/radio helpers out of `telltale-simulator` itself.
If shared helpers become worthwhile later, they should live in a separate optional crate with domain-neutral names and interfaces.

## Lean Mirror

Lean mirrors the executable field boundary under `lean/Runtime/Simulation/Field.lean`.
That module includes a Lean-native `FieldModel`, `FieldHandler`, built-in `FieldParams` catalog, and default initial-state derivation for the shipped field families.
It remains an executable parity layer rather than a mirror of Rust trait objects or serde-based scenario parsing.

## Coverage

The main parity and extension lanes are:

- `rust/simulator/tests/field_handler_parity.rs`
- `rust/simulator/tests/environment_models.rs`
- `rust/simulator/tests/lean_reference_parity.rs`
- `lean/Runtime/Tests/SimulatorParity.lean`

`environment_models.rs` exists specifically to prove that topology, medium, mobility, capability, and admission hooks work through an external adapter without built-in domain knowledge.

## Related Docs

- [Protocol-Machine Simulation](501_simulation_overview.md)
- [Protocol-Machine Simulation Runner](502_simulation_runner.md)
- [Protocol-Machine Simulation Scenarios](503_simulation_scenarios.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
