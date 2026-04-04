# Simulation Fields

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

The built-in scenario schema uses the serde-tagged `FieldSpec` catalog through `Scenario.field`.
Current built-in families are `mean_field`, `hamiltonian`, and `continuum_field`.

### Adapter Integration

Use `FieldAdapter::from_scenario(...)` when built-in scenario field parameters should drive handler construction and default state derivation.
Use `FieldAdapter::new(...)` or `FieldAdapter::from_boxed_model(...)` when a host integration wants the harness to own a custom `FieldModel`.
The harness provides `derive_initial_states(&Scenario)` for the built-in schema and `derive_initial_states_for_field_model(&dyn FieldModel, roles)` for arbitrary implementations.

Simulator field handlers implement deterministic `EffectHandler::step` updates over fixed-point state.
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
That snapshot exposes current tick, logical step, participating roles, field-backed node state, node poses, node capabilities, and potential links.
The shared execution core emits one canonical `EnvironmentTrace` of `EnvironmentArtifact` records for mobility updates, capability snapshots, reachability decisions, admission outcomes, and medium outcomes.

### Extension Configuration

`Scenario.extensions` is the generic config hook for domain-owned environment configuration.
It is a namespaced map of arbitrary TOML values so external projects can carry their own config without adding vertical-specific fields to core `Scenario`.
Vertical-specific logic belongs in downstream crates, not in the core simulator schema.

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

- [Simulation Overview](501_simulation_overview.md)
- [Simulation Runner](502_simulation_runner.md)
- [Simulation Scenarios](503_simulation_scenarios.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
