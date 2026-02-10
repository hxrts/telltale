# Lean Verification

Telltale uses Lean 4 to formalize session types, projection, and runtime models. This document summarizes what is proven, what remains axiomatized, and how the Lean tooling integrates with Rust.

## Verified Scope

The Lean codebase defines the core session type theory and projection pipeline. The `SessionTypes` and `SessionCoTypes` libraries cover inductive and coinductive representations, along with duality and roundtrip lemmas. The `Choreography` library proves projection properties using blindness arguments to avoid projectability axioms.

## Axiomatized Areas

Several areas are still axiomatized. The main stubs live in:

- `lean/Protocol/Preservation.lean` and `lean/Protocol/DeadlockFreedom.lean`
- `lean/Protocol/Deployment/Linking.lean` and related deployment files
- `lean/Runtime/Shim/*` for the Iris style logic shims
- `lean/Runtime/Proofs/TheoremStubs.lean` for remaining runtime level placeholders

Use the axiom inventory in [Lean Verification Code Map](../lean/CODE_MAP.md) for the complete list.

## Module Map

The Lean tree is organized into top level libraries:

- `SessionTypes` for inductive global and local types
- `SessionCoTypes` for coinductive equality and bisimulation
- `Choreography` for projection and harmony proofs
- `Semantics` for operational rules
- `Protocol` for buffered MPST and monitoring
- `Runtime` for VM models and Iris shims

See [Lean Verification Code Map](../lean/CODE_MAP.md) for file level detail.

## Rust Integration

The `telltale-lean-bridge` crate exports GlobalType JSON plus per-role LocalTypeR JSON and runs the Lean validator. The main entry points are the `lean-bridge-exporter` binary and the `telltale_validator` Lean executable.

The Justfile includes convenience recipes:

```bash
just telltale-lean-check
just telltale-lean-check-extended
just telltale-lean-check-failing
```

These recipes expect `.choreo` inputs under `fixtures/choreo/` and write artifacts to `lean/artifacts`.

## VM Correspondence

Runtime correspondence checks live in the bridge and VM test suites:

- `rust/lean-bridge/tests/vm_correspondence_tests.rs`
  - runs Tier1 protocol fixtures through Rust VM execution
  - compares normalized Rust traces against Lean VM runner traces via `VmRunner::compare_execution`
- `rust/lean-bridge/tests/invariant_verification_tests.rs`
  - validates protocol bundles against Lean verification entrypoints
  - asserts structured error artifacts (`code`, `path`) for negative cases

The bridge schema tests (`rust/lean-bridge/tests/schema_version_tests.rs`) also gate payload compatibility for:

- `lean_bridge.v1`
- `protocol_bundle.v1`
- `vm_state.v1`

## Golden Equivalence Tests

There are golden comparison tests in `telltale-lean-bridge` that check Rust and Lean outputs.

```bash
just check-golden-drift
just test-live-equivalence
```

These commands build the Lean runner and execute the bridge tests.

## Working With Lean

Lean builds use Lake with the toolchain in `lean/lean-toolchain`. Use `just lean-test` to confirm the toolchain is available before running the full recipes.

See [Lean-Rust Bridge](20_lean_rust_bridge.md) for the exporter format and the runner protocol.
