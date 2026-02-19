# Lean-Rust Bridge

The `telltale-lean-bridge` crate connects Rust runtime artifacts to Lean validation and correspondence workflows.

## Purpose

The bridge exports typed protocol/runtime payloads and runs Lean-backed checks over those payloads. The bridge does not define VM semantics.

The semantic authority stays in Lean runtime models and Rust kernel execution paths.

## Artifact Families

| Schema Family | Version | Primary Use |
|---|---|---|
| `lean_bridge` | `lean_bridge.v1` | Runner payloads and validation requests |
| `protocol_bundle` | `protocol_bundle.v1` | Invariant/capability claim transport |
| `vm_state` | `vm_state.v1` | Runtime state export and compatibility checks |

All families are version tagged. Decoder paths retain backward-compatible alias handling for prior payload shapes.

## Correspondence Lanes

| Lane | Coverage |
|---|---|
| `vm_correspondence_tests` | Trace-level Lean/Rust correspondence for protocol fixtures |
| `vm_differential_step_tests` | Step-indexed differential correspondence |
| `projection_equivalence_tests` | Theory projection versus DSL projection consistency |

These lanes are included in the parity suite script used by CI.

## Runtime Contract Alignment

Bridge outputs feed parity and gate checks that enforce runtime contract alignment.

- Runtime admission/profile gate shape checks: `scripts/check-runtime-contract-gates.sh`.
- Parity and undocumented deviation gates: `scripts/check-parity-ledger.sh`.
- Speculation, scheduler, and failure-envelope parity fixtures: `rust/vm/tests/parity_fixtures_v2.rs` via `scripts/check-vm-parity-suite.sh`.

## Proved Versus Interface Boundary

Bridge validation uses proved theorem exports where available. It also uses premise-scoped interface surfaces for threaded `n > 1` refinement and capability-gated admission.

This separation is intentional and explicit in Lean API modules. Runtime docs and CI gates preserve the same boundary.

## Related Docs

- [Lean Verification](19_lean_verification.md)
- [VM Parity Contract](29_vm_parity_contract.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
