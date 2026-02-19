# Lean Verification

This document summarizes the Lean theorem surfaces that are currently consumed by runtime architecture and release gates.

## Scope

Lean covers session typing, projection, scheduler semantics, runtime envelope interfaces, and theorem-pack inventory APIs.

Rust parity and bridge tests consume these surfaces through executable fixtures, artifact schemas, and capability gate checks.

## Proved Theorem Surfaces

| Area | Lean Surface | Status |
|---|---|---|
| Canonical scheduler normalization | `Runtime/Proofs/Concurrency.lean` | Proved |
| Threaded equality at `n = 1` | `Runtime/Proofs/ConcurrencyThreaded.lean` | Proved |
| Scheduler policy theorems | `Runtime/Proofs/VM/Scheduler.lean` | Proved |
| Release conformance gate surfaces | `Runtime/Proofs/TheoremPack/ReleaseConformance.lean` | Proved API surface with executable checks |
| Speculation theorem API exports | `Runtime/Proofs/VM/Speculation.lean`, `Runtime/Proofs/TheoremPack/API.lean` | Proved interface exports |

## Premise-Scoped Interfaces

| Area | Lean Surface | Interface Type |
|---|---|---|
| Threaded `n > 1` refinement | `ThreadedRoundRefinementPremises` in `Runtime/Proofs/ConcurrencyThreaded.lean` | Premise-scoped |
| Runtime contract admission and profile gates | `Runtime/Proofs/CompileTime/RuntimeContracts.lean` | Interface consumed by runtime gating |
| Theorem-pack capability inventory composition | `Runtime/Proofs/TheoremPack/API.lean` | Interface consumed by admission logic |

These interfaces are explicit and versioned. They are not presented as unconditional global theorems.

## Runtime Alignment Checks

Lean-facing contract checks run through repository scripts and test lanes.

| Check | Path |
|---|---|
| Runtime contract gate shape | `scripts/check-runtime-contract-gates.sh` |
| Speculation/WP surface checks | `scripts/check-speculation-wp-surface.sh` |
| Release conformance checks | `scripts/check-release-conformance.sh` |
| Lean/Rust parity and deviation checks | `scripts/check-parity-ledger.sh`, `scripts/check-vm-parity-suite.sh` |

## Bridge and Fixture Lanes

Bridge correspondence is exercised in `rust/lean-bridge/tests`. VM parity fixtures are exercised in `rust/vm/tests/parity_fixtures_v2.rs` and `rust/vm/tests/threaded_equivalence.rs`.

These lanes enforce practical alignment between executable Rust behavior and Lean theorem/API surfaces.

## Related Docs

- [Lean-Rust Bridge](20_lean_rust_bridge.md)
- [VM Parity Contract](29_vm_parity_contract.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
- [Lean VM Concurrency and Envelope Architecture](37_lean_vm_concurrency_envelope_architecture.md)
