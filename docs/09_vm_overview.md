# VM Overview

This document defines the current VM architecture used by Rust runtime targets and Lean conformance surfaces.

## Architecture Snapshot

The canonical semantic authority is `VMKernel`. The cooperative `VM` and threaded `ThreadedVM` are execution adapters that call kernel-owned step entrypoints.

The runtime keeps a single state model across targets. Core state includes coroutines, sessions, scheduler queues, observable trace, effect trace, and failure-topology snapshot fields.

The canonical round model is one semantic step when concurrency is nonzero. Threaded execution is admitted as an extension only when the wave certificate gate is satisfied.

## Engine Roles

| Engine | Role | Contract Surface |
|---|---|---|
| `VM` | Canonical cooperative runtime | Exact reference for parity at concurrency `1` |
| `ThreadedVM` | Parallel wave executor | Certified-wave execution with fallback to canonical one-step |
| WASM runtime | Single-thread deployment | Cooperative schedule only |

## Runtime Gates

Runtime mode admission and profile selection are capability gated.

| Gate | Runtime Surface | Current Rust Path |
|---|---|---|
| Advanced mode admission | `requires_vm_runtime_contracts` and `admit_vm_runtime` | `rust/vm/src/runtime_contracts.rs`, `rust/vm/src/composition.rs` |
| Determinism profile validation | `request_determinism_profile` | `rust/vm/src/runtime_contracts.rs`, `rust/vm/src/composition.rs` |
| Threaded certified-wave fallback | `WaveCertificate` check with one-step degrade | `rust/vm/src/threaded.rs` |
| Deviation registry enforcement | undocumented parity drift rejection | `scripts/check-parity-ledger.sh` |

## Determinism Profiles

`VMConfig.determinism_mode` now includes `Full`, `ModuloEffects`, `ModuloCommutativity`, and `Replay`.

`Full` is exact-trace mode. `ModuloEffects` and `ModuloCommutativity` require mixed-profile capability evidence plus artifact support. `Replay` requires replay artifact support and mixed-profile capability evidence.

## Conformance Envelope

The project keeps exact parity at concurrency `1`. For `n > 1`, threaded behavior is accepted only inside declared `EnvelopeDiff` classes.

The parity fixture lane verifies speculation behavior, canonical `n = 1` equality, threaded `n > 1` envelope-bounded behavior, and failure-envelope scenarios. The lane is wired through `scripts/check-vm-parity-suite.sh`.

## Proof Boundary

This page describes runtime architecture and executable gates. For theorem-level status, including proved versus premise-scoped surfaces, see [Lean Verification](19_lean_verification.md) and [Lean VM Concurrency and Envelope Architecture](37_lean_vm_concurrency_envelope_architecture.md).

## Related Docs

- [VM Scheduling](11_vm_scheduling.md)
- [VM Parity Contract](29_vm_parity_contract.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
- [Lean VM Concurrency and Envelope Architecture](37_lean_vm_concurrency_envelope_architecture.md)
