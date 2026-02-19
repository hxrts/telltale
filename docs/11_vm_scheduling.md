# VM Scheduling

This document defines the current scheduler semantics and threaded refinement envelope.

## Canonical Round Semantics

Canonical scheduling is one semantic step when concurrency is nonzero. `VMKernel` owns the selection and step contract.

For cooperative execution, this gives exact behavior for deterministic replay and baseline parity. This is the reference surface for Lean and Rust conformance checks.

## Scheduler Policies

Scheduler policy controls selection order. Policy does not change instruction semantics.

| Policy | Primary Runtime Use |
|---|---|
| `Cooperative` | Canonical single-step execution and WASM deployment |
| `RoundRobin` | Fair queue progression in native runs |
| `Priority` | Explicit priority maps or token weighting |
| `ProgressAware` | Token-biased pick behavior |

## Threaded Wave Execution

Threaded execution selects compatible picks per wave. Compatibility is lane-disjoint, session-disjoint, and footprint-disjoint for picks in the same wave.

Each wave is checked against a `WaveCertificate`. If certificate validation fails, the runtime degrades to canonical one-step behavior for that round.

## Refinement Envelope

| Concurrency Regime | Required Contract |
|---|---|
| `n = 1` | Exact canonical parity |
| `n > 1` | Envelope-bounded parity with declared `EnvelopeDiff` |
| Invalid wave certificate | Mandatory fallback to canonical one-step |

The regression lane validates both regimes. `canonical_parity_is_exact_at_concurrency_one` enforces exact equality. `envelope_bounded_parity_holds_for_n_gt_1` enforces envelope-bounded behavior.

## Proved Versus Interface Status

Canonical one-step normalization and `n = 1` refinement are theorem-backed in Lean.

Higher-concurrency threaded refinement is modeled as a certified interface with premise-scoped refinement obligations. Rust uses executable certificate checking and parity fixtures as release guards.

For theorem details, see [Lean VM Concurrency and Envelope Architecture](37_lean_vm_concurrency_envelope_architecture.md).

## Related Docs

- [VM Overview](09_vm_overview.md)
- [VM Parity Contract](29_vm_parity_contract.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
