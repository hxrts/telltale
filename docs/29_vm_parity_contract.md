# VM Parity Contract

This document defines the Lean/Rust parity contract for VM behavior, policy/data encodings, and deviation governance.

## Contract Levels

Parity is enforced at two levels.

Level 1 is policy/data shape parity for shared runtime encodings. Level 2 is behavior parity for executable traces under the declared concurrency envelope.

## Policy/Data Shape Contract

The following shapes must remain aligned between Lean and Rust unless a deviation entry is active.

- `FlowPolicy` and `FlowPredicate`.
- `OutputConditionPolicy`.
- core runtime `Value` variants.
- `ProgressToken` field shape.

These checks are automated by `scripts/check-parity-ledger.sh`.

## Behavior Contract

| Regime | Required Behavior |
|---|---|
| Canonical `n = 1` | Exact parity between cooperative and threaded execution |
| Threaded `n > 1` | Conformance within declared `EnvelopeDiff` bounds |
| Failure-visible artifacts | Snapshot parity within declared failure envelope class |
| Speculation | No sentinel fallback behavior for join/abort; deterministic gated semantics |

These checks are automated by `scripts/check-vm-parity-suite.sh`.

## Runtime Capability and Profile Gates

Runtime modes that require theorem/capability evidence are admission gated.

| Gate | Rust Surface |
|---|---|
| Advanced mode admission | `admit_vm_runtime` in `rust/vm/src/runtime_contracts.rs` |
| Determinism profile selection | `request_determinism_profile` in `rust/vm/src/runtime_contracts.rs` |
| Composition admission enforcement | `rust/vm/src/composition.rs` |

## Deviation Governance

Any intentional parity break must be recorded in `docs/lean_vs_rust_deviations.json` before merge.

Required fields include `id`, `owner`, `status`, `reason`, `impact`, `alternatives_considered`, `revisit_date`, and `covers`. CI fails when a parity mismatch is not covered by an active deviation entry.

## CI Gates

The minimum parity governance gates are:

1. `scripts/check-parity-ledger.sh`.
2. `scripts/check-vm-parity-suite.sh`.
3. workflow wiring in `.github/workflows/verify.yml` and `.github/workflows/check.yml`.

If any gate fails, parity drift is treated as a release blocker.

## Related Docs

- [VM Overview](09_vm_overview.md)
- [VM Scheduling](11_vm_scheduling.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
- [Lean VM Concurrency and Envelope Architecture](37_lean_vm_concurrency_envelope_architecture.md)
