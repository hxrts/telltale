# Lean VM Concurrency and Envelope Architecture

This document is the final architecture reference for concurrency, capability gates, and envelope-bounded refinement.

## Scope

This page covers executable scheduler semantics, theorem/API boundaries, and cross-target conformance requirements.

It distinguishes proved theorem surfaces from premise-scoped interfaces.

## Canonical Scheduler Model

The canonical Lean runner is `runScheduled` in `Runtime/VM/Runtime/Runner.lean`.

For nonzero concurrency, canonical round semantics normalize to one scheduler step. This model is the semantic reference for parity at concurrency `1`.

## Threaded Extension Model

The threaded extension is defined in `Runtime/VM/Runtime/ThreadedRunner.lean`.

`n = 1` is theorem-equal to canonical execution. For `n > 1`, execution is admitted through certified waves, and invalid certificates degrade to canonical one-step behavior.

## Proved Theorem Surfaces

| Area | Lean Surface | Status |
|---|---|---|
| Canonical round normalization | `Runtime/Proofs/Concurrency.lean` | Proved |
| Threaded equality at `n = 1` | `schedRoundThreaded_one_eq_schedRound_one`, `runScheduledThreaded_one_eq_runScheduled` | Proved |
| Per-session trace equality at `n = 1` | `per_session_trace_threaded_one_eq_canonical` | Proved |
| Scheduler theorem exports | `Runtime/Proofs/VM/Scheduler.lean` | Proved |

## Premise-Scoped Interface Surfaces

| Area | Lean Surface | Interface Type |
|---|---|---|
| Threaded `n > 1` refinement | `ThreadedRoundRefinementPremises` | Premise-scoped |
| Runtime admission/profile gates | `Runtime/Proofs/CompileTime/RuntimeContracts.lean` | Interface consumed by runtime |
| Theorem-pack capability inventory APIs | `Runtime/Proofs/TheoremPack/API.lean` | Interface consumed by runtime |

These interfaces are intentionally explicit. They are not claimed as unconditional global theorems.

## Capability Gate Architecture

| Capability Gate | Lean Surface | Rust Surface |
|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_vm_runtime_contracts`, `admit_vm_runtime` |
| Live migration switch | `requestLiveMigration` | runtime contracts capability booleans in composition admission |
| Autoscale/repartition switch | `requestAutoscaleOrRepartition` | runtime contracts capability booleans in composition admission |
| Placement refinement switch | `requestPlacementRefinement` | runtime contracts capability booleans in composition admission |
| Relaxed reordering switch | `requestRelaxedReordering` | runtime contracts capability booleans in composition admission |

## Determinism Profile Architecture

| Profile | Lean Profile | Rust Profile | Gate Requirement |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | profile artifact support |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | mixed-profile capability plus artifact support |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | mixed-profile capability plus artifact support |
| Replay | `replay` | `DeterminismMode::Replay` | mixed-profile capability plus artifact support |

## Threaded Refinement Envelope Table

| Regime | Required Contract | Enforcement Lane |
|---|---|---|
| Concurrency `1` | exact canonical parity | `threaded_equivalence.rs` |
| Concurrency `n > 1` | envelope-bounded conformance | `parity_fixtures_v2.rs` |
| Certified-wave validity failure | fallback to canonical one-step | `threaded_lane_runtime.rs::invalid_wave_certificate_falls_back_to_single_step` |
| Undocumented deviation prevention | active deviation coverage required | `scripts/check-parity-ledger.sh` |

## Release and CI Conformance

Release conformance surfaces are exported through theorem-pack APIs and enforced by `scripts/check-release-conformance.sh`.

Parity and drift governance are enforced by `scripts/check-vm-parity-suite.sh` and `scripts/check-parity-ledger.sh`.

## Related Docs

- [VM Overview](09_vm_overview.md)
- [VM Scheduling](11_vm_scheduling.md)
- [Lean Verification](19_lean_verification.md)
- [VM Parity Contract](29_vm_parity_contract.md)
- [Lean-Rust Parity Matrix](31_lean_rust_parity_matrix.md)
