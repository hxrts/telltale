# VM Architecture

This document defines the VM architecture, scheduling semantics, and concurrency envelope used by Rust runtime targets and Lean conformance surfaces.

## Architecture Overview

The canonical semantic authority is `VMKernel`. The cooperative `VM` and threaded `ThreadedVM` are execution adapters that call kernel-owned step entrypoints.

The runtime keeps a single state model across targets. Core state includes coroutines, sessions, scheduler queues, observable trace, effect trace, and failure-topology snapshot fields.

The canonical round model is one semantic step when concurrency is nonzero. Threaded execution is admitted as an extension only when the wave certificate gate is satisfied.

## Engine Roles

| Engine | Role | Contract Surface |
|---|---|---|
| `VM` | Canonical cooperative runtime | Exact reference for parity at concurrency `1` |
| `ThreadedVM` | Parallel wave executor | Certified-wave execution with fallback to canonical one-step |
| WASM runtime | Single-thread deployment | Cooperative schedule only |

## Scheduler Semantics

Canonical scheduling is one semantic step when concurrency is nonzero. `VMKernel` owns the selection and step contract. For cooperative execution, this gives exact behavior for deterministic replay and baseline parity.

The canonical Lean runner is `runScheduled` in `Runtime/VM/Runtime/Runner.lean`. For nonzero concurrency, canonical round semantics normalize to one scheduler step. This model is the semantic reference for parity at concurrency `1`.

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

The threaded extension is defined in `Runtime/VM/Runtime/ThreadedRunner.lean`. Concurrency `n = 1` is theorem-equal to canonical execution. For `n > 1`, execution is admitted through certified waves. Invalid certificates degrade to canonical one-step behavior.

Each wave is checked against a `WaveCertificate`. If certificate validation fails, the runtime degrades to canonical one-step behavior for that round.

## Refinement Envelope

| Concurrency Regime | Required Contract | Enforcement Lane |
|---|---|---|
| `n = 1` | Exact canonical parity | `threaded_equivalence.rs` |
| `n > 1` | Envelope-bounded parity with declared `EnvelopeDiff` | `parity_fixtures_v2.rs` |
| Invalid wave certificate | Mandatory fallback to canonical one-step | `threaded_lane_runtime.rs` |
| Undocumented deviation | Active deviation coverage required | `scripts/check-parity-ledger.sh` |

The regression lane validates both regimes. The test `canonical_parity_is_exact_at_concurrency_one` enforces exact equality. The test `envelope_bounded_parity_holds_for_n_gt_1` enforces envelope-bounded behavior.

## Runtime Gates

Runtime mode admission and profile selection are capability gated.

| Gate | Runtime Surface | Current Rust Path |
|---|---|---|
| Advanced mode admission | `requires_vm_runtime_contracts` and `admit_vm_runtime` | `rust/vm/src/runtime_contracts.rs`, `rust/vm/src/composition.rs` |
| Determinism profile validation | `request_determinism_profile` | `rust/vm/src/runtime_contracts.rs`, `rust/vm/src/composition.rs` |
| Threaded certified-wave fallback | `WaveCertificate` check with one-step degrade | `rust/vm/src/threaded.rs` |
| Deviation registry enforcement | Undocumented parity drift rejection | `scripts/check-parity-ledger.sh` |

## Capability Gate Architecture

| Capability Gate | Lean Surface | Rust Surface |
|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_vm_runtime_contracts`, `admit_vm_runtime` |
| Live migration switch | `requestLiveMigration` | Runtime contracts capability booleans in composition admission |
| Autoscale/repartition switch | `requestAutoscaleOrRepartition` | Runtime contracts capability booleans in composition admission |
| Placement refinement switch | `requestPlacementRefinement` | Runtime contracts capability booleans in composition admission |
| Relaxed reordering switch | `requestRelaxedReordering` | Runtime contracts capability booleans in composition admission |

## Determinism Profiles

`VMConfig.determinism_mode` includes `Full`, `ModuloEffects`, `ModuloCommutativity`, and `Replay`.

| Profile | Lean Profile | Rust Profile | Gate Requirement |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | Profile artifact support |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | Mixed-profile capability plus artifact support |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | Mixed-profile capability plus artifact support |
| Replay | `replay` | `DeterminismMode::Replay` | Mixed-profile capability plus artifact support |

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

These interfaces are intentionally explicit. They are not claimed as unconditional global theorems. Canonical one-step normalization and `n = 1` refinement are theorem-backed in Lean. Higher-concurrency threaded refinement is modeled as a certified interface with premise-scoped refinement obligations. Rust uses executable certificate checking and parity fixtures as release guards.

## Release and CI Conformance

Release conformance surfaces are exported through theorem-pack APIs and enforced by `scripts/check-release-conformance.sh`. Parity and drift governance are enforced by `scripts/check-vm-parity-suite.sh` and `scripts/check-parity-ledger.sh`.

## Related Docs

- [Bytecode Instructions](12_bytecode_instructions.md)
- [Session Lifecycle](13_session_lifecycle.md)
- [VM Simulation](14_vm_simulation.md)
- [VM Parity](15_vm_parity.md)
- [Lean Verification](18_lean_verification.md)
