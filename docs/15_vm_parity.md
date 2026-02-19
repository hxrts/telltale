# VM Parity

This document defines the Lean/Rust parity contract for VM behavior, state schemas, and deviation governance.

## Contract Levels

Parity is enforced at two levels. Level 1 is policy/data shape parity for shared runtime encodings. Level 2 is behavior parity for executable traces under the declared concurrency envelope.

## Policy and Data Shapes

The following shapes must remain aligned between Lean and Rust unless a deviation entry is active.

| Area | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `FlowPolicy` variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned |
| `FlowPredicate` variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned |
| `OutputConditionPolicy` | `Runtime/VM/Model/OutputCondition.lean` | `rust/vm/src/output_condition.rs` | Aligned |
| Runtime `Value` variants | `Protocol/Values.lean` | `rust/vm/src/coroutine.rs` | Aligned |
| `ProgressToken` fields | `Runtime/VM/Model/State.lean` | `rust/vm/src/coroutine.rs` | Aligned |

These checks are automated by `scripts/check-parity-ledger.sh`.

## Behavior Contract

| Regime | Required Behavior |
|---|---|
| Canonical `n = 1` | Exact parity between cooperative and threaded execution |
| Threaded `n > 1` | Conformance within declared `EnvelopeDiff` bounds |
| Failure-visible artifacts | Snapshot parity within declared failure envelope class |
| Speculation | No sentinel fallback behavior for join/abort with deterministic gated semantics |

These checks are automated by `scripts/check-vm-parity-suite.sh`.

## State Schema

Lean and Rust schemas remain shape-equivalent on safety-visible and replay-visible fields. Runtime-only helper fields are allowed when they do not alter observable semantics.

### Lean VMState

Source: `lean/Runtime/VM/Model/State.lean`

The `CoroutineState` structure contains `id`, `programId`, `pc`, `regs`, `status`, `effectCtx`, `ownedEndpoints`, `progressTokens`, `knowledgeSet`, `costBudget`, and `specState`.

The `VMState` structure contains `config`, `programs`, `coroutines`, `sessions`, `monitor`, `sched`, `resourceStates`, `persistent`, `obsTrace`, failure/topology state fields, and output-condition state.

### Rust VM

Source: `rust/vm/src/vm.rs`

The `VM` structure contains `config`, `programs`, `code`, `coroutines`, `sessions`, `monitor`, `sched`, `resource_states`, `persistent`, `obs_trace`, symbol/clock counters, failure/topology state fields, and output-condition state.

The `Coroutine` structure in `rust/vm/src/coroutine.rs` contains identity/program/pc/status, register file, ownership/progress/knowledge sets, cost budget, speculation metadata, and effect context.

## Runtime Capability Gates

Runtime modes that require theorem/capability evidence are admission gated.

| Gate Surface | Lean API | Rust API | Status |
|---|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_vm_runtime_contracts`, `admit_vm_runtime` | Aligned |
| Determinism profile validation | `requestDeterminismProfile` | `request_determinism_profile` | Aligned |
| Runtime capability snapshot | `runtimeCapabilitySnapshot` | `runtime_capability_snapshot` | Aligned |

The Rust surfaces are in `rust/vm/src/runtime_contracts.rs` and `rust/vm/src/composition.rs`.

## Determinism Profiles

| Profile | Lean | Rust | Status |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | Aligned |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | Aligned |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | Aligned |
| Replay | `replay` | `DeterminismMode::Replay` | Aligned |

`Full` is exact-trace mode. `ModuloEffects` and `ModuloCommutativity` require mixed-profile capability evidence plus artifact support. `Replay` requires replay artifact support and mixed-profile capability evidence.

## Threaded Concurrency Envelope

| Regime | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `n = 1` exact refinement | `runScheduledThreaded_one_eq_runScheduled` | `threaded_equivalence.rs::test_threaded_matches_cooperative` | Aligned |
| Certified-wave fallback | `executeCertifiedRound` | `threaded.rs` wave certificate check with one-step fallback | Aligned |
| `n > 1` envelope-bounded parity | `ThreadedRoundRefinementPremises` (premise-scoped) | `parity_fixtures_v2.rs::envelope_bounded_parity_holds_for_n_gt_1` | Aligned under envelope contract |

## Lean Module Boundaries

The `lean/Runtime/VM` directory is organized into executable and proof modules.

The `Runtime/VM/Model/` directory contains runtime data types, config, state, instruction forms, and event surfaces. The `Runtime/VM/Semantics/` directory contains executable step semantics. The `Runtime/VM/Runtime/` directory contains runtime adapters for loading, JSON, monitoring, and failure ingress.

The `Runtime/VM/API.lean` file provides the stable facade for executable VM API imports. The `Runtime/VM/Composition/` directory contains composition/admission and theorem-pack integration surfaces. The `Runtime/Proofs/` directory contains proof/theorem-pack modules not required for core executable stepping.

Executable modules must not depend on placeholder proof definitions. Proof-only placeholders stay isolated under proof modules. Any executable-path dependency on a stub or placeholder is a release blocker.

## Deviation Governance

Any intentional parity break must be recorded in `docs/lean_vs_rust_deviations.json` before merge. Required fields include `id`, `owner`, `status`, `reason`, `impact`, `alternatives_considered`, `revisit_date`, and `covers`.

Active deviations are tracked in `docs/lean_vs_rust_deviations.json`. Current active entry keeps threaded multi-pick wave rounds as a performance extension. The entry is gated by CI and revisit date ownership.

## CI Gates

The minimum parity governance gates are `scripts/check-parity-ledger.sh`, `scripts/check-vm-parity-suite.sh`, and workflow gates in `.github/workflows/verify.yml` and `.github/workflows/check.yml`.

If any gate fails, parity drift is treated as a release blocker.

## Update Rule

When any parity matrix row changes, update this file and `docs/lean_vs_rust_deviations.json` in the same change set. For any VM PR that changes public runtime behavior, include a parity impact statement in the PR checklist and add differential tests when observable behavior changes.

## Related Docs

- [VM Architecture](11_vm_architecture.md)
- [Bytecode Instructions](12_bytecode_instructions.md)
- [Lean Verification](18_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
