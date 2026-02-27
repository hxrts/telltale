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
| `CommunicationReplayMode` variants | `Runtime/VM/Model/Config.lean` | `rust/vm/src/communication_replay.rs` | Aligned |
| `SignedValue` transport fields (`payload`, `signature`, `sequence_no`) | `Runtime/VM/Model/TypeClasses.lean` | `rust/vm/src/buffer.rs` | Aligned |
| Payload hardening controls (`payload_validation_mode`, `max_payload_bytes`) | `Runtime/VM/Model/Config.lean`, `Runtime/VM/Semantics/ExecComm.lean` | `rust/vm/src/vm.rs` | Aligned |
| Register bounds failure semantics (`OutOfRegisters`) | `Runtime/VM/Semantics/ExecSteps.lean` | `rust/vm/src/vm`, `rust/vm/src/threaded` | Aligned |

These checks are automated by `just check-parity --types`.

## Behavior Contract

| Regime | Required Behavior |
|---|---|
| Canonical `n = 1` | Exact parity between cooperative and threaded execution |
| Threaded `n > 1` | Conformance within declared `EnvelopeDiff` bounds |
| Failure-visible artifacts | Snapshot parity within declared failure envelope class |
| Speculation | No sentinel fallback behavior for join/abort with deterministic gated semantics |
| Register bounds | Out-of-range register operands fail with `OutOfRegisters` (no unchecked panic paths) |
| Load boundary | Runtime rejects malformed trusted image role/type shape before session open |

These checks are automated by `just check-parity --suite`.

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
| Spawn step parity (`n = 1`) | `Runtime/VM/Semantics/ExecControl.lean`, `Runtime/VM/Semantics/ExecSteps.lean` | `differential_step_corpus.rs::threaded_matches_cooperative_step_corpus_control_spawn` | Aligned |
| Certified-wave fallback | `executeCertifiedRound` | `threaded.rs` wave certificate check with one-step fallback | Aligned |
| `n > 1` envelope-bounded parity | `ThreadedRoundRefinementPremises` (premise-scoped) | `parity_fixtures_v2.rs::envelope_bounded_parity_holds_for_n_gt_1` | Aligned under envelope contract |

## Simulator Material Mirror

Lean now includes executable mirror dynamics for simulator material handlers under `lean/Runtime/Simulation/`.
Rust material handlers live under `rust/simulator/src/material_handlers/`.

Parity fixtures are enforced by:

- `rust/simulator/tests/material_handler_parity.rs`
- `lean/Runtime/Tests/SimulatorParity.lean` (built as `simulator_parity_tests`)

## Lean Module Boundaries

The `lean/Runtime/VM` directory is organized into executable and proof modules.

The `Runtime/VM/Model/` directory contains runtime data types, config, state, instruction forms, and event surfaces. The `Runtime/VM/Semantics/` directory contains executable step semantics. The `Runtime/VM/Runtime/` directory contains runtime adapters for loading, JSON, monitoring, and failure ingress.

The `Runtime/VM/API.lean` file provides the stable facade for executable VM API imports. The `Runtime/VM/Composition/` directory contains composition/admission and theorem-pack integration surfaces. The `Runtime/Proofs/` directory contains proof/theorem-pack modules not required for core executable stepping.

Executable modules must not depend on placeholder proof definitions. Proof-only placeholders stay isolated under proof modules. Any executable-path dependency on a stub or placeholder is a release blocker.

## Deviation Governance

Any intentional parity break must be recorded in the deviation table below before merge. Required fields include id, owner, status, reason, impact, alternatives considered, revisit date, and coverage scope.

### Deviation Registry (Active)

| ID | Status | Owner | Revisit | Summary |
|----|--------|-------|---------|---------|
| _none_ | _n/a_ | _n/a_ | _n/a_ | No active VM parity deviations |

Resolved deviations move to history after one stable release cycle with no regressions on the covered surfaces.

### Resolved Deviation History

| ID | Status | Owner | Moved On | Summary |
|----|--------|-------|----------|---------|
| threaded-round-extension | resolved | vm-runtime | 2026-02-27 | Threaded backend defaults to canonical one-step rounds |
| payload-hardening-extension | resolved | vm-runtime | 2026-02-27 | Lean and Rust now enforce payload-size admission on executable send/receive paths and strict-schema annotation rejection on annotationless send/receive shapes |
| comm-replay-label-context | resolved | vm-runtime | 2026-02-27 | Rust receive replay identity now canonicalizes to the Lean-style typed-context label token when session payload annotation is available |
| types-merge-payload-annotation | resolved | types-parity | 2026-02-27 | Lean canonical merge now enforces payload-annotation compatibility on overlapping send/recv labels and exposes matching soundness at the compatibility-gated entrypoint |
| types-content-id-closedness | resolved | types-parity | 2026-02-27 | Lean now exposes explicit closed-only canonical identity and open-term template identity policy surfaces with proofs matching Rust `content_id`/`template_id` contract |
| types-local-db-payload-retention | resolved | types-parity | 2026-02-27 | Lean payload-preserving DB conversion is promoted via parity surfaces with explicit success-equivalence bridge theorems to legacy erased conversion |
| theory-async-subtyping-conservative | resolved | theory-parity | 2026-02-27 | Lean and Rust both expose conservative executable async-subtyping with cross-validation tests |
| theory-orphan-free-conservative | resolved | theory-parity | 2026-02-27 | Lean and Rust both expose conservative executable orphan-freedom with cross-validation tests |

### Deviation Details (Active)

### Resolved Deviation Notes

#### threaded-round-extension

**Lean:** `Runtime/VM/Runtime/Runner.lean`
**Rust:** `rust/vm/src/threaded.rs`

**Resolution:** VMConfig exposes `threaded_round_semantics` and defaults to canonical one-step semantics aligned with Lean.

**Covers:** `threaded.round.wave.parallelism`

#### payload-hardening-extension

**Lean:** `lean/Runtime/VM/Model/Config.lean`, `lean/Runtime/VM/Semantics/ExecComm.lean`
**Rust:** `rust/vm/src/vm.rs`, `rust/vm/src/threaded.rs`, `rust/vm/tests/parity_fixtures_v2.rs`

**Resolution:** Lean and Rust both expose executable payload-size admission controls. Lean now emits strict-schema annotation rejection on annotationless single-branch send/receive shapes, and parity fixtures cover oversized payload rejection behavior at canonical concurrency.

**Covers:** `runtime.payload.admission`, `runtime.payload.size_bound`, `runtime.payload.strict_schema`

#### comm-replay-label-context

**Lean:** `Runtime/VM/Semantics/ExecComm.lean`, `Runtime/VM/Model/State.lean`
**Rust:** `rust/vm/src/vm/instruction_control_and_effects.rs`, `rust/vm/src/threaded/instructions_send_recv_control.rs`, `rust/vm/src/communication_replay.rs`

**Resolution:** Rust receive replay identity now canonicalizes to typed-context replay labels (`recv:<ValType>`) when expected payload annotations are present, matching Lean receive identity construction.

**Covers:** `comm.replay.identity.label_context`

#### types-merge-payload-annotation

**Lean:** `lean/Choreography/Projection/Erasure/Merge.lean`, `lean/Choreography/Projection/Erasure/PayloadCompat.lean`, `lean/Choreography/Projection/Erasure/MergeSoundness.lean`
**Rust:** `rust/types/src/merge.rs`

**Resolution:** Lean `merge` is now compatibility-gated directly via `payloadAnnotationsCompatible`, `mergeWithPayloadCompat` is a stable alias to canonical `merge`, and `merge_with_payload_compat_sound` proves soundness at the compatibility-gated entrypoint.

**Covers:** `types.merge.payload_annotation.compatibility`

#### types-content-id-closedness

**Lean:** `lean/SessionTypes/ContentIdentityPolicy.lean`
**Rust:** `rust/types/src/contentable.rs`

**Resolution:** Lean now exposes executable closed-only canonical identity surfaces (`globalToCanonicalIdentityBytes?`, `localToCanonicalIdentityBytes?`) and open-term template identity surfaces (`globalToTemplateIdentityBytes`, `localToTemplateIdentityBytes`) plus proofs that canonical identity is admitted iff terms are closed/all-bound.

**Covers:** `types.content_id.closed_only`

#### types-local-db-payload-retention

**Lean:** `lean/SessionTypes/LocalTypeDB/Annotated.lean`, `lean/SessionTypes/LocalTypeConv.lean`, `lean/SessionTypes/LocalTypeConvProofs/PayloadParityBridge.lean`
**Rust:** `rust/types/src/de_bruijn.rs`, `rust/types/src/contentable.rs`

**Resolution:** Lean `LocalTypeDBAnn` is promoted via parity-facing conversion surfaces (`toDBParity?`, `fromDBParity`, `toDBParity_closed_safe`). Bridge theorems now prove success/failure equivalence between payload-preserving and legacy erased conversion (`to_db_ann_is_some_eq_to_db_is_some`) and provide lift witnesses from erased-success to payload-preserving success (`to_db_lifts_to_db_ann`).

**Covers:** `types.local_db.payload_annotation.retention`

#### theory-async-subtyping-conservative

**Lean:** `lean/SessionTypes/LocalTypeR/AsyncSubtype.lean`, `lean/Choreography/Projection/Validator.lean`
**Rust:** `rust/theory/src/subtyping/async.rs`, `rust/lean-bridge/src/runner_projection_export.rs`

**Resolution:** Lean and Rust now expose matching conservative executable async-subtyping with parity tests.

**Covers:** `theory.async_subtyping.conservative_subset`

#### theory-orphan-free-conservative

**Lean:** `lean/SessionTypes/LocalTypeR/AsyncSubtype.lean`, `lean/Choreography/Projection/Validator.lean`
**Rust:** `rust/theory/src/subtyping/async.rs`, `rust/lean-bridge/src/runner_projection_export.rs`

**Resolution:** Lean and Rust now expose matching conservative executable orphan-freedom with parity tests.

**Covers:** `theory.orphan_free.conservative_local_check`

#### conservative-async-subtyping-contract

Conservative async-subtyping (Lean and Rust) is intentionally phase- and tree-structural:

- SISO decomposition must succeed on both sides under bounded unfolding.
- Subtype and supertype must have equal phase counts.
- Each aligned phase must satisfy input-tree and output-tree structural compatibility.
- Empty behavior (`End`) only matches supertypes with empty phase decomposition under this conservative contract.

## CI Gates

The minimum parity governance gates are `just check-parity --all`, `just check-release-conformance`, and workflow gates in `.github/workflows/verify.yml` and `.github/workflows/check.yml`.

If any gate fails, parity drift is treated as a release blocker.

## Performance SLA

Runtime performance governance enforces explicit thresholds from `artifacts/v2/benchmark_matrix/summary.json` through `just v2-baseline sla`.

- `TT_SLA_THROUGHPUT_RATIO_MIN` (default `1.0`)
- `TT_SLA_P99_REGRESSION_MAX_PERCENT` (default `15.0`)
- `TT_SLA_LOCK_CONTENTION_REDUCTION_MIN_PERCENT` (default `50.0`)

If any threshold is violated, CI fails before benchmark lanes are considered healthy.

## Update Rule

When any parity matrix row changes, update the Deviation Registry table in this file in the same change set. For any VM PR that changes public runtime behavior, include a parity impact statement in the PR checklist and add differential tests when observable behavior changes.

## Type-Level Parity Checklist

Every Rust PR that changes type semantics must include this checklist in the PR description.

1. List affected Rust modules under `rust/types/src/`.
2. List corresponding Lean modules reviewed for parity.
3. State whether behavior is aligned or intentionally divergent.
4. If divergent, add or update a Deviation Registry entry in this document.
5. Link tests that cover new behavior and edge cases.

## Naming Compatibility

Rust VM includes explicit Lean-compatibility wrappers such as `openDelta`, `siteName`, and `signValue`.
These wrappers intentionally keep Lean-facing casing and therefore retain focused `#[allow(non_snake_case)]` annotations in `guard.rs`, `identity.rs`, `persistence.rs`, and `verification.rs`.

## Related Docs

- [VM Architecture](12_vm_architecture.md)
- [Bytecode Instructions](13_bytecode_instructions.md)
- [Lean Verification](23_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
