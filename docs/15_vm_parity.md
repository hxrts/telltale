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
| Payload hardening controls (`payload_validation_mode`, `max_payload_bytes`) | no executable admission gate in baseline Lean runner | `rust/vm/src/vm.rs` | Runtime-only extension (documented deviation) |

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

### Deviation Registry

| ID | Status | Owner | Revisit | Summary |
|----|--------|-------|---------|---------|
| threaded-round-extension | resolved | vm-runtime | 2026-04-30 | Threaded backend defaults to canonical one-step rounds |
| payload-hardening-extension | active | vm-runtime | 2026-06-30 | Rust VM adds configurable payload-admission checks for malformed/adversarial message values |

### Deviation Details

#### threaded-round-extension

**Lean:** `Runtime/VM/Runtime/Runner.lean`
**Rust:** `rust/vm/src/threaded.rs`

**Reason:** VMConfig now exposes `threaded_round_semantics` and defaults to canonical one-step semantics aligned with Lean.

**Impact:** No active parity divergence remains for default threaded execution; multi-pick wave mode is now an explicit opt-in extension.

**Alternatives considered:** Keeping wave-parallel semantics as default was rejected because it kept parity drift in the baseline runner path.

**Covers:** `threaded.round.wave.parallelism`

**Tests:**
- `rust/vm/tests/topology_effect_ingress.rs::cooperative_vm_ingests_topology_events_before_instruction_effects`
- `rust/vm/tests/threaded_lane_runtime.rs`
- `rust/vm/tests/parity_fixtures_v2.rs::envelope_bounded_parity_holds_for_n_gt_1`

#### payload-hardening-extension

**Lean:** Baseline executable semantics assume well-formed value flows for typed transitions.
**Rust:** `rust/vm/src/vm.rs`, `rust/vm/src/threaded.rs` add `VMConfig.payload_validation_mode` and `VMConfig.max_payload_bytes` runtime checks.

**Reason:** Integrations often run in environments where peers may construct malformed payloads. VM-level admission checks avoid requiring each integrator to hand-write custom guards.

**Impact:** For well-formed traces, behavior is parity-preserving. For malformed/adversarial payload traces, Rust may reject earlier via `Fault::TypeViolation` under `structural`/`strict_schema` modes.

**Alternatives considered:** Integrator-only guard implementations and codegen-only validation were rejected as insufficiently uniform at the VM boundary.

**Covers:** `runtime.payload.admission`, `runtime.payload.size_bound`, `runtime.payload.strict_schema`

**Tests:**
- `rust/vm/src/vm.rs::tests::test_payload_validation_structural_rejects_annotated_type_mismatch`
- `rust/vm/src/vm.rs::tests::test_payload_validation_off_allows_annotated_type_mismatch_for_compatibility`
- `rust/vm/src/vm.rs::tests::test_payload_validation_strict_schema_requires_annotations_for_send_recv`
- `rust/vm/src/vm.rs::tests::test_payload_validation_size_bound_rejects_oversized_payloads`

## CI Gates

The minimum parity governance gates are `scripts/check-parity-ledger.sh`, `scripts/check-vm-parity-suite.sh`, and workflow gates in `.github/workflows/verify.yml` and `.github/workflows/check.yml`.

If any gate fails, parity drift is treated as a release blocker.

## Performance SLA

Runtime performance governance enforces explicit thresholds from `artifacts/v2/benchmark_matrix/summary.json` in `scripts/check-runtime-performance-governance.sh`.

- `TT_SLA_THROUGHPUT_RATIO_MIN` (default `1.0`)
- `TT_SLA_P99_REGRESSION_MAX_PERCENT` (default `15.0`)
- `TT_SLA_LOCK_CONTENTION_REDUCTION_MIN_PERCENT` (default `50.0`)

If any threshold is violated, CI fails before benchmark lanes are considered healthy.

## Update Rule

When any parity matrix row changes, update the Deviation Registry table in this file in the same change set. For any VM PR that changes public runtime behavior, include a parity impact statement in the PR checklist and add differential tests when observable behavior changes.

## Naming Compatibility

Rust VM includes explicit Lean-compatibility wrappers such as `openDelta`, `siteName`, and `signValue`.
These wrappers intentionally keep Lean-facing casing and therefore retain focused `#[allow(non_snake_case)]` annotations in `guard.rs`, `identity.rs`, `persistence.rs`, and `verification.rs`.

## Related Docs

- [VM Architecture](11_vm_architecture.md)
- [Bytecode Instructions](12_bytecode_instructions.md)
- [Lean Verification](18_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
