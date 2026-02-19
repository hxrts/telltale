# Lean-Rust Parity Matrix

This matrix tracks current parity status for VM architecture surfaces that are release gated.

## Policy and Data Shapes

| Area | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `FlowPolicy` variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned |
| `FlowPredicate` variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned |
| `OutputConditionPolicy` | `Runtime/VM/Model/OutputCondition.lean` | `rust/vm/src/output_condition.rs` | Aligned |
| Runtime `Value` variants | `Protocol/Values.lean` | `rust/vm/src/coroutine.rs` | Aligned |
| `ProgressToken` fields | `Runtime/VM/Model/State.lean` | `rust/vm/src/coroutine.rs` | Aligned |

## Runtime Capability and Admission Gates

| Gate Surface | Lean API | Rust API | Status |
|---|---|---|---|
| Advanced mode admission | `requiresVMRuntimeContracts`, `admitVMRuntime` | `requires_vm_runtime_contracts`, `admit_vm_runtime` | Aligned |
| Determinism profile validation | `requestDeterminismProfile` | `request_determinism_profile` | Aligned |
| Runtime capability snapshot | `runtimeCapabilitySnapshot` | `runtime_capability_snapshot` | Aligned |

## Determinism Profiles

| Profile | Lean | Rust | Status |
|---|---|---|---|
| Full | `full` | `DeterminismMode::Full` | Aligned |
| Modulo effect trace | `moduloEffectTrace` | `DeterminismMode::ModuloEffects` | Aligned |
| Modulo commutativity | `moduloCommutativity` | `DeterminismMode::ModuloCommutativity` | Aligned |
| Replay | `replay` | `DeterminismMode::Replay` | Aligned |

## Threaded Concurrency Envelope

| Regime | Lean Surface | Rust Surface | Status |
|---|---|---|---|
| `n = 1` exact refinement | `runScheduledThreaded_one_eq_runScheduled` | `threaded_equivalence.rs::test_threaded_matches_cooperative` (concurrency `1`) | Aligned |
| Certified-wave fallback | `executeCertifiedRound` | `threaded.rs` wave certificate check + one-step fallback | Aligned |
| `n > 1` envelope-bounded parity | `ThreadedRoundRefinementPremises` (premise-scoped) | `parity_fixtures_v2.rs::envelope_bounded_parity_holds_for_n_gt_1` | Aligned under envelope contract |

## Active Intentional Divergences

Active deviations are tracked in `docs/lean_vs_rust_deviations.json`.

Current active entry keeps threaded multi-pick wave rounds as a performance extension. The entry is gated by CI and revisit date ownership.

## Enforcement Lanes

- `scripts/check-parity-ledger.sh`
- `scripts/check-vm-parity-suite.sh`
- workflow gates in `.github/workflows/verify.yml` and `.github/workflows/check.yml`

## Update Rule

When any matrix row changes, update this file and `docs/lean_vs_rust_deviations.json` in the same change set.
