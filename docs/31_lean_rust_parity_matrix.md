# Lean/Rust Parity Matrix

This matrix is required to be updated in every VM PR that changes behavior or encoding.

## Policy/Data Encoding Parity

| Area | Lean | Rust | Parity Status | Notes |
|---|---|---|---|---|
| FlowPolicy variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned | Includes dynamic predicate + serializable predicate expr |
| FlowPredicate variants | `Runtime/VM/Model/Knowledge.lean` | `rust/vm/src/vm.rs` | Aligned | `targetRolePrefix`, `factContains`, `endpointRoleMatchesTarget`, `all`, `any` |
| OutputConditionPolicy variants | `Runtime/VM/Model/OutputCondition.lean` | `rust/vm/src/output_condition.rs` | Aligned | `disabled`, `allowAll`, `denyAll`, `predicateAllowList` |
| Core `Value` variants | `Protocol/Values.lean` | `rust/vm/src/coroutine.rs` | Aligned | Lean-compatible runtime value surface only |
| `ProgressToken` field shape | `Runtime/VM/Model/State.lean` | `rust/vm/src/coroutine.rs` | Aligned | `{sid, endpoint}` |
| Default observable predicate | `vm.observable_output` | `vm.observable_output` | Aligned | Default when host provides no explicit hint |

## Runtime Behavior Parity (Tracked)

| Area | Lean | Rust | Status |
|---|---|---|---|
| `check` flow-policy evaluation | `ExecOwnership.stepCheck` | VM `Check` execution path | In progress |
| Output-condition commit gate | `Semantics.Exec` + model policy | `vm.rs` + `output_condition.rs` | In progress |
| Monitor precheck | `Runtime/VM/Runtime/Monitor.lean` | `vm.rs`/`threaded.rs` monitor paths | In progress |
| Failure/topology ingress | `Runtime/VM/Runtime/Failure.lean` | `effect.rs` + VM ingestion paths | In progress |

## PR Update Rule

When any row changes:

1. Update this matrix row.
2. Update `docs/lean_vs_rust_deviations.json` if parity is intentionally broken.
3. Link the exact test(s) that validate the new state.
