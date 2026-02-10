# VM State Schema (Lean and Rust)

This document is the strict state-schema reference for VM runtime state.

## Lean Schema

Source: `lean/Runtime/VM/Model/State.lean`

### `CoroutineState`

- `id`, `programId`, `pc`
- `regs`
- `status`
- `effectCtx`
- `ownedEndpoints`
- `progressTokens`
- `knowledgeSet`
- `costBudget`
- `specState`

### `VMState`

- `config`
- `programs`
- `coroutines`
- `sessions`
- `monitor`
- `sched` / scheduler state
- `resourceStates`
- `persistent`
- `obsTrace`
- failure/topology state (`crashedSites`, `partitionedEdges`, `corruptedEdges`, `timedOutSites`)
- output-condition state (`outputConditionChecks`)

## Rust Schema

Source: `rust/vm/src/vm.rs`

### `VM`

- `config`
- `programs` + `code`
- `coroutines`
- `sessions`
- `monitor`
- `sched`
- `resource_states`
- `persistent`
- `obs_trace`
- symbols/clock counters (`role_symbols`, `label_symbols`, `clock`, ids)
- failure/topology state (`crashed_sites`, `partitioned_edges`, `corrupted_edges`, `timed_out_sites`)
- output-condition state (`output_condition_checks`)

### `Coroutine`

Source: `rust/vm/src/coroutine.rs`

- identity/program/pc/status
- register file
- ownership/progress/knowledge sets
- cost budget + speculation metadata
- effect context

## Schema Intent

- Lean and Rust schemas should remain shape-equivalent on safety- and replay-visible fields.
- Runtime-only helper fields are allowed when they do not alter observable semantics.
- Any schema divergence on policy/data encodings must be recorded as a justified deviation.
