# Session Lifecycle

This document defines session state and lifecycle behavior in `rust/vm/src/session.rs` and `rust/vm/src/vm.rs`.

## Session State Model

A session stores role membership, per-endpoint local types, directed buffers, edge handler bindings, trace data, and lifecycle metadata.

| Field group | Purpose |
|---|---|
| `sid`, `roles` | Session identity and participant set |
| `local_types` | Current and original local type for each endpoint |
| `buffers` | Signed directed edge buffers |
| `edge_handlers` | Per-edge runtime handler binding |
| `edge_traces`, auth fields | Coherence and authenticated trace material |
| `status`, `epoch` | Lifecycle phase and close epoch counter |

## Session Status Values

`SessionStatus` includes `Active`, `Draining`, `Closed`, `Cancelled`, and `Faulted`.

`Draining` is currently a declared status only. The current `SessionStore::close` path sets `Closed` directly and clears buffers.

## Open Path

`Open` is executed by `VM::step_open`. The instruction carries `roles`, `local_types`, `handlers`, and `dsts`.

Open admission checks enforce role uniqueness and full handler coverage across the opened role set. Arity must match between `local_types` and `dsts`.

On success the VM allocates a fresh session, initializes buffers and local type entries, stores edge handlers, writes endpoint values to destination registers, and emits an `Opened` event.

## Type Advancement

The session store is the source of truth for endpoint type state. Runtime step logic calls `lookup_type`, `update_type`, `update_original`, and `remove_type`.

Recursive progression uses `unfold_mu`, `unfold_if_var`, and `unfold_if_var_with_scope`. This keeps `Var` continuations aligned with the active recursive body.

## Buffers and Backpressure

Each directed edge has a `BoundedBuffer` configured by `BufferConfig`.

| Config axis | Values |
|---|---|
| Mode | `Fifo`, `LatestValue` |
| Backpressure policy | `Block`, `Drop`, `Error`, `Resize { max_capacity }` |

Signed send and receive paths use endpoint-specific verification keys. Auth tree fields track per-edge authenticated history.

## Close Path

`Close` is executed by `VM::step_close` and then `SessionStore::close`.

The VM first checks endpoint ownership for the closing coroutine. If ownership is valid, the store sets `status = Closed`, clears buffers and edge traces, and increments `epoch`.

Close emits `Closed` and `EpochAdvanced` observable events. There is no automatic draining loop in the current close implementation.

## Related Docs

- [Bytecode Instructions](12_bytecode_instructions.md)
- [VM Architecture](11_vm_architecture.md)
- [VM Parity](15_vm_parity.md)
