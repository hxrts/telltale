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

The VM also tracks communication replay-consumption state at runtime scope (`off`, `sequence`, `nullifier`). This state is keyed by session-qualified edges and contributes to canonical replay artifacts.

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

## Communication Replay-Consumption Lifecycle

Communication replay-consumption is separate from resource nullifiers and is enforced at communication boundaries.

| Phase | Runtime location | Behavior |
|---|---|---|
| Create sequence identity | send path (`step_send`) | Allocates `sequence_no` per session-qualified edge and writes it into signed transport payloads |
| Verify and consume | receive path (`step_recv`) | Verifies signature first, then applies replay policy (`off`, `sequence`, `nullifier`) on canonical identity |
| Record proof artifact | receive commit path | Appends pre-root/post-root artifact entries for recursive proof composition |
| Finalize on close | session close path | Prunes per-session replay counters from in-memory tracker state |

Policy semantics:

- `off`: replay-consumption checks disabled.
- `sequence`: requires exact next sequence number per edge.
- `nullifier`: rejects duplicate canonical identities via consumed nullifier set.

## Close Path

`Close` is executed by `VM::step_close` and then `SessionStore::close`.

The VM first checks endpoint ownership for the closing coroutine. If ownership is valid, the store sets `status = Closed`, clears buffers and edge traces, and increments `epoch`.

Close emits `Closed` and `EpochAdvanced` observable events. There is no automatic draining loop in the current close implementation.

## Migration and Operations

Default behavior:

- `VMConfig.communication_replay_mode` defaults to `off`, preserving prior runtime behavior.
- Existing workloads continue to run without replay-consumption enforcement until mode is changed.

Opt-in guidance:

- Local development: set `communication_replay_mode = sequence` to catch reorder/duplicate transport issues early.
- Strict zk-oriented traces: set `communication_replay_mode = nullifier` to force one-time identity consumption checks.

Why this matters for consensus protocols:

- Protocol-level BFT logic can tolerate many faults, but zk proofs of full executions require transport-level one-time consumption to prevent replay-equivalent transcript ambiguity.
- Enabling replay-consumption closes this gap between protocol safety and proof transcript soundness.

Configuration examples:

- Local test config: `VMConfig { communication_replay_mode: Sequence, ..VMConfig::default() }`
- CI parity fixture config: set `communication_replay_mode` in both cooperative and threaded runners and compare canonical replay fragments.

Risk notes:

- Performance overhead: replay checks add per-receive hashing and state updates.
- State growth: sequence maps and nullifier sets grow with message volume, session close prunes per-session sequence counters.
- Rollback/restart behavior: replay roots and consumption artifacts are included in canonical replay fragments and should be persisted with other replay evidence.

## Related Docs

- [Bytecode Instructions](13_bytecode_instructions.md)
- [VM Architecture](12_vm_architecture.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
