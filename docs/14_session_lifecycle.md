# Session Lifecycle

This document defines session state and lifecycle behavior in `rust/machine/src/session/mod.rs` and `rust/machine/src/engine/`.

## Session State Model

A session stores role membership, per-endpoint local types, directed buffers, edge handler bindings, trace data, lifecycle metadata, and host-runtime ownership state.

| Field group | Purpose |
|---|---|
| `sid`, `roles` | Session identity and participant set |
| `local_types` | Current and original local type for each endpoint |
| `buffers` | Signed directed edge buffers |
| `edge_handlers` | Per-edge runtime handler binding |
| `edge_traces`, auth fields | Coherence and authenticated trace material |
| `status`, `epoch` | Lifecycle phase and close epoch counter |
| ownership state | current owner capability, transfer-in-progress state, issued readiness/cancellation/timeout witnesses, consumed witness ids, and terminal ownership reason |

The protocol machine also tracks communication replay-consumption state at runtime scope (`off`, `sequence`, `nullifier`). This state is keyed by session-qualified edges and contributes to canonical replay artifacts.

Ownership fields are a runtime hardening contract rather than a theorem surface. They govern who may drive session-local host mutation and how ownership transfer is staged and audited.

## Session Status Values

`SessionStatus` includes `Active`, `Draining`, `Closed`, `Cancelled`, and `Faulted`.

`Draining` is currently a declared status only. The current `SessionStore::close` path sets `Closed` directly and clears buffers.

## Ownership Lifecycle

Session ownership is tracked separately from capability admission.

| Ownership element | Meaning |
|---|---|
| current owner capability | the live owner label, generation, and authorized scope |
| ownership generation | increments on transfer or scope attenuation so stale handles fail closed |
| pending transfer receipt | explicit staged transfer that must commit or roll back |
| readiness witness | single-use proof that a protocol-critical check succeeded under one live owner generation |
| authority audit log | deterministic issuance, consumption, invalidation, rollback, rejection, and expiry history for first-class ownership/receipt/witness objects |
| terminal ownership reason | recorded reason when owner death or transfer failure forces cancellation or fault |

Default runtime rules:

- at most one current owner exists for one active session ownership unit
- transfer is explicit and uses a receipt
- readiness witnesses are single-use and generation-bound
- timeout activation stores and later expires the exact issued timeout witness rather than reconstructing timeout evidence from ambient clock state
- rollback is claim-specific, so failing one staged transfer does not tear down unrelated ownership state
- fragment-scoped ownership attenuates authority and does not imply full-session mutation rights

## Ownership Failure Mapping

Ownership failures map into session terminal behavior as follows.

| Ownership failure | Runtime behavior |
|---|---|
| owner death | `Faulted { reason = "ownership owner ... died" }` |
| abandoned transfer | `Cancelled` |
| failed transfer commit | `Faulted { reason = "ownership transfer commit failed: ..." }` |
| stale owner use | typed ownership error, fail-closed, no status change unless policy escalates |
| forged or reused readiness witness | typed ownership error, fail-closed, audit rejection record |

These mappings are implementation policy. They are not claims that the Lean theory proves host-runtime ownership outcomes directly.

## Explicit Failure and Timeout Observability

Failure, timeout, and cancellation behavior is now explicit at the semantic-audit surface rather than inferred only from final status.

| Observable event | Meaning |
|---|---|
| `TimeoutIssued` | a timeout occurrence became active for one site and issued a timeout witness |
| `CancellationRequested` | a cancellation path was requested for one session with one cancellation witness |
| `Cancelled` | the explicit cancellation path completed for one session using the same witness |
| `FailureBranchEntered` | a typed failure branch became visible before terminal fault handling |
| `SessionTerminal` | a session reached an explicit terminal state with a deterministic terminal reason |

Deterministic ordering rules:

- timeout activation is recorded as `TimeoutIssued` at the tick where the topology timeout becomes active
- explicit cancellation emits `CancellationRequested`, then `Cancelled`, then `SessionTerminal { Cancelled { ... } }`
- explicit abort emits `Aborted`, then `SessionTerminal { Aborted { ... } }`
- explicit close emits `Closed`, then `SessionTerminal { Closed { ... } }`, then `EpochAdvanced`
- coroutine fault handling emits `FailureBranchEntered` before `Faulted`

These events are part of replay-visible observability. Host integrations should not reconstruct this ordering indirectly from final statuses.

Canonical replay artifacts retain these lifecycle-visible events through `semantic_audit_log`. That surface also includes authority witness issuance/consumption and delegation completion records. The stricter lifecycle export for protocol-critical ownership, receipt, and witness objects is `capability_lifecycle_audit_log()`. Embedders and simulator harnesses should prefer these canonical audit surfaces over custom post-hoc reconstruction from raw logs.
Choreography-level `timeout ... on timeout ... on cancel ...` lowering maps its
protocol-visible timeout and cancellation outcomes to this same explicit lifecycle
event family.

## Semantic Handoff and Transformation Obligations

Committed delegation is now exported as a first-class semantic handoff surface,
not only as a low-level transfer receipt.

| Semantic object | Meaning |
|---|---|
| `SemanticHandoff` | replay-visible owner transition with explicit revoked and activated owners |
| `TransformationObligation` | bundle of fragment, operation, effect, witness, and publication obligations induced by the handoff |

Runtime rules for committed handoff:

- old-owner revocation and new-owner activation are explicit semantic events
- publication authority transfers from `revoked_owner_id` to
  `activated_owner_id`
- pending outstanding effects in the affected session are rebound to the new
  owner
- blocked outstanding effects are invalidated and become late-result-rejecting
  semantic artifacts
- affected `OperationInstance` values gain an explicit dependency edge on the
  handoff receipt and are rebound or failed closed as required by status

`TransformationObligation` is the canonical export for the resulting
transformation-local obligations. Each obligation records:

- transformed fragments
- affected operation ids
- affected effect ids
- transported effect ids
- invalidated effect ids
- witness transport or invalidation policy
- publication revocation and activation owners
- scope, tick, and status

Late results arriving after invalidation or post-handoff revocation must fail
closed. Embedders and simulator harnesses should treat these invalidation
artifacts as canonical semantic audit data rather than reconstructing them from
raw effect trace order.

## Open Path

`Open` is executed by `protocol machine::step_open`. The instruction carries `roles`, `local_types`, `handlers`, and `dsts`.

Open admission checks enforce role uniqueness and full handler coverage across the opened role set. Arity must match between `local_types` and `dsts`.

On success the protocol machine allocates a fresh session, initializes buffers and local type entries, stores edge handlers, writes endpoint values to destination registers, and emits an `Opened` event.

Preferred host integration path:

- ownership-bearing open: `load_choreography_owned(...)`

The open path immediately claims session ownership. It is the public integration route for hosts that will mutate session-local runtime metadata.
Hosts that need to materialize protocol-critical checks should issue explicit readiness witnesses through that ownership-bearing path.
Language-level `check Effect.op(...)` forms are expected to lower into this same
readiness/evidence machinery rather than inventing a separate host-visible
authority cache.

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

`Close` is executed by `protocol machine::step_close` and then `SessionStore::close`.

The protocol machine first checks endpoint ownership for the closing coroutine. If ownership is valid, the store sets `status = Closed`, clears buffers and edge traces, and increments `epoch`.

Close emits `Closed`, `SessionTerminal { Closed { ... } }`, and `EpochAdvanced` observable events. There is no automatic draining loop in the current close implementation.

The close path is distinct from host-runtime ownership transfer. Endpoint/coroutine ownership for bytecode execution remains part of normal protocol-machine execution semantics. Host-runtime ownership governs who may mutate session-local host state at the embedding boundary.

## Migration and Operations

Default behavior:

- `ProtocolMachineConfig.communication_replay_mode` defaults to `off`, preserving prior runtime behavior.
- Existing workloads continue to run without replay-consumption enforcement until mode is changed.

Opt-in guidance:

- Local development: set `communication_replay_mode = sequence` to catch reorder/duplicate transport issues early.
- Strict zk-oriented traces: set `communication_replay_mode = nullifier` to force one-time identity consumption checks.

Why this matters for consensus protocols:

- Protocol-level BFT logic can tolerate many faults. However, zk proofs of full executions require transport-level one-time consumption to prevent replay-equivalent transcript ambiguity.
- Enabling replay-consumption closes this gap between protocol safety and proof transcript soundness.

Configuration examples:

- Local test config: `ProtocolMachineConfig { communication_replay_mode: Sequence, ..ProtocolMachineConfig::default() }`
- CI parity fixture config: set `communication_replay_mode` in both cooperative and threaded runners and compare canonical replay fragments.

Risk notes:

- Performance overhead: replay checks add per-receive hashing and state updates.
- State growth: sequence maps and nullifier sets grow with message volume, session close prunes per-session sequence counters.
- Rollback/restart behavior: replay roots and consumption artifacts are included in canonical replay fragments and should be persisted with other replay evidence.

## Related Docs

- [Protocol-Machine Bytecode Instructions](13_bytecode_instructions.md)
- [Protocol Machine Architecture](12_protocol_machine_architecture.md)
- [Rust-Lean Parity](19_rust_lean_parity.md)
