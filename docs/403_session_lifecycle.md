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

`OwnedSession` uses the sealed `owned::OwnedSessionMachine` interface for both
cooperative and threaded machines. Its public operations require an actual issued
`OwnedSession`, rather than serializable capability fields. Both storage adapters borrow the original
resident `SessionState` and execute the same ownership transitions. Threaded
entry is exclusive with respect to machine execution. No worker wave remains
active across that mutable entry. Host code does not receive a raw mutable
threaded session store.

Owned commit, rollback, owner-death and abandoned-transfer operations validate
the calling handle's live capability. Receipt operations also require the
receipt's session to match the calling handle, so possession of an unrelated
session's valid receipt cannot redirect an operation. Rollback removes only the
matching staged claim and preserves its current owner. It does not undo a
previously committed transfer or acknowledge application resource settlement.

Scope attenuation and transfer may preserve or reduce the actual owner's scope.
A fragment owner cannot recover session-wide authority or add other fragments.
Session-local edge mutations reject an edge naming another session. Generations
remain monotonic across release/reclaim, including restored ownership history.
Generation, claim and witness counters fail before mutation when exhausted.
Owner-death and abandoned-transfer paths allocate their required witness before
changing terminal state. Exhaustion therefore leaves the original owner and
staged transfer available for explicit recovery.

Authority records come from the canonical transition producer on both backends.
The store-owned journal records actual cross-session emission order and stamps
owned operations with the current machine tick. It retains genuine rejection
records even when the attempted operation returns an error. Disposal order does
not reorder that history. The threaded journal lock is acquired before mutation.
Poisoning it cannot commit an ownership change without its required audit.
Older cooperative snapshots with only per-session observations retain that
representation without inventing historical emission times or stronger evidence.
Targeted disposal retains those records as historical audit evidence, including
across cooperative snapshot restoration. Repeated disposal does not duplicate
them. Semantic objects, capability lifecycle exports and replay fragments include
the retained records. They cannot reconstruct a live owner or resume a session.

Owned-loader ownership failures retain `OwnershipError` as the source of
`ProtocolMachineError::OwnershipContract`, rather than formatting the cause into
a string. Existing callers matching that variant must handle the typed payload.

## Native worker-pool construction failures

Threaded construction preserves the original Rayon failure and its native I/O
source in ProtocolMachineError::ThreadPoolBuild. Diagnostic text does not replace
the original error chain. This host-construction error precedes admitted protocol
sessions and changes no instruction, capability or protocol outcome.

A failed pool constructor can follow partial native worker startup. Rayon requests
termination on failure but returns no worker-join acknowledgment. The production
owned constructor therefore retains its original native handles alongside the
actual Rayon cause. Only explicit `NativeWorkerPoolBuildFailure::settle_original_workers`
issues the retained join receipt. Observing the constructor error or dropping a
pool does not acknowledge settlement. Targeted session disposal leaves a live
shared pool available and remains a separate acknowledgment.

The original direct-Rayon error fixtures establish their own host-owned joins.
The canonical owned-constructor fixtures additionally exercise the production
handle custodian. Neither fixture family proves signed protocol termination or
settlement of unrelated application resources.

## Session Status Values

`SessionStatus` includes `Active`, `Draining`, `Closed`, `Cancelled`, and `Faulted`.

`Draining` is currently a declared status only. The current `SessionStore::close` path sets `Closed` directly and clears buffers.

## Required Targeted Disposal

`ProtocolMachine::close_and_reap_session` and
`ThreadedProtocolMachine::close_and_reap_session` acknowledge removal of exactly
one resident session and its runnable or blocked coroutine custody. A successful
return leaves no target-session coroutine in live storage or scheduler queues.
Session resources, pending handoffs, and communication-consumption state are
retired, and outstanding target effects are invalidated. Unrelated sessions and
the shared worker pool remain available.

The caller holds exclusive mutable machine ownership. Threaded rounds join every
owned worker job before returning, so disposal acknowledges completed worker
execution as well as removal of scheduling custody. This API neither interrupts
an active handler from another thread nor creates an independent teardown worker.

Residency, stable coroutine indices, required locks, terminal count and epoch
checks precede mutation. Failures return `SessionDisposalError` or
`ThreadedSessionLifecycleError`, without a successful acknowledgment or partial
target removal. Active closure requires a checked epoch increment. An exhausted
active epoch fails closed. Disposal preserves the existing epoch and status of a
naturally Closed, Cancelled or Faulted session. Repeated acknowledgment returns
the original compact archived summary. Reaped coroutine identifiers remain stable
for surviving sessions and are never interpreted as compacted array positions.

Compact summaries and historical observations follow the machine's existing
lifetime archival policy. They are diagnostic history, not resumable sessions or
protocol authority. Target disposal does not clear shared guard resources or
establish successful protocol completion, authenticated cancellation, or
application-level terminal publication. Those obligations remain with the owner
that drives the protocol before disposal.

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

In the canonical capability taxonomy, this lifecycle section spans:

- `ownership` capability state for the live owner
- `transition` lifecycle state for transfer receipts and semantic handoff
- `evidence` lifecycle state for readiness, cancellation, and timeout witnesses

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

Nullifier identity (`ProtocolMachineConfig.communication_nullifier_identity`):

- `sequence_bound` (default): the nullifier covers the full canonical identity, including `sequence_no`. A resent message with a fresh sequence number derives a fresh nullifier and is accepted.
- `content_only`: the nullifier covers the domain tag, `sid`, sender, receiver, step kind, label, and payload digest. `sequence_no` is excluded, so a resend of identical content is rejected with `DuplicateIdentity`. Protocols that legitimately repeat identical content on one edge and label must distinguish those payloads.

Hash model (`ProtocolMachineConfig.communication_hash_model`):

- `HashModel::DEFAULT` uses the built-in portable pseudo-hash, which is deterministic but not collision resistant.
- Security-sensitive embedders supply a cryptographic hash with `HashModel::new(id, hash_fn)` or `HashModel::from_verification_model::<V>(id)`. The model computes payload digests, receive nullifiers, and the replay root.
- Serialized configs and machines record only the model id. Deserialization rejects any id other than the default, so a custom model is never silently replaced by the pseudo-hash. Re-supply custom models programmatically after restore.

Consumed nullifiers are never pruned. Session close drops only per-edge sequence counters, so closing a session cannot re-admit a consumed identity.

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
- Content replay protection: combine `nullifier` mode with `communication_nullifier_identity = content_only` and a cryptographic `communication_hash_model`.

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

- [Protocol-Machine Bytecode Instructions](402_bytecode_instructions.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Bridge and Parity](802_rust_lean_parity.md)

Required host integration coverage is part of `just check-session-disposal`: the
Rust-native inventory requires all 35 nonignored declarations, actual harness
discovery and successful execution across the two binary targets. The ownership
aggregate reuses that gate. Opaque-handle and metadata-substitution compile-fail
doctests additionally protect the public owned API. CI acceptance runs with
`CARGO_INCREMENTAL=0`. This does not change the host's independent cleanup duties.

## Explicit private worker-pool settlement

`ThreadedProtocolMachine::shutdown_worker_pool` consumes the original machine,
requests termination of its private Rayon pool and joins every original native
worker handle retained by the production spawn handler. The returned opaque
`NativeWorkerPoolDisposal` acknowledges those joins, including workers that
terminated with a retained original panic payload. It does not certify protocol
success, signed-terminal publication, or host resource settlement outside that
pool. Callers settle their session obligations before consuming the machine.

This host operation blocks until the actual workers exit. It cannot interrupt a
handler. Ordinary pool Drop remains an unacknowledged termination request.
Construction failures retain the actual Rayon error and partial native worker
handles in `NativeWorkerPoolBuildFailure`. Explicit `settle_original_workers`
joins those original handles and retains the first actual disposal receipt.
Repeated receipt observation neither restarts workers nor consumes panic payloads.

Both normal shutdown and failed construction use the same resident native-worker
settlement custodian. It removes only the next original handle at the consuming
join boundary, without holding its state mutex across the join. Actual worker
panic results acknowledge their completed joins and retain original payloads.
A panic of the join operation itself instead returns retained custody and the
exact panic payload. Its consumed handle remains permanently unproven. Untouched
original handles, completed-join counts and chronological independent causes
survive for same-original retry. Settling those remaining workers cannot erase
the earlier uncertainty or issue a whole-pool acknowledgment.

`NativeWorkerPoolShutdownFailure::OriginalWorker` retains the untouched machine.
`NativeWorkerPoolShutdownFailure::Unproven` retains the native settlement owner.
Failed-constructor settlement returns that same resident owner by reference on
refusal. Every settlement entry rejects an actual original-worker caller, including a still-live worker whose consumed handle has\nunproven settlement, or a
concurrent settler before consuming another handle. Progress snapshots expose
observations and retained causes, never reconstructed authority or cleanup ACK.
No external callback runs under the resident state mutex. The host operation is
still blocking and cannot interrupt a stuck worker or provide async Drop cleanup.

Eleven native component fixtures are required. Five additions exercise injected
unwind at the canonical consuming join boundary, preservation of earlier and
later worker panic causes with real pending workers, same-original remaining
joins, actual-worker refusal, retained consumed-worker identity across unwind, and\nobservation during a pending join. Injection
does not establish an actual operating-system deadlock refusal or settlement of
the handle whose join unwound. Actual compilation and execution remain required.

Shutdown checks the actual original worker handles before requesting termination.
A caller executing on one of those workers receives the unchanged original
machine in the refusal result and must transfer it to an external owning context
for same-original retry. This prevents self-join without discarding custody.

`CARGO_INCREMENTAL=0`. This does not change the host's independent cleanup duties.

## Typed Host Outcome State Commit

InvokeStep and Receive results update coroutine registers only after successful
status and exact response-kind acceptance. The failed instruction does not
advance its continuation, and an attached payload on a failure or blocked result
does not replace the original register file. A raw successful exchange with the
wrong response kind remains observable but is a Failed lifecycle result and
cannot publish effect.succeeded.

This state-commit rule is not a receive-buffer rollback guarantee. It does not
undo a dequeued message, validate a domain label, acknowledge a host future, or
implement a generation-bound asynchronous completion. Those are separate
protocol and host-resource obligations.

VM Invoke and Receive requests retain their actual configured register width as
optional instruction context. All VM state-replacing responses, including branch
Choose/Receive, must preserve that width before register replacement or effect-
success publication. This enforces the canonical Rust `wf_coroutine_state`
register-width invariant, not an inferred equal-length convention. Receive also
retains its actual destination and requires that register to exist. Branch receive
omits the destination because it performs no destination write, but retains width.
Handler-only wrappers omit both instruction contexts. Missing fields on older
serialized requests decode as absent and do not invent historical VM context. The original raw outcome remains observational evidence. This check
is not rollback of earlier buffer dequeue, replay consumption, clock or type work.
Optional observability retention cannot replace an original host failure: the
canonical recorded exchange supplies lifecycle status without a second synthetic
issue/complete cycle. Blocked remains a Blocked observation while the synchronous
instruction reports its existing blocked-contract fault.

Host-response acceptance is distinct from whole-instruction commit. In particular,
Invoke may apply its accepted register state and host-success observation before
persistence-delta application faults. No rollback of that state, emitted events,
or earlier communication work is implied by the response-kind/destination guard.
The prior cooperative owner could evict live enforcement inputs under diagnostic
retention, while the prior threaded owner used untrimmed vectors. The canonical
live/resident retention rule below repairs that storage boundary in both existing
owners. Response/error preservation alone was insufficient. Neither correction
claims nominal authority, a disposal acknowledgment or a Lean correspondence proof.

Serialized request context is an observation used to validate response shape, not
proof of original request ownership or nominal authority. The replay handler
selects by expected entry kind. It does not establish full incoming request
identity. Actual VM producers attach current configured width before execution,
including when replay supplies the response. Lean's abstract effect-context step
and spawn register copying are not a proof of this concrete Rust register ABI.

Canonical host exchanges also supply Acquire/Release/SendDecision outcome
observations directly. Duplicate synthetic issue/complete cycles must not replace
the original typed failure under optional diagnostic retention. Existing policy
is preserved: cooperative Acquire Blocked waits on AcquireDenied, threaded Acquire
Blocked reports its synchronous blocked-contract fault, and Release/SendDecision
Blocked remain synchronous faults. The separate Send buffer WouldBlock producer
retains its actual live capacity obligation: successful host decision is not queue
admission, so that issue/complete pair is not a duplicate host outcome.

Live outstanding effects and their operation/progress records survive Disabled
and Capped observability settings in the same canonical owner fields. Targeted
session invalidation updates those originals before terminal-history pruning.
Other live sessions remain untouched. Retention pruning is not a completion,
cleanup acknowledgment, owner transfer or proof that a host future stopped.

Resident-session terminal records remain canonical inputs to agreement/WAL gates
and cannot be discarded as history. Successful targeted reap or actual closed
session reap establishes their nonresidency before terminal-history pruning.
The next real WalSync gate must see the same original operation and evidence
under Full, Capped1 and Disabled retention. Loss must not silently select the
synthetic fallback operation or its default agreement level.

The composed required native ownership/disposal inventory contains 59 unique
fixtures: the original 35 plus 17 strict-outcome/error, six live/resident retention
and one cooperative full-queue/Disabled regression. The existing canonical checker
requires their nonignored declarations, actual harness discovery and successful
execution. Declarations alone are not passing evidence. Module filters can also
execute required fixtures appearing in a narrower sub-suite, without changing the
unique required count. Authority guard DSL/compiler/bridge fixtures and formal
examples remain separate targets and obligations.

### Authoritative-read reference identity

Readiness and cancellation witness numbers are local to a session. New semantic
exports use opaque content references covering every exported AuthoritativeRead
field except read_id itself: session, owner, kind, lifecycle, predicate, witness
number, generation and reason. Fields have explicit None/Some discriminants and
UTF-8 byte-length framing. Equal complete content may alias. Distinct complete
content does not, including distinct rejected submissions for one witness.
Operation and region read references use those same canonical producer IDs.
These observations do not replace the actual issued witness or its consumption
checks and confer no additional runtime authority.

The v1 semantic-object field schema remains readable: existing unambiguous
serialized references keep their original bytes and can still be looked up.
Lookup accepts repeated identical read records, but rejects different records
under one reference rather than choosing the first. This includes ambiguous
historical cross-session references. No migration reconstructs witness authority
from a reference. Consumers must not parse read-reference strings as a stable
wire grammar. Newly generated references are deliberately session-qualified.
Output-condition references remain content-addressed by predicate and output
digest: identical reobservations are allowed. Contradictory records refuse
lookup. This does not assign an occurrence identity or claim that every check
has a distinct audit event.

### Timeout-witness identifier exhaustion

The cooperative topology timeout producer allocates witness numbers within its
original machine, separately from session-local readiness/cancellation numbers.
It refuses an exhausted successor before replacing an existing timeout, changing
eligibility, or publishing timeout evidence. A returned topology batch is
preflighted for all required witness numbers before any event in that batch is
applied. The host callback's already-observed outcome remains retained. Refusal
does not undo that observation, renew a window or acknowledge pending work.
The existing contract-violation error reports exhaustion. The threaded topology
path currently records timeout horizons without issuing these TimeoutWitness
objects. This correction does not invent threaded witness parity or new
physical-time behavior. SimClock admission and original timeout horizons remain
unchanged.
