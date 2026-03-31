# Protocol-Critical Authority and Evidence

This page defines what counts as protocol-critical authority in Telltale and
how evidence-bearing decisions are expected to behave.

## Scope

Telltale owns protocol-critical authority flow. It does not own arbitrary host
application state.
More concretely: first-class protocol-critical capability semantics are in
scope; general host application authorization is out of scope.

Use Telltale authority/evidence features when:

- the decision changes protocol control flow
- the decision must be replayable or auditable
- missing authority must fail closed instead of falling back silently
- the decision needs typed success/failure semantics

Keep logic in the host when:

- it is ordinary UI/application state with no protocol meaning
- it does not affect protocol-visible branching
- replay/audit semantics are not required

## Core Concepts

| Term | Meaning |
|---|---|
| authority | the right to drive a protocol-critical action |
| capability | the current runtime token that proves live authority |
| evidence | typed proof object consumed by a protocol-critical branch |
| receipt | typed proof that a transfer or handoff was staged/committed |
| typed failure | an explicit `Err`, cancellation, or timeout outcome rather than host-local absence |

Protocol-critical authority/evidence objects are intentionally linear. They do
not become valid by convention or post-hoc reconstruction. The runtime issues,
consumes, invalidates, rolls back, rejects, or expires explicit objects and
exports those transitions through one stable lifecycle audit surface:

- `ProtocolMachine::capability_lifecycle_audit_log()`
- `ThreadedGuestRuntime::capability_lifecycle_audit_log()`
- `telltale_machine::capability_lifecycle_audit_log_v1(...)`

## Canonical Capability Classes

Telltale's first-class capability model is intentionally narrow.

| Class | Main question | Current examples |
|---|---|---|
| `admission` | may this runtime/profile/configuration run at all? | theorem-pack eligibility, runtime contracts, determinism profile gates |
| `ownership` | who may currently mutate one live session or fragment? | `OwnershipCapability` |
| `evidence` | why is a protocol-critical branch or finalization step justified? | `ReadinessWitness`, `AuthoritativeRead`, `MaterializationProof`, `CanonicalHandle` |
| `transition` | what explicit object authorizes handoff, cutover, or reconfiguration? | `OwnershipReceipt`, semantic handoff, reconfiguration transition artifacts |

The canonical Rust source-of-truth boundary for these classes is:

- `rust/machine/src/capabilities.rs`
- `rust/machine/src/runtime_contracts.rs`
- `rust/machine/src/session/overview.rs`
- `rust/machine/src/semantic_objects.rs`
- `rust/machine/src/composition.rs`

The canonical Lean theorem/model boundary is:

- `lean/Runtime/Proofs/Capabilities.lean`
- `lean/Runtime/Proofs/AuthorityMetatheory.lean`
- `lean/Runtime/Proofs/Conservation/Authority.lean`
- `lean/Runtime/Proofs/Conservation/Evidence.lean`
- `lean/Runtime/Proofs/ReconfigurationObserver.lean`
- `lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean`

### Source-Derived Boundary Rows

The rows below are source-derived and checked against
`telltale_machine::protocol_critical_capability_boundary()` by
`rust/bridge/tests/docs_contract_tests.rs`.

| Surface | Class | Lifecycle | Rust boundary | Lean boundary | Rationale |
|---|---|---|---|---|---|
| `runtime_admission` | `admission` | `issued`, `rejected` | `rust/machine/src/runtime_contracts.rs` | `lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean` | Admits or rejects runtime/profile execution before protocol-critical execution begins. |
| `theorem_pack_capabilities` | `admission` | `issued`, `rejected` | `rust/machine/src/composition.rs` | `lean/Runtime/Proofs/TheoremPack/API.lean` | Carries proof-backed eligibility that higher-level runtime admission consumes. |
| `ownership_capability` | `ownership` | `issued`, `invalidated`, `expired`, `rejected` | `rust/machine/src/session/overview.rs` | `lean/Runtime/Proofs/Conservation/Authority.lean` | Proves which actor may currently mutate session-local protocol-critical state. |
| `readiness_witness` | `evidence` | `issued`, `consumed`, `rejected`, `invalidated`, `expired` | `rust/machine/src/session/overview.rs` | `lean/Runtime/Proofs/AuthorityMetatheory.lean` | Justifies a protocol-critical readiness decision under one live owner generation. |
| `authoritative_read` | `evidence` | `issued`, `consumed`, `rejected` | `rust/machine/src/semantic_objects.rs` | `lean/Runtime/Proofs/Conservation/Evidence.lean` | Carries evidence-bearing protocol input that may author canonical truth. |
| `materialization_proof` | `evidence` | `issued`, `consumed`, `rejected` | `rust/machine/src/semantic_objects.rs` | `lean/Runtime/Proofs/Conservation/Evidence.lean` | Witnesses proof-bearing success on the sanctioned materialization path. |
| `canonical_handle` | `evidence` | `issued`, `consumed`, `rejected`, `invalidated` | `rust/machine/src/semantic_objects.rs` | `lean/Runtime/Proofs/Conservation/Evidence.lean` | Provides the strong reference required on parity-critical follow-on paths. |
| `ownership_receipt` | `transition` | `issued`, `committed`, `rolled_back`, `rejected`, `invalidated`, `expired` | `rust/machine/src/session/overview.rs` | `lean/Runtime/Proofs/Conservation/Authority.lean` | Stages and commits explicit ownership transfer rather than ambient authority mutation. |
| `semantic_handoff` | `transition` | `committed`, `rolled_back`, `rejected`, `invalidated` | `rust/machine/src/semantic_objects.rs` | `lean/Runtime/Proofs/Conservation/Authority.lean` | Represents explicit protocol-visible authority transfer and old-owner revocation. |
| `reconfiguration_transition` | `transition` | `issued`, `committed`, `rolled_back`, `rejected` | `rust/machine/src/composition.rs` | `lean/Runtime/Proofs/ReconfigurationObserver.lean` | Captures protocol-critical cutover and membership/runtime transition artifacts. |

Runtime upgrade is intentionally not a separate ambient authority system. It is
a specialized transition-capability family inside the same reconfiguration
subsystem. The canonical Rust objects are:

- `RuntimeUpgradeRequest`
- `RuntimeUpgradeExecution`
- `RuntimeUpgradeArtifact`
- `RuntimeUpgradeCompatibility`

Those objects make staged, admitted, committed-cutover, rolled-back, and
failed transition phases replay-visible, along with the cutover contract for
ownership continuity, pending-effect treatment, and canonical publication
continuity.

## First-Class Finalization Subsystem

Canonical protocol truth is also modeled explicitly rather than inferred from
scattered helper methods. The runtime derives one stable finalization view from
the semantic-object bundle:

- `ProtocolMachineFinalization`
- `FinalizationPath`
- `FinalizationReadClass`
- `FinalizationStage`

This is the claim-critical boundary between provisional observation and
canonical protocol truth:

| Stage | Meaning |
|---|---|
| `observed` | only observational reads/effects exist; nothing canonical may be consumed |
| `authoritative` | typed authoritative evidence exists, but no proof-bearing materialization has succeeded yet |
| `materialized` | proof-bearing success exists, but canonical publication/handle pairing is not complete yet |
| `canonical` | proof-bearing publication plus canonical handle make the path consumable as protocol truth |
| `invalidated` | an explicit handoff or transition revoked the path before canonical reuse |
| `rejected` | proof-bearing publication or repair failed and the path stays non-canonical |

Observed reads may never become canonical truth directly. They must pass
through the explicit evidence and materialization path first.

## Language Shape

The current language surface uses a small set of explicit forms:

```tell
effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  authoritative let readiness = check Runtime.ready(session) in
    case readiness of
      | Ok(witness) =>
          Coordinator -> Worker : Commit(witness)
      | Err(TimedOut) =>
          Coordinator -> Worker : Cancel
```

Evidence binding uses ordinary `let`:

```tell
let receipt = transfer Session from Coordinator to Worker
handoff acceptInvite to Worker with receipt
```

Receipts and transfer-like bindings are linear and must be consumed exactly
once.

Capability-class mapping for the language surface:

| DSL form | Capability class | Lifecycle emphasis |
|---|---|---|
| `authoritative let x = check ...` | `evidence` | issued -> consumed/rejected |
| `observe let x = observe ...` | `evidence` | observed-only input, never canonical directly |
| `let receipt = transfer ...` | `transition` | issued -> committed/rolled_back/rejected/invalidated |
| `publish witness as Publication` | `evidence` | authoritative -> published |
| `materialize proof from Publication` | `evidence` | materialized/rejected |
| `handoff op to Role with receipt` | `transition` | committed/rolled_back/invalidated |

The runtime follows the same linear rule for timeout and cancellation
evidence. Timeout expiry is modeled as a state transition on the exact stored
`TimeoutWitness`, not as an inferred event derived later from ambient clock
state.

## Runtime Meaning

Language-level authority checks are expected to lower into the existing runtime
authority surfaces:

- `check Effect.op(...)` lowers to the typed protocol-machine effect boundary
- successful protocol-critical checks produce explicit evidence/witness objects
- invalid or missing evidence fails closed
- timeout and cancellation become explicit observable/runtime-audit outcomes
- transfer/delegation emits explicit receipts and audit records
- stale capability, receipt, and witness reuse are rejected and retained in the
  lifecycle audit rather than being silently ignored

This keeps the user-facing language aligned with:

- `EffectHandler` typed outcomes
- `OwnedSession` and runtime ownership capability checks
- `ReadinessWitness`, `CancellationWitness`, and `TimeoutWitness`
- `semantic_audit_log` and replay-visible event ordering

## No Fallback Masking

Protocol-critical authority must not degrade into ambient host heuristics.

Fail-closed rules:

- no implicit wildcard/default masking for `Result` and `Maybe`
- no ad hoc “missing data means false” authority checks
- no silent reuse of stale capabilities or receipts
- no hidden host-only branch decisions outside typed effect queries

## Relation to the Effect Bridge

This design does not create a second host/runtime bridge.

The authoritative path is:

1. declare a nominal `effect`
2. name it in `uses`
3. invoke it with `check Effect.op(...)`
4. lower it into the existing typed protocol-machine `invoke` boundary
5. preserve its outcome in effect/audit/replay surfaces

That matches the project’s existing typed effect-obligation architecture and
observational correctness story.

## Related Docs

- [Protocol-Critical Authority Scope](33_protocol_authority_scope.md)
- [Authority Language Surface](34_authority_language_surface.md)
- [Effect Handlers and Session Types](11_effect_session_bridge.md)
- [Protocol Machine Architecture](12_protocol_machine_architecture.md)
