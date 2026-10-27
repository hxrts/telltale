# Authority Language Surface

This page records the current authority/failure-oriented DSL surface added on
top of the choreography parser.

It is the current reference page for language-level authority checks, typed
failure branching, and nominal effect interfaces.
It is intentionally narrower than a full generalized effect language.
General host application authorization is out of scope.

## Current Surface

Top-level declarations:

- `type Name = | Ctor | Ctor(Payload)`
- `type alias Name =`
- `  {`
- `    field : Type`
- `  }`
- `effect Runtime`
- `  authoritative ready : Session -> Result CommitError ReadyWitness`
- `protocol Flow uses Runtime =`
- `  roles Coordinator, Worker`
- `  authoritative let witness = check Runtime.ready(session)`

Protocol-local forms:

- `authoritative let binding = check Runtime.op(args)`
- `observe let binding = observe Effect.op(args)`
- `let receipt = transfer Session from A to B`
- `let binding = ... in ...`
- `case expr of | Ok(value) => ... | Err(reason) => ...`
- `timeout 5s Coordinator at ... on timeout => ... on cancel => ...`
- `choice Coordinator at | Commit when check Runtime.ready(session) yields witness => ...`

## Review Sketches

These are the short canonical examples for the current reviewed language
additions.

### Nominal Effects and `uses`

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
  observe watchPresence : Session -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

protocol Flow uses Runtime =
  roles Coordinator, Worker
  authoritative let witness = check Runtime.ready(session)
  Coordinator -> Worker : Commit
```

This is the smallest effect declaration plus dependency declaration that the language accepts.

### `Result` with `case/of`

```tell
authoritative let readiness = check Runtime.ready(session) in
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Worker : Cancel(reason)
```

This is the canonical typed branching form for authority checks.

### `Maybe`

```tell
case maybeReceipt of
  | Just(receipt) =>
      Coordinator -> Worker : UseReceipt(receipt)
  | Nothing =>
      Coordinator -> Worker : MissingReceipt
```

This keeps absence explicit instead of falling back to implicit defaults.

### Custom Union and Alias

```tell
type CommitError =
  | TimedOut
  | Cancelled

type alias ReadyWitness =
  { epoch : Int
  }
```

Custom unions and aliases name failure and evidence values directly in the DSL.

### Evidence Binding with `let`

```tell
let receipt = transfer Session from Coordinator to Worker
handoff acceptInvite to Worker with receipt
```

Ordinary `let` syntax is the only binding form used for receipts and other authority artifacts.

### Timeout and Cancellation

```tell
timeout 5s Coordinator at
  Worker -> Coordinator : Ready
on timeout =>
  Coordinator -> Worker : Cancel
on cancel =>
  Coordinator -> Worker : Cancelled
```

Timeout and cancellation are explicit protocol branches, not host-only control flow.

### Evidence Guard

```tell
choice Coordinator at
  | Commit when check Runtime.ready(session) yields witness =>
      Coordinator -> Worker : Commit(witness)
  | Abort =>
      Coordinator -> Worker : Abort
```

Evidence guards bind the witness directly at the branch point that authorizes the action.

### Linear Single-Use Binding

```tell
let receipt = transfer Session from Coordinator to Worker
handoff acceptInvite to Worker with receipt
```

Transfers produce first-class transition receipts. The compiler requires each
receipt to be consumed exactly once, and the runtime/Lean model treats the
receipt as a transition artifact rather than an untyped helper value.

### Local Helper Expression

```tell
authoritative let readiness = check Runtime.ready(session) in
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Worker : Cancel(reason)
```

`let ... in ...` keeps small authority decisions local instead of pushing them into host callbacks.

### No Implicit Default

```tell
case readiness of
  | Ok(witness) =>
      Coordinator -> Worker : Commit(witness)
  | Err(reason) =>
      Coordinator -> Worker : Cancel(reason)
```

Protocol-critical matches must be exhaustive. Implicit catch-all masking is rejected.

### Typed External Query

```tell
authoritative let readiness = check Runtime.ready(session)
```

Typed external queries always enter the protocol through explicit `check` expressions.

## Result and Maybe

The DSL currently treats `Result` and `Maybe` as built-in naming conventions rather than a separate kind system.

- `Result` constructors: `Ok`, `Err`
- `Maybe` constructors: `Just`, `Nothing`

Current compiler rules:

- `case/of` over `Result` must include both `Ok` and `Err`
- `case/of` over `Maybe` must include both `Just` and `Nothing`
- implicit catch-all masking is not supported

## Let and Linearity

`let` is the normal binding form for transition receipts and non-authoritative
query results. `authoritative let` and `observe let` are the explicit binding
forms for protocol-critical authoritative and observational reads.

## DSL Capability Mapping

| DSL form | Capability class | Lifecycle emphasis |
|---|---|---|
| `authoritative let x = check ...` | `evidence` | issued -> consumed/rejected |
| `observe let x = observe ...` | `evidence` | observed-only input, never canonical directly |
| `let receipt = transfer ...` | `transition` | issued -> committed/rolled_back/rejected/invalidated |
| `publish witness as Publication` | `evidence` | authoritative -> published |
| `materialize proof from Publication` | `evidence` | materialized/rejected |
| `handoff op to Role with receipt` | `transition` | committed/rolled_back/invalidated |
| `case/of` over evidence | control-flow over evidence | must preserve linear assets and remain exhaustive |
| `timeout ... on timeout ... on cancel ...` | evidence/transition-adjacent control-flow | explicit timeout/cancellation outcomes with replay-visible lifecycle |

Current linear classification:

- `transfer ...` bindings are linear first-class transition receipts
- `authoritative let check ...` bindings are first-class evidence reads
- `observe let observe ...` bindings are first-class observational reads and may not be used where authoritative evidence is required

Current linear rules:

- linear bindings must be consumed exactly once
- duplicate use is rejected
- implicit discard is rejected

Current cross-construct rule:

- the implementation counts use across subsequent statements and across explicit branch bodies
- the parser and protocol-machine surface support `choice`, `case`, `timeout`, `loop`, `par`, `call`, and recursion with explicit linear preservation checks
- rejected programs fail closed when linear assets diverge across branches, timeout/cancel paths, loop iterations, recursive unfoldings, or parallel arms
- observational bindings remain separated from authoritative evidence under these control-flow forms

## Explicit Scope Boundary

The DSL currently gives first-class meaning to:

- authoritative reads
- observed reads
- transfer receipts
- publication events
- materialization proofs
- canonical handles
- semantic handoffs

The DSL does not currently give first-class syntax to runtime upgrades or
reconfiguration statements. Those remain runtime/model surfaces, not
choreography statements, until they have a real shared Rust and Lean meaning.

## Authority Metatheory Boundary

The authority theorem story is intentionally narrower than the executable DSL surface.

Current proof-plane split:

- ordinary communication, recursion, and other coordination-only structure remain part of the session-typed theorem story
- the supported authority-bearing theorem slice lives in the protocol-machine semantic-object layer, not in a generalized session-type extension

Current supported authority theorem slice:

- evidence-bearing reads introduced by `authoritative let`, `observe let`, and evidence guards
- canonical publication/materialization paths introduced by `publish ... as ...` and `materialize ... from ...`
- explicit progress contracts for parity-critical operations protecting those paths

Current runtime-semantic-only authority surfaces:

- `case/of`
- `timeout ... on timeout ... on cancel ...`
- `par`
- transfer-produced receipts and their consumption
- `handoff`
- `dependent work`
- explicit commitment lifecycle forms such as `begin`, `await`, `resolve`, and `invalidate`

These forms name protocol-machine semantic obligations. Concrete executable
lowering is entry-point-specific, as described in the
[source-derived support matrix](#source-derived-support-matrix) and
[prepared enclosing-operation slice](#prepared-enclosing-operation-executable-slice).
Parser acceptance, generated metadata and communication projection do not
establish that an authority obligation is executed. Protocol-machine conservation
theorems retain their declared premises and do not supply a missing source-to-machine
lowering. These forms remain outside the smallest authority-specific theorem slice.

## Effect Declarations and Uses

`effect` declarations are nominal interfaces.

Current validation rules:

- effect interface names must be unique
- operation names must be unique within an effect
- effect operations may be classified as `authoritative`, `command`, or `observe`
- `protocol ... uses ...` may reference only declared effects
- `check Effect.op(...)` and evidence guards may reference only:
  - effects named in `uses`
  - operations declared on those effects
- `check Effect.op(...)` may not target `observe` operations
- `observe Effect.op(...)` may reference only observational operations

This is the current clean-break contract.
There is no fallback to implicit host knowledge.
Lowering is expected to preserve this split into the runtime semantic-object
family as `AuthoritativeRead` versus `ObservedRead`. Observational reads are not
allowed to become proof-bearing success or canonical publication by repair.

## Typed Host Effect Invocation

`check Effect.op(...)` is the language-level way to invoke typed host effects.

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

protocol Flow uses Runtime =
  roles Coordinator, Worker
  authoritative let readiness = check Runtime.ready(session)
  Coordinator -> Worker : Commit
```

Current contract:

- the protocol must declare the effect in `uses`
- the operation must exist on the named nominal interface
- `check` is for authoritative or command operations
- `observe` is for observational operations
- lowering stays centered on the existing protocol-machine `invoke` boundary
- effect observations keep the nominal interface and operation identity for
  replay/audit surfaces

## Projection and Theory Boundary

Current projection behavior is intentionally explicit:

- `let` is treated as local-only and projects through to its continuation
- `case/of` is currently rejected by projection
- `timeout ... on timeout ... on cancel ...` is currently rejected by projection
- accepted authority-aware `choice`, `call`, `loop`, `par`, and recursion forms remain protocol-machine executable, and the subset without other blockers remains session-projectable

This preserves MPST clarity while the explicit projection rules are still being designed.

Theory conversion is narrower than projection today:

- `let`, `case/of`, and `timeout` must be lowered further before conversion to theory-facing global types
- `choice`, `call`, counted loops, and recursion convert today when the surrounding protocol stays in the common subset
- `par` is session-projectable and protocol-machine executable, but it still has no theory-facing global-type conversion and fails closed with an explicit `Parallel` blocker

### Source-Derived Support Matrix

The following rows are source-derived from the checked authority fixture corpus
and validated by `rust/bridge/tests/docs_contract_tests.rs`.

| Fixture surface | Protocol-machine executable | Session-projectable | Theory-convertible | Authority theorem tier | Explicit blocker |
|---|---|---|---|---|---|
| `call` with plain communication | yes | yes | yes | `session_typed_coordination` | `none` |
| `choice` with observational binding | yes | yes | no | `evidence_publication_semantic_objects` | `AuthorityBinding` |
| counted `loop` with authoritative binding | yes | yes | no | `evidence_publication_semantic_objects` | `AuthorityBinding` |
| recursion with authoritative binding | yes | yes | no | `evidence_publication_semantic_objects` | `AuthorityBinding` |
| `par` with observational binding | yes | yes | no | `runtime_semantic_only` | `AuthorityBinding` |
| `case/of` with authoritative binding | yes | yes | no | `runtime_semantic_only` | `AuthorityBinding` |
| `timeout` with observational binding | yes | yes | no | `runtime_semantic_only` | `AuthorityBinding` |

Explanatory prose below remains hand-written. The table above is the checked
contract surface for the reviewed authority/control-flow subset.

## Lowering Boundary

The current lowering split is:

- parser/AST surface in `rust/language`
- protocol-machine effect execution boundary in `rust/machine`
- typed handler boundary centered on protocol-machine `invoke`

Current intent:

- `effect` declarations become the source for generated Rust host interfaces
- `check Effect.op(...)` remains a DSL-level reference to a typed external query
- execution must still cross the same typed handler-obligation boundary rather than inventing a second host channel
- the Lean bridge statement for nominal effect declarations stays centered on the existing protocol-machine `invoke` obligation rather than a separate effect-language proof surface

## Observable Trace Model

Language-level effect usage is expected to remain observable through the same runtime/effect tracing surfaces used by protocol-machine replay and effect-bisimulation work.

Current design rule:

- language-level authority checks and evidence-sensitive decisions must map to explicit effect operations and explicit protocol-machine-visible events
- missing or ambiguous authoritative input must become typed failure, never silent fallback success
- canonical replay artifacts must preserve these decisions as structured semantic audit records rather than opaque host-only log text

## Source-Derived Boundary Rows

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

## Runtime Meaning

Language-level authority checks lower into the existing runtime authority surfaces:

- `check Effect.op(...)` lowers to the typed protocol-machine effect boundary
- successful protocol-critical checks produce explicit evidence/witness objects
- invalid or missing evidence fails closed
- timeout and cancellation become explicit observable/runtime-audit outcomes
- transfer/delegation emits explicit receipts and audit records
- stale capability, receipt, and witness reuse are rejected and retained in the lifecycle audit

This keeps the language aligned with `EffectHandler` typed outcomes,
`OwnedSession` ownership capability checks, the witness family
(`ReadinessWitness`, `CancellationWitness`, `TimeoutWitness`), and
`semantic_audit_log` replay-visible event ordering.

## Fail-Closed Rules

Protocol-critical authority must not degrade into ambient host heuristics.

- no implicit wildcard/default masking for `Result` and `Maybe`
- no ad hoc "missing data means false" authority checks
- no silent reuse of stale capabilities or receipts
- no hidden host-only branch decisions outside typed effect queries

This design does not create a second host/runtime bridge. The authoritative
path is: declare a nominal `effect`, name it in `uses`, invoke it with
`check Effect.op(...)`, lower it into the existing typed protocol-machine
`invoke` boundary, and preserve its outcome in effect/audit/replay surfaces.

## Communication Artifact Refusal

Communication projection remains a type-level abstraction. Plain, non-linear
identifier and constructor bindings have no invocation node and may project
through to communication. Their identifier-only constructor payload grammar
cannot contain an effect call. This does not evaluate a local value or grant
authority. Calls are not presumed pure: a plain call can contain an effect-call
argument and has no checked purity contract.

Theory conversion and integration executable-artifact requests now reject
explicit authoritative/observational modes, check/observe/transfer expressions,
linear aliases, and unclassified calls instead of silently erasing them. The
local artifact request checks the strongest original AST before consuming its
already projected communication view. Scope shadowing cannot hide a preceding
authority binding from that whole-AST check. The generated-effects entry point
also refuses these bindings, including those nested in control flow.

The table's protocol-machine-executable classification describes the existing
AST semantic surface, not proof that these bindings lower through a
communication-only CodeImage. Positive effect-preserving authority lowering is
still unavailable on that path. The supported Lean semantic-object theorems do
not supply the missing compiler correspondence.

## Explicit Local Binding Placement Prerequisite

A binding may spell its execution placement as `let value at Coordinator = expr`,
with the same `at Role` clause after the binding name for authoritative and
observational forms and for `let ... in`. The role reference must name a declared
role. Indexed references retain the existing role-reference syntax. Placement is
preserved in the AST, cloning and continuation composition. An omitted clause
remains unplaced. It does not choose the first role or the next sender.

This is a source representation prerequisite, not executable authority lowering.
An explicitly placed binding requires effect-preserving lowering even when its
expression is plain. Communication theory conversion, direct local projection
and generated-effects artifact construction refuse it. Generic communication
programs and `runtime.step` keep their existing semantics. Placement does not
issue a session capability, resolve a role family to an original endpoint, name a
nominal operation at runtime, or authorize a continuation.

A future admitted nominal construct must bind this source placement to the
actual coroutine's session endpoint and generation, declared operation and
argument/result types, then retain one issued continuation through its accepted
outcome. The existing communication-only LocalTypeR and total Lean
EffectRuntime.exec contract cannot express that transaction. They are unchanged
by the placement prerequisite. Positive nominal execution and correspondence
proof remain required before authority bindings can be admitted.

## First Nominal Command Execution Contract

The selected-operation compiler admits an explicitly placed, declared Command
with Unit input and `Result String Bool` output, followed immediately by an
exhaustive Ok/Err case whose branches each send a distinct terminal label to the
same peer. This is a command result, not authoritative evidence. Application
Err, host Failure and a pending host outcome are distinct states.

The enclosing operation retains its source-selected NoAgreement profile, owner
role and named progress window. That window requires an explicit nonzero tick
budget. Missing configuration and unsupported agreement or escalation semantics
refuse admission. Model ticks do not replace a host's physical deadline.

An executable nominal call requires an actually issued owned-session handle,
the original session generation and role endpoint, its exact admitted nominal
declaration and a live canonical effect/operation occurrence. The coroutine
retains the original nonserialized continuation and any returned typed result
through commit gates. A pending response resumes that same occurrence and
progress owner, without resetting the window. Admission and result commit require
`current_tick <= original_issued_tick + selected_budget`, with checked overflow
refused before issuance. Multi-window progress escalation cannot extend this
original endpoint even while its canonical effect still reports Blocked. A changed semantic handler
identity, stale generation, invalidated occurrence or restored checkpoint without
that original handle cannot invoke the callback or consume the continuation.
Handler identity is a semantic contract identifier. Equality does not prove
physical provider identity or host-future teardown.

The compiler does not admit arbitrary expressions, authority-producing checks,
readiness, publication, materialization, transfer or handoff by this command
contract. Ordinary communication conversion continues to refuse explicitly
placed authority expressions. Both backend producers and an executable nominal
Lean transition are prepared source. Their fixtures and correspondence facts
must be checked before any execution or parity claim. This is not full lowering
of the remaining authority/evidence forms.

## Executable Source Operation Continuations

`begin`, `await`, `resolve`, and `invalidate` describe one original operation
continuation on its actual executing coroutine. `begin` does not spawn another
runtime, thread or task, and does not invoke an unspecified host callback. It
selects the declared operation, explicit owner role, agreement profile and original
logical progress window. Its live continuation retains the actual issued session
owner. Serialized declaration fields cannot reconstruct it.

A selected operation body retains the validated parent role scope and its original
declaration. Its explicit owner must belong to that scope, and every referenced
role must remain declared. An empty local operation need not invent communication
for every parent role. Ordinary complete choreographies still require all declared
roles to participate.

The selected source compiler binds its declared nominal callbacks as explicit
children in the existing operation/effect/progress records. Communication and
control instructions remain on the actual coroutine continuation. Incidental
observational exchanges are not invented as additional declared child slots. A child is identified
by its original canonical occurrence, not by a later effect name, last trace row,
or a newly constructed equal-valued request. `await` observes this admitted set.
A missing, ambiguous or pruned admitted child refuses. It never counts as terminal
success. Live children keep the same operation and PC pending. An operation with
no admitted children may pass this child-quiescence condition, but this neither
executes omitted work nor proves any required dependent work was performed.
Original unsuccessful child outcomes remain typed failures on the continuation.

`resolve` retains its proposed typed result before the final original-owner,
window and child-completion gates. A refusal cannot substitute another result,
reset the original window, or discard the original child failure. Duplicate
resolution is rejected. An application `Success` status does not satisfy a
selected proof requirement or create a publication, materialization proof or
canonical handle. Those require their own genuine issuing/consuming transitions.

`invalidate` revokes the original semantic continuation and its still-live child
occurrences. Late results cannot commit through that continuation. Invalidation
is not host-future cancellation or physical resource settlement. Those resources
and their actual completion obligations remain under the original host owner.

An executable `handoff` must transport this actual original continuation to an
eligible target, including its child identities, selected original window,
retained result and failure. Changing a session's host owner, moving an endpoint,
or emitting a semantic record alone does not execute `handoff`. Static role names
may identify a destination but cannot replace the original issued owner gate.

### Prepared authoritative readiness command slice

`compile_command_operation` additionally lowers an explicitly placed
`authoritative let result at A = check Host.ready()` when the admitted nominal
operation is `authoritative`, `class : authoritative`, `progress : may_block`,
`region : session`, Unit input and `Result String ReadinessWitness` output.
The existing explicit NoAgreement profile and selected named simulation-tick
budget remain required. This bounded slice branches to terminal unit-message
continuations. It does not implement witness transport, publication,
materialization, or a general authority expression interpreter.

The callback returns a typed `NominalCommandValue::Readiness`, distinct from
`Bool`. The predicate is the exact source interface and operation joined by
`.`. Before executing the success continuation, both backends consume the
original registered witness using the retained issued session owner, after
output and WAL admission and destination validation. The registry checks exact
issuance, session, owner, generation, full-session scope and single use.
A Boolean, copied serialized field set, stale owner, wrong predicate, or foreign
session cannot replace that check. Gate refusal keeps the original callback
result resident and leaves the witness unconsumed. Transfer/rollback remains
the canonical session transaction. This lowering adds no transfer registry.

These implementation and fixture declarations are source-only until their
actual Rust harness discovery/execution and Lean elaboration succeed.


### Prepared enclosing-operation executable slice

`compile_operation_image` selects the checked original operation body. The
current enclosing slice supports an explicit Begin and either an empty body or
one placed nominal Bool/readiness command with distinct terminal unit-message
branches. Each child branch retains its explicit Await/Resolve tail. The static
manifest binds each required child to the complete installed typed call and PC.
Role-image assembly and slicing relocate both, while the loader verifies them
against the actual installed opcode. Skipping required work cannot produce
empty-inventory success. A Halt cannot abandon an unresolved original parent.

Begin, child invocation, result commit and explicit resolution retain one
original issued owner and logical window. All nominal calls, including Bool
commands, require that owner. Ordinary loading, checkpoint observations and a
new registry generation cannot refresh a stale coroutine. Actual callback
failure and independent output refusal retain the first typed execution fault
and original returned outcome while revoking protocol commit. No revocation or
application cancellation acknowledges physical host cleanup.

In this same-coroutine slice, a Blocked nominal child retains its original call
PC until that child returns. This is not evidence of a separately pending Await.
The existing scheduler has original-child wake semantics, but the genuine
cross-continuation dependent-work producer, executable handoff, general
cancellation/timeout escalation, stronger agreement, publication and
materialization remain required implementation work. Unsupported forms refuse.
That refusal does not complete those requirements. The prepared source and
model examples require actual compilation and execution before acceptance.
