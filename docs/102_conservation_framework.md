# Conservation Framework

Telltale is a conservation system over protocol semantics. All semantically meaningful behavior is expressed in terms of conserved quantities. All other behavior is erased or reduced to those quantities.

This framework defines the six properties that Telltale conserves, the principles that constrain the programming model, and the semantic objects through which conservation is realized at runtime.

## Conserved Properties

Telltale enforces conservation over six properties. Each property has a conservation law stating what the system guarantees across all protocol evolution.

### Evidence

Evidence is the integrity of what has been established. Witnesses, proofs, and attestations are the concrete forms of evidence. Evidence backs protocol claims and gates protocol progression.

Conservation law: the evidential backing of any protocol claim cannot increase except through explicit witness production. It cannot decrease except through explicit invalidation. Evidence cannot be fabricated from weaker evidence.

### Authority

Authority is the exclusivity of who may act. Ownership is the concrete form of authority. Authority determines which actor may produce evidence, commit state, or transfer control.

Conservation law: exactly one semantic owner holds authority over a given resource at any time. Authority cannot be duplicated. Transfer is explicit and invalidates prior authority.

### Identity

Identity is the definiteness of object references. Identity distinguishes one unit of semantic work from another across retries, effects, and handoffs. Definite references are what make ownership meaningful and commitments trackable.

Conservation law: identity is stable across all transformations of an operation. It cannot be reconstructed from ambient context. It is assigned once and carried, never re-derived.

### Commitment

Commitment is the account of outstanding obligations. Outstanding effects are the concrete form of commitment. A commitment is a promise that the system will produce a resolution for a given operation.

Conservation law: every commitment must resolve to exactly one of success, failure, timeout, cancellation, or invalidation. Commitments cannot silently disappear. The total number of unresolved commitments is always known.

### Structure

Structure is the essential shape of the protocol. Multiparty session types are the concrete form of structure. Structure defines the topology of interaction, the composition of roles, and the coherence between local and global behavior.

Conservation law: the compositional structure of the protocol is defined entirely by its type. Local behavior must remain a valid projection of the global protocol. No runtime behavior can alter the protocol shape. See [Theory](103_theory.md) for the session type foundations.

### Premise

Premise is the explicitness of environmental assumptions. Failure models, fairness assumptions, and progress expectations are the concrete forms of premise. Premise determines what the protocol can rely on from its environment.

Conservation law: the system operating assumptions are explicit and fixed for a given execution context. Premise violation triggers explicit escalation rather than silent degradation. Escalation classes include blocked, degraded, and failed.

## Property Relations

The six properties are mutually constitutive. They do not layer into a dependency hierarchy. A coherent protocol state is a simultaneous assignment of all six. A violation in any one can manifest as a failure in any other.

## Erasure Principle

Any behavior that is not part of the conserved quantities is not part of the programming model. Scheduling, task execution, callback timing, retry loops, thread interleaving, and background task structure are implementation details. They must reduce to the conserved system.

Developers reason about evidence, authority, identity, commitment, structure, and premise. They extend the system through typed effect interfaces that enforce the conservation laws at the boundary. Domain logic plugs into contracts, not into concurrency.

## Reduction Principle

All runtime behavior must reduce to the conservation framework.

| Runtime phenomenon | Reduced form |
|---|---|
| async execution | commitment lifecycle |
| race condition | authority violation |
| retry logic | identity + commitment |
| stale callback | invalidated commitment |
| state bug | invalid evidence or identity |
| timeout | premise escalation |
| background task | detached or structured commitment |

This table maps common runtime phenomena to their conservation-framework equivalents. If a runtime behavior cannot be expressed in these terms, it does not belong in the model.

## Eliminated Bug Classes

The system eliminates these classes of bugs by construction. Each maps to a violation of specific conserved properties.

| Bug class | Description | Violated property | Eliminated by |
|---|---|---|---|
| Hidden concurrency | Work outside structured control | commitment | Explicit commitments, no ambient async |
| Authority ambiguity | Multiple actors advancing same state | authority | Single semantic owner, explicit handoff |
| Weakening of evidence | Fallback from strong to weak backing | evidence | Monotonic witness strengthening, canonical handles |
| Silent failure | Work disappearing or failing invisibly | commitment | Commitment conservation, typed outcomes |
| Late result races | Stale results applied after handoff | authority, identity | `OutstandingEffect` tracking, identity + owner validation |
| Observational state becoming evidence | Cache or UI state treated as authoritative | evidence | Separation of `AuthoritativeRead` and `ObservedRead` |
| Best-effort work defining success | Optional work affecting terminal state | commitment | Work classification (required vs best-effort) |
| Unbounded waiting | Operations that never resolve | commitment, premise | `ProgressContract`, required escalation |
| Hidden reentrancy | Same domain re-entered unexpectedly | structure | Explicit reentrancy rules |
| Multiple evidence sources | Multiple publication paths | evidence, authority | Canonical publication path, proof-bound publication |

## Semantic Core Objects

The conservation framework is realized through a closed set of semantic objects. All protocol-visible language features must lower to these objects or to pure structural session terms. If a feature cannot be reduced to this semantic core, it is not admitted as part of the model.

| Object | Role | Capability class |
|---|---|---|
| `Region` | Locality and framing domain for structured coordination | structural context |
| `OperationInstance` | Stable identity for one semantic operation across retries, handoff, and replay | identity carrier |
| `OutstandingEffect` | One unresolved capability invocation with explicit lifecycle state | commitment/evidence support |
| `SemanticHandoff` | Explicit transfer of responsibility and authority between actors | `transition` |
| `AuthoritativeRead` | Proof-carrying read surface that may support semantic commitment | `evidence` |
| `ObservedRead` | Non-authoritative read surface for rendering, diagnostics, or advisory logic | `evidence` |
| `MaterializationProof` | Typed proof that a canonical artifact has been materially established | `evidence` |
| `CanonicalHandle` | Non-forgeable reference obtained from authoritative materialization | `evidence` |
| `ProgressContract` | Explicit liveness and budget contract governing waits and escalation | premise/commitment support |

These objects are first-class in the Lean formalization, represented canonically in Rust, and referenced in the protocol machine semantic audit surface. See [Protocol Machine Architecture](401_protocol_machine_architecture.md) for the runtime accessors and [Lean Verification](801_lean_verification.md) for the proof surfaces.

## Implementation Techniques

Each implementation technique serves one or more conserved properties.

| Technique | Description | Properties conserved |
|---|---|---|
| Protocol machine | Single component that commits state | authority, structure |
| Operation instances | Explicit identity for all semantic work | identity |
| Outstanding effects | All deferred work tracked to resolution | commitment |
| Semantic handoff | Explicit authority transfer between actors | authority, identity |
| Witness system | All evidence is proof-bearing | evidence |
| Capability algebra | Authority is explicit and constrained | authority |
| Effect system | Boundary interactions are typed and classified | commitment, evidence |
| Progress contracts | Liveness is explicit and enforced | commitment, premise |
| Structured session decomposition | All concurrency follows session structure | structure, commitment |
| Enforcement | Type-level where possible, runtime fail-closed otherwise | all |

## Debugging Model

Every failure is a conservation failure. Every failure must be explainable as a violation of one or more conserved properties.

Instead of "the system hung," a developer sees: which operation, which owner, which commitment, which required witness, which premise, and which escalation state. Every failure answers whether the protocol was correct, whether authority was modeled correctly, whether the premise was correct, whether the effect classification was correct, and whether the progress contract was correct.

## Related Docs

- [Architecture](104_architecture.md)
- [Theory](103_theory.md)
- [Effect Handlers and Session Types](303_effect_session_bridge.md)
- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Authority Language Surface](703_authority_language_surface.md)
