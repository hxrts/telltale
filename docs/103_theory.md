# Theory

This document explains the theory that Telltale builds on.
It is organized by audience relevance.
Developer-facing protocol concepts come first.
Proof-oriented topics come last.

## Foundations

Session types describe communication protocols as types.
They let the type system check message order, branch structure, and termination behavior.
Telltale uses them as the structure layer of its protocol model.

### Why Session Types

Distributed programs fail when participants disagree about message order or branch choice.
Ordinary data types do not describe those communication obligations.
Session types add that missing protocol structure.

With session types, communication mistakes become type errors rather than runtime surprises.
This is the main reason they matter in practice.
They let developers state protocol shape directly and check it mechanically.

### Binary Session Types

Binary session types describe one conversation between two parties.
The core actions are send, receive, choice, and termination.

| Syntax | Meaning |
|---|---|
| `!T.S` | send a value of type `T`, then continue as `S` |
| `?T.S` | receive a value of type `T`, then continue as `S` |
| `⊕{...}` | choose one labeled branch |
| `&{...}` | accept one labeled branch |
| `end` | terminate the session |

Binary types also rely on duality.
If one side sends, the other side must receive.
If one side chooses, the other side must branch on that choice.

```text
Client: !Request.?Response.end
Server: ?Request.!Response.end
```

This pair is dual.
The client sends then receives.
The server receives then sends.

### Multiparty Session Types

Multiparty session types extend the same idea to three or more roles.
They separate the protocol into a global view and one local view per participant.
This is the core abstraction behind Telltale choreographies.

Global types describe the whole protocol from a neutral perspective.
Local types describe only what one role must send and receive.
Projection computes those local types from the global type.

```text
Global:
  Alice -> Bob: Request.
  Bob -> Carol: Forward.
  Carol -> Bob: Result.
  Bob -> Alice: Response.
  end
```

This global type describes the whole conversation.
Projection gives Alice a two-step local view, Bob a four-step local view, and Carol a two-step local view.

### Projection and Merging

Projection extracts one role-local type from the global type.
When a message does not involve the target role, projection skips it.
When a message does involve the target role, projection turns it into a local send or receive action.

Branching requires one extra operation called merge.
If a participant is not the branch chooser, its projected local view must combine the possible continuations.
Merge succeeds only when those continuations remain compatible from that participant's viewpoint.

### Protocol Constraints

Not every syntactically valid protocol is meaningful.
Telltale relies on a set of constraints that a protocol must satisfy before projection and execution are well behaved.
These are often called well-formedness conditions in the literature.

For global protocols, the main rules are:

- recursion variables must be bound
- communication branches must be non-empty
- a role must not send to itself
- recursion must pass through communication

For local protocols, the main rules are:

- the type must be closed
- recursion must unfold to observable communication or termination

These constraints are developer-facing.
They are the rules a protocol must satisfy in order to project cleanly and support the later guarantees.

### Recursion

Session types support recursive protocols through fixed points.
This is how a protocol expresses repetition or long-running interaction.

```text
μX. Alice -> Bob: Ping. Bob -> Alice: Pong. X
```

This protocol repeats the same request-response cycle forever.
Recursion is valid only when unfolding eventually reaches observable communication.

### Subtyping

Subtyping determines when one protocol can replace another.
This matters when a component offers a more specific behavior than the caller requires.

In synchronous settings, subtyping follows the usual session-typing variance rules.
In asynchronous settings, buffering allows some outputs to move earlier relative to inputs.
Telltale implements asynchronous subtyping using the Bravetti et al. POPL 2021 algorithm.

## Protocol Guarantees

This section describes the guarantees developers usually care about once a protocol satisfies the foundational constraints.
These guarantees are still premise-scoped.
They depend on explicit assumptions about execution and delivery.

### Coherence

Coherence is the central MPST invariant.
It states that the collective local state of the protocol still matches the global protocol state.
Without coherence, projection would not give a trustworthy local view.

In Telltale, coherence is tracked per communication edge.
Each edge relates the sender state, the receiver state, the relevant buffer contents, and the remaining global structure.
This is the invariant that lets local endpoint behavior stay aligned with the choreography.

### Preservation

Preservation states that a well-typed and coherent protocol state remains well-typed and coherent after a valid step.
A correct protocol execution does not silently fall out of the typing discipline.
This is the usual subject-reduction property.

Preservation is mainly a meta-level guarantee.
Developers benefit from it because protocol execution stays inside the checked state space once it starts there.

### Progress

Progress states that a well-typed protocol can continue unless it has already terminated.
A participant does not get stuck waiting for behavior the protocol itself forbids.

This guarantee is premise-scoped.
Telltale states those premises explicitly.
They include well-typedness, reachability of communication, and fair scheduling.

### Deadlock Freedom

Deadlock freedom is the developer-facing consequence of preservation plus progress under the declared premises.
A well-typed protocol cannot reach a state where all participants are permanently blocked by protocol structure alone.

This guarantee does not ignore the environment.
If the delivery model or scheduler violates the stated premises, the theorem does not apply.
That separation is part of Telltale's premise discipline.

### Harmony

Harmony is a compilation-correctness property rather than a direct developer-facing liveness property.
It states that global protocol evolution and projected local evolution stay in correspondence.
This is what makes endpoint projection trustworthy.

```text
project(step(G)) = localStep(project(G))
```

This equation says that stepping the choreography and then projecting gives the same result as projecting first and stepping locally.
Developers benefit indirectly because generated endpoint behavior stays aligned with the choreography they wrote.

## Operational Extensions

This section covers theory that matters once the protocol interacts with realistic runtime concerns.
These topics are still user-relevant, but they are more specialized than the core session-typing model.

### Delegation and Reconfiguration

Delegation transfers a session endpoint from one participant to another.
This allows the active participant set to change during execution.
It is the main extension beyond fixed-role MPST.

Delegation is safe only when the transferred endpoint state matches what the receiver can legally assume.
Telltale captures those conditions with `DelegationWF`.
The important developer-facing point is that endpoint transfer is governed by explicit protocol-side conditions, not by ambient host authority.

### Delivery Models

Asynchronous session reasoning depends on the delivery model.
Different delivery models allow different message orderings and therefore support different theorems.

Telltale parameterizes theorems over `DeliveryModel`.
Important examples are FIFO, causal, and lossy delivery.
This keeps the theorem shape stable while making delivery assumptions explicit.

### Host-Runtime Ownership Contract

The Rust runtime adds an ownership contract around delegation, reconfiguration, and host-visible mutation.
This layer uses concepts such as current owner capability, ownership generation, transfer receipts, rollback, and stale-owner rejection.
It is an implementation hardening layer.

This runtime contract is aligned with theory-side predicates such as `DelegationWF`.
It should not be read as a separate theorem family.
It is the host/runtime realization of the protocol boundaries that the theory already identifies.

## Verification Topics

This section is mainly for readers of the Lean formalization.
These concepts matter for proofs and mechanization.
They are not the first concepts a protocol author usually needs.

### Bisimulation

Bisimulation compares two types by observable behavior rather than by literal syntax.
It is useful when recursive types differ syntactically but unfold to the same behavior.
This is a proof and equivalence technique.

In practice, bisimulation matters most when reasoning about proof identities, recursive encodings, and normalization arguments.
It is less central for day-to-day protocol authoring.

### De Bruijn Indices

The Lean formalization uses de Bruijn indices in foundational proof layers.
This avoids name-capture problems during substitution and recursion reasoning.
Rust-facing protocol APIs keep named recursion variables for usability.

If you are reading the proof code, expect de Bruijn forms in the foundational libraries.
If you are writing protocols, this detail is mostly invisible.

### Lean Formalization

The Lean formalization proves the core metatheory behind projection and protocol execution.
Important theorem families include coherence, preservation, progress, and harmony.
Current library structure and metrics are tracked in [Lean Verification Code Map](../lean/CODE_MAP.md).

At a high level, `SessionTypes` and `SessionCoTypes` cover syntax and equivalence.
`Choreography` covers projection and harmony.
`Protocol` covers coherence and typing.
`Runtime` covers the protocol-machine model and runtime correctness surfaces.

## Theory in Telltale

Telltale implements the theory across Rust and Lean.
The Rust crates provide executable data types and algorithms.
The Lean libraries provide mechanized proofs and proof-facing models.

On the Rust side, `telltale-types` defines `GlobalType` and `LocalTypeR`.
`telltale-theory` implements projection, merge, duality, and subtyping.
The runtime and machine layers then realize those structures operationally.

On the Lean side, the formalization provides the theorem libraries that justify those structures.
See [Lean Verification](801_lean_verification.md) for the proof pipeline and source layout.
See [Introduction](101_introduction.md) for the system-level overview.

## Conservation and Session Structure

Session types are Telltale's concrete realization of structure conservation.
The protocol type fixes the allowed interaction shape.
Local behavior must remain a valid projection of that shape.

The other conserved properties extend the guarantee surface beyond session structure alone.
Evidence governs witnesses and attestations.
Authority governs exclusive ownership.
Identity governs stable references.
Commitment governs outstanding effects.
Premise governs environmental assumptions.

In the runtime and Lean model, these properties are carried by explicit typed objects.
They are not left as ambient host assumptions.
See [Conservation Framework](102_conservation_framework.md) for the full conservation model.

## Further Reading

For deeper study of session type theory:

- [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf)
- [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf)
- [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf)

Within this documentation:

- [Introduction](101_introduction.md)
- [Choreographic DSL](202_choreographic_dsl.md)
- [Lean Verification](801_lean_verification.md)
