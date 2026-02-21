# Theory

This document provides a primer on the theoretical foundations of Telltale. It covers session types, multiparty session types, and the key properties that make them useful for distributed programming. It also covers delivery models, coherence, harmony, and delegation.

## Why Session Types

Distributed systems are difficult to program correctly. Participants must coordinate their communication to avoid deadlocks, message mismatches, and protocol violations. Traditional type systems check data types but not communication patterns.

Session types fill this gap. They describe communication protocols as types. The type system then checks that implementations follow the protocol. Errors that would otherwise appear at runtime become compile-time type errors.

## Binary Session Types

Binary session types describe communication between exactly two parties. Each party has a session type that specifies what messages they send and receive in what order.

### Basic Syntax

The fundamental operations are send and receive.

| Syntax | Meaning |
|--------|---------|
| `!T.S` | Send a value of type T, then continue as S |
| `?T.S` | Receive a value of type T, then continue as S |
| `end`  | Session complete |

A session type is a sequence of these operations. The type `!Int.?Bool.end` means send an integer, receive a boolean, then terminate.

### Duality

For two parties to communicate correctly, their session types must be dual. If one party sends, the other must receive. If one party terminates, the other must also terminate.

| Type | Dual |
|------|------|
| `!T.S` | `?T.S̄` |
| `?T.S` | `!T.S̄` |
| `end` | `end` |

The dual of `!Int.?Bool.end` is `?Int.!Bool.end`. When two parties with dual types communicate, every send has a matching receive.

### Choice and Branching

Protocols often involve decisions. One party chooses which branch to take and the other party follows.

| Syntax | Meaning |
|--------|---------|
| `⊕{l₁: S₁, l₂: S₂}` | Internal choice: select and send a label |
| `&{l₁: S₁, l₂: S₂}` | External choice: receive a label and branch |

Internal choice (`⊕`) is the active side that decides. External choice (`&`) is the passive side that reacts. These are dual to each other.

### Example: Request-Response

A client sends a request and receives a response.

```
Client: !Request.?Response.end
Server: ?Request.!Response.end
```

These types are dual. The client sends then receives. The server receives then sends. Both terminate together.

## Multiparty Session Types

Binary session types handle two parties. Multiparty session types (MPST) handle protocols with three or more participants. This extension requires new concepts.

### The Challenge

With two parties, duality ensures compatibility. With three or more parties, the situation is more complex. Messages between Alice and Bob affect what Carol expects. The type system must track these dependencies across all participants.

### Global Types

Global types describe the protocol from a neutral perspective. They specify all interactions between all participants without favoring any viewpoint.

```
G = Alice -> Bob: Request.
    Bob -> Carol: Forward.
    Carol -> Bob: Result.
    Bob -> Alice: Response.
    end
```

This global type specifies a four-message protocol. Alice sends to Bob, Bob forwards to Carol, Carol replies to Bob, and Bob responds to Alice.

### Local Types

Local types describe the protocol from one participant's viewpoint. Each participant sees only the messages they send or receive.

From the global type above:

```
Alice: Bob!Request.Bob?Response.end
Bob:   Alice?Request.Carol!Forward.Carol?Result.Alice!Response.end
Carol: Bob?Forward.Bob!Result.end
```

Alice sees two messages. Bob sees four. Carol sees two. Each local type captures exactly that participant's communication.

### Projection

Projection is the algorithm that transforms a global type into local types. For each role, projection extracts the relevant communication actions.

The projection of `Alice -> Bob: M.G` for role R is:
- If R = Alice: `Bob!M.project(G, Alice)`
- If R = Bob: `Alice?M.project(G, Bob)`
- Otherwise: `project(G, R)`

Projection preserves protocol structure while extracting the local view.

### Merging

When a global type has branches, projection must merge the local views. Consider:

```
G = Alice -> Bob: {
      Left: Bob -> Carol: X.end,
      Right: Bob -> Carol: Y.end
    }
```

Carol's projection must handle both branches. The merge operation combines `Bob?X.end` and `Bob?Y.end` into `Bob?{X, Y}.end`.

Merge succeeds when branches are compatible. It fails when branches conflict in ways that would leave a participant unable to distinguish which branch was taken.

## Well-Formedness

Not every syntactically valid type is meaningful. Well-formedness conditions ensure types represent sensible protocols.

### Global Type Conditions

A global type is well-formed when:
- All recursion variables are bound
- All communication branches are non-empty
- No participant sends to themselves
- Recursion passes through at least one communication

The productivity condition prevents types like `μX.X` that recurse without doing anything.

### Local Type Conditions

A local type is well-formed when:
- It is closed (no free variables)
- It is contractive (recursion unfolds to observable action)

Contractiveness ensures that unfolding a recursive type eventually produces a send, receive, or termination.

## Subtyping

Subtyping determines when one session type can substitute for another. A subtype can do everything the supertype promises and possibly more.

### Synchronous Subtyping

Synchronous subtyping assumes messages are delivered instantly. The rules are:

- A type that sends more labels is a subtype (internal choice covariance)
- A type that receives fewer labels is a subtype (external choice contravariance)
- Continuations must be subtypes recursively

### Asynchronous Subtyping

Asynchronous subtyping accounts for message buffering. Messages may arrive before they are expected. This relaxes some constraints but complicates the analysis.

The key insight is that output actions can be reordered with respect to input actions under certain conditions. This enables optimizations that would be unsound in synchronous semantics.

Telltale implements the asynchronous subtyping algorithm from Bravetti et al. (POPL 2021) which decomposes types into single-input-single-output segments for decidable checking.

## Bisimulation

Two session types are bisimilar when they exhibit the same observable behavior. Bisimulation is a coinductive relation that compares types by their transitions.

Types T and S are bisimilar when:
- Every transition of T can be matched by a transition of S to bisimilar states
- Every transition of S can be matched by a transition of T to bisimilar states

Bisimulation is useful for comparing recursive types where structural equality is too strict. Two types with different recursion structure may still be bisimilar if they unfold to the same infinite behavior.

## Safety Properties

Session type theory establishes several safety properties for well-typed programs.

### Preservation

Preservation (subject reduction) states that well-typed configurations remain well-typed after transitions. If a protocol state is valid and takes a step, the resulting state is also valid.

This ensures that type safety is maintained throughout execution. A program that starts in a well-typed state cannot reach an ill-typed state.

### Progress

Progress states that well-typed configurations can always take a step or have terminated. No participant is stuck waiting for a message that will never arrive.

Progress depends on assumptions. Telltale's progress theorems require explicit premises:
- Well-typedness of the configuration
- Reachability of communication (no infinite internal computation)
- Fair scheduling (all participants eventually run)

### Deadlock Freedom

Deadlock freedom follows from preservation and progress together. A well-typed protocol cannot reach a state where all participants are blocked.

This property is assumption-scoped. It holds under the premises required for progress. Circular dependencies between participants are ruled out by the global type structure.

### Harmony

Harmony states that projection commutes with protocol evolution. When the global protocol takes a step, projecting the result equals taking the corresponding local step on the projected type.

```
project(step(G)) = localStep(project(G))
```

This equation establishes that global and local views remain synchronized. The global choreography and the local implementations evolve in lockstep.

Harmony is essential for compositional reasoning. It allows proving properties at the global level and transferring them to local implementations. Without harmony, the connection between choreography and endpoint code would be unclear.

## Delegation

Delegation allows dynamic changes to participant sets during protocol execution. A participant can transfer their session endpoint to another party. The receiving party takes over the communication obligations.

### The Problem

Static MPST assumes a fixed set of participants. The global type names all roles at the start. But real distributed systems often need dynamic topology. New participants join. Existing participants leave. Capabilities transfer between parties.

### Delegation Operations

A delegation operation transfers an endpoint from one participant to another. The delegating party sends a channel endpoint. The receiving party gains the ability to communicate on that channel.

```
Alice -> Bob: delegate(channel_to_Carol)
```

After this operation, Bob can communicate with Carol on the delegated channel. Alice no longer participates in that sub-protocol.

### Reconfiguration Harmony

Delegation introduces a reconfiguration step that changes the participant structure. Telltale proves that harmony extends to these reconfiguration steps. Projection commutes with both static linking and dynamic delegation.

The reconfiguration harmony theorem covers two cases. Static composition through linking combines independent sub-protocols. Dynamic delegation transfers endpoints during execution. Both preserve coherence when well-formedness conditions hold.

### Delegation Safety

For delegation to be safe, certain conditions must hold. The delegated endpoint must be in a state compatible with the receiver's expectations. The delegation must not create orphaned messages or dangling references.

Telltale's `DelegationWF` predicate captures these conditions. The safe delegation theorem shows that coherence is preserved when this predicate holds.

## Coherence

Coherence is the invariant that makes multiparty session types work. It ensures that the collective state of all participants remains consistent with the global protocol.

In Telltale, coherence is formulated as a per-edge property. Each communication edge between two roles maintains a coherence invariant involving:
- The message buffer contents
- The local type states of both endpoints
- The global type structure

The `Consume` function is the recursive alignment check at the heart of coherence. It interprets buffered traces against receiver expectations. For a receiver expecting type T and a buffer containing messages [m1, m2, ...], `Consume` verifies that each message matches the expected type at that point.

Two key lemmas support preservation proofs. `Consume_append` shows that consumption over concatenated traces factors through sequential consumption. `Consume_cons` shows that head consumption reduces to one-step alignment plus recursive continuation alignment. These lemmas isolate message-type alignment complexity into reusable components.

## Delivery Models

Asynchronous session types parameterize over message delivery semantics. Different delivery models affect what orderings are possible and what safety properties hold.

### FIFO Delivery

FIFO (first-in-first-out) delivery guarantees that messages between any two participants arrive in the order they were sent. If Alice sends m1 then m2 to Bob, Bob receives m1 before m2.

This is the most common model in MPST literature. It matches the behavior of TCP connections and many message queue systems.

### Causal Delivery

Causal delivery preserves causality across all participants. If message m1 causally precedes message m2, then any participant that receives both will receive m1 first.

Causal delivery is stronger than FIFO. It handles scenarios where Alice sends to Bob, Bob sends to Carol based on that message, and Carol must see consistent ordering even though she communicates with both.

### Lossy Delivery

Lossy delivery permits message loss. Messages may fail to arrive. The type system must account for this possibility in its safety guarantees.

Telltale's theorems are parameterized by `DeliveryModel`. This gives one theorem shape across FIFO, causal, and lossy instances. The delivery model affects which buffer orderings are possible and which coherence conditions must hold.

## Recursion

Session types support recursive protocols through fixed-point constructs.

### Named Recursion

Named recursion binds a variable to a type body.

```
μX. Alice -> Bob: Ping. Bob -> Alice: Pong. X
```

This protocol repeats forever. The variable X refers back to the enclosing μ.

### De Bruijn Indices

Internally, Telltale uses de Bruijn indices for recursion. Instead of names, variables are represented by their binding depth. This simplifies substitution and avoids name capture issues.

The index 0 refers to the innermost binder. The index 1 refers to the next enclosing binder. This representation is used in the Lean formalization and the Rust core types.

## Telltale Implementation

Telltale implements these concepts in Rust with formal verification in Lean.

### Rust Types

The `telltale-types` crate defines `GlobalType` and `LocalTypeR` matching the theory. The `telltale-theory` crate implements projection, merge, duality, and subtyping algorithms.

### Lean Formalization

The Lean formalization in `lean/` proves preservation, progress, and coherence theorems. The formalization covers 610 files and approximately 126,000 lines of verified code.

Key libraries include:
- `SessionTypes` and `SessionCoTypes` for type definitions and bisimulation
- `Choreography` for projection and harmony proofs
- `Protocol` for coherence and preservation
- `Runtime` for VM correctness

See `lean/CODE_MAP.md` for detailed documentation of the proof structure.

## Further Reading

For deeper study of session type theory:

- [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf) provides an accessible overview.
- [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf) covers asynchronous subtyping.
- [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf) integrates session types with choreographic programming.

Within this documentation:
- [Background](00_introduction.md) introduces the concepts in context
- [Choreographic DSL](04_choreographic_dsl.md) shows how to write protocols
- [Lean Verification](18_lean_verification.md) details the proof infrastructure
