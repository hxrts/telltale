# Effects: Multiparty Session Types with Buffered Communication

This library formalizes a type system for **asynchronous multiparty session types** (MPST) with buffered message passing. The goal is to prove that well-typed programs cannot exhibit communication errors—messages are always received with the expected types, even when communication is non-blocking.

## Overview

### What Problem Does This Solve?

In distributed systems, processes communicate by sending and receiving messages. Without static guarantees, many things can go wrong:
- A process sends a string when the receiver expects an integer
- A process tries to receive when no message is available
- Two processes deadlock waiting for each other

**Session types** solve this by describing communication protocols as types. Each endpoint carries a local type that specifies what messages can be sent or received next.

### Why Async/Buffered?

Synchronous session types require send and receive to happen simultaneously. This is unrealistic for distributed systems where messages travel through networks.

**Asynchronous session types** allow sends to complete immediately by buffering messages. The receiver can dequeue messages later. This introduces a key challenge: how do we ensure type safety when sent messages are "in flight"?

### Why Multiparty?

Binary session types only handle two communicating parties. Real protocols often involve three or more participants (e.g., client-server-database, buyer-seller-shipper). **Multiparty session types** extend the framework to handle N participants, with communication directed between specific roles.

### The Coherence Invariant

The central insight is the **coherence invariant**: we track not just local types, but also the types of messages currently in transit (the "delayed type environment" `D`). For each directed edge (sender → receiver), the sender's and receiver's local types must be consistent with the in-flight message trace.

```
Coherent(G, D) :=
  ∀ edge (sender → receiver),
    the sender's local type is consistent with what was sent (tracked in D)
    the receiver's local type can consume the pending messages
```

## Architecture

```
Effects/
├── Basic.lean         # SessionId, Role, Endpoint, Edge
├── LocalType.lean     # Local types with role-directed actions
├── Values.lean        # Runtime values with endpoint channels
├── Environments.lean  # Per-edge buffers and type environments
├── Coherence.lean     # Multiparty coherence invariant
├── Process.lean       # MPST process language
├── Typing.lean        # Process typing rules
├── Semantics.lean     # Async operational semantics
└── Preservation.lean  # Subject reduction theorem
```

## Module Details

### `Basic.lean`
Foundational types for multiparty communication:
- `SessionId`: natural number identifying a session instance
- `Role`: string identifier for participants (e.g., "Alice", "Bob")
- `Endpoint`: `(SessionId × Role)` pair
- `Edge`: `(SessionId × sender × receiver)` for directed communication
- `RoleSet`: set of roles participating in a session

### `LocalType.lean`
Local session types with role-directed actions:
- `send r T L` - send type `T` to role `r`, continue as `L`
- `recv r T L` - receive type `T` from role `r`, continue as `L`
- `select r bs` - select label to send to role `r`
- `branch r bs` - branch on label received from role `r`
- `end_` - terminated session
- `mu L` / `var n` - recursive types (de Bruijn indices)

### `Values.lean`
Runtime values:
- `Value`: unit, bool, nat, string, products, endpoint channels
- `ValType`: corresponding value types
- `ValType.isLinear`: channels are linear (must be used exactly once)

### `Environments.lean`
Typed environments:
- `Store`: Var → Value (runtime variable bindings)
- `SEnv`: Var → ValType (static typing environment)
- `Buffer`: List Value (message queue per edge)
- `Buffers`: Edge → Buffer (all message queues)
- `GEnv`: Endpoint → LocalType (current local types)
- `DEnv`: Edge → List ValType (in-flight message types per edge)

### `Coherence.lean` ★
The key MPST coherence proofs:
- `EdgeCoherent`: coherence for a single directed edge
- `Coherent`: all edges are coherent
- `Coherent_send_preserved`: coherence maintained after send
- `Coherent_recv_preserved`: coherence maintained after receive

**Proof Technique**: 3-way case split on edges:
1. Edge being updated
2. Edge involving modified endpoint
3. Unrelated edge (environments unchanged)

### `Process.lean`
The process calculus:
- `skip`, `seq`, `par` - structural constructs
- `send k x` - send value x through channel k
- `recv k x` - receive into x through channel k
- `select k ℓ` - select label ℓ on channel k
- `branch k bs` - branch on incoming label
- `assign x v` - assign value to variable
- `newSession roles f P` - create session with roles

### `Typing.lean`
Process typing judgment:
- `HasTypeProcN`: typing judgment tracking environment evolution
- `WTConfigN`: well-typed configuration predicate
- Rules for each process construct

### `Semantics.lean`
Operational semantics:
- `StepBase`: primitive reductions (send enqueues, recv dequeues)
- `Step`: contextual closure (seq/par evaluation contexts)
- Helper functions: `sendStep`, `recvStep`

### `Preservation.lean`
The main metatheory:
- `preservation_send`: send step preserves typing
- `preservation_recv`: recv step preserves typing
- `preservation`: main subject reduction theorem
- `progress`: progress theorem (terminates, steps, or blocked on recv)

## Proof Status

### Structure Complete ✓

- [x] Core type definitions (LocalType, Endpoint, Edge)
- [x] Environment operations (lookup, update)
- [x] Coherence definition (EdgeCoherent, Coherent)
- [x] Process language and typing
- [x] Operational semantics
- [x] Theorem statements

### Proofs with `sorry` (TODO)

The following proofs have detailed strategies documented but are incomplete:

#### Environment Lemmas
- [ ] `lookupStr_update_eq/neq` - Store lookup/update
- [ ] `lookupG_update_eq/neq` - GEnv lookup/update
- [ ] `lookupBuf_update_eq/neq` - Buffer lookup/update
- [ ] `lookupD_update_eq/neq` - DEnv lookup/update

#### Coherence Preservation
- [ ] `Coherent_send_preserved` - 3-way edge case analysis
- [ ] `Coherent_recv_preserved` - 3-way edge case analysis
- [ ] `Coherent_empty` - Empty environments are coherent
- [ ] `initSession_coherent` - Initialized sessions are coherent

#### Typing Preservation
- [ ] `StoreTyped_update_nonChan` - Store typing preserved
- [ ] `BuffersTyped_enqueue` - Buffer typing after enqueue
- [ ] `preservation_send` - Send step preservation
- [ ] `preservation_recv` - Recv step preservation
- [ ] `preservation` - Main theorem
- [ ] `progress` - Progress theorem

## Key Theorems

### Subject Reduction (Preservation)
```lean
theorem preservation
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (C C' : Config)
    (hWT : WTConfigN n S G D C)
    (hStep : Step C C') :
    ∃ n' S' G' D', WTConfigN n' S' G' D' C'
```

If a well-typed configuration takes a step, the resulting configuration is also well-typed (under possibly updated environments).

### Coherence Preservation
```lean
theorem Coherent_send_preserved
    (G : GEnv) (D : DEnv) (senderEp : Endpoint) (receiverRole : Role)
    (T : ValType) (L : LocalType)
    (hCoh : Coherent G D)
    (hG : lookupG G senderEp = some (.send receiverRole T L)) :
    let e := { sid := senderEp.sid, sender := senderEp.role, receiver := receiverRole }
    Coherent (updateG G senderEp L) (updateD D e (lookupD D e ++ [T]))
```

When an endpoint sends type `T`, advancing its local type from `send r T L` to `L`, coherence is maintained by appending `T` to the edge's in-flight trace.

## Key Design Insights

### 1) Communication modeled like real systems: buffers are first-class state

Instead of rendezvous send/recv, the network is explicit:
* **`send` enqueues** and continues immediately
* **`recv` dequeues** from an explicit per-edge FIFO buffer
* Buffers are keyed by directed edges `(sid, sender, receiver)`

### 2) Typed "shadow buffer" (`D`) tracks in-flight messages statically

The type-level traces in `DEnv` mirror the runtime buffers:
* Runtime buffers: `Buffers : Edge → List Value`
* Type-level traces: `DEnv : Edge → List ValType`

This is what makes asynchronous fidelity provable: preservation updates both in lockstep.

### 3) Coherence is semantics-dependent via `Consume`

The `Coherent(G,D)` invariant says:
> For each edge, after consuming the queued types, the sender's and receiver's local types are compatible.

The `Consume` function operationally models how a local type evolves as buffered messages arrive.

## Usage Example

```lean
import Effects

-- Define roles
def alice : Role := "Alice"
def bob : Role := "Bob"

-- A local type for Alice: send Nat to Bob, then recv Bool from Bob
def aliceType : LocalType :=
  .send bob .nat (.recv bob .bool .end_)

-- A local type for Bob: recv Nat from Alice, then send Bool to Alice
def bobType : LocalType :=
  .recv alice .nat (.send alice .bool .end_)
```

## References

- Gay & Hole, "Subtyping for Session Types in the Pi Calculus" (2005)
- Deniélou & Yoshida, "Dynamic Multirole Session Types" (2011)
- Scalas & Yoshida, "Less is More" (2019)
- Lindley & Morris, "A Semantics for Propositions as Sessions" (2015)

## Building

```bash
cd lean
lake build Effects
```

Requires Mathlib (see `lakefile.lean` for version).
