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

At the core is an **asynchronous multiparty session calculus** where a running system state is explicit: processes execute while messages sit in **unbounded FIFO buffers**. Instead of a binary endpoint `(id, L/R)`, an endpoint is a **session id plus role** `(sid, r)`, and messages flow along directed edges `(sid, p → q)`. The operational semantics is "real": a send by role `p` to `q` **enqueues** immediately (no rendezvous), and a receive by `q` from `p` **dequeues** when the corresponding buffer edge is nonempty. Session creation allocates a fresh `sid` and initializes empty buffers for all relevant role-to-role edges (or mailboxes, depending on the delivery model you pick).

Typing is split into three coupled environments that are checked and evolved together. First, `G` maps each role endpoint `(sid, r)` to a **local session type** (MPST local types: `!q(T).L`, `?p(T).L`, plus labeled selection/branching). Second, `D` maps each directed edge `(sid, p→q)` to a **type-level shadow queue**—a list of message types (and labels) that predicts exactly what values are currently in flight on that edge. Third, `S` (and a heap typing if you include state) tracks ordinary values, references, and effect capabilities. The crucial invariant is that runtime buffers `B` are related to `D` by `BuffersTyped`: every queued runtime value on `(sid, p→q)` matches the head types recorded in `D(sid, p→q)`.

"Global correctness" is expressed as a semantics-dependent **coherence condition** over `(G, D)` rather than a simple binary duality. Coherence says: if you "consume" the queued traces `D` against the local types in `G` (a function like your `Consume`, generalized to directed edges and labels), then all roles' remaining local types are mutually compatible—equivalently, they are consistent with some global conversation shape (either explicitly stored as a global type and checked by projection, or implicitly by a compatibility relation). This is what makes the system robust under real asynchrony: coherence talks about **in-flight messages**, so connecting components is safe even when buffers are non-empty, and protocol agreement is stated relative to the actual delivery discipline (FIFO-per-edge first, then generalize).

Composable effects fit in by making "communication state" and "effect state" coexist without collapsing guarantees. The process typing judgment is effect-aware: a process is typed not just with `(S,G,D)` but also with an **effect context** (exceptions/cancellation, transactions/rollback, shared state via references, etc.) and explicit side conditions that preserve session invariants. The discipline is: linear resources (endpoints/tokens) cannot be duplicated or stored in shared locations unless mediated by a controlled capability; effect steps may interleave freely with communication steps, but any effect that can abort or roll back must do so in a way that keeps `(G,D,B)` coherent (e.g., a receive that "fails" cannot partially consume the queue trace). The result is a conditional but crisp theorem package: preservation always, and progress/non-stuckness relative to stated delivery/scheduler and effect assumptions.

Finally, to support **safe runtime composition between untrusted nodes**, you wrap the boundary in a **proof-carrying runtime monitor**. Each node presents a compact *boundary certificate* describing the endpoints it owns, the local types it claims for them, and (critically) the shadow traces `D` for edges it shares; the monitor checks a decidable "link" condition (linearity/non-aliasing + buffer/type-trace agreement + coherence after consuming queued traces). After linking, nodes don't directly enqueue/dequeue—every send/recv goes through the verified monitor, which updates `B`, `D`, and `G` in lockstep and issues fresh linear tokens so endpoints can't be misused or aliased. The big meta-theorem you aim for is: **if the monitor accepts steps, the global invariant holds forever**, so no participant can ever observe a protocol mismatch even under unbounded buffering, dynamic composition, and interleaved effects.


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
Runtime values and linear capabilities:
- `Value`: unit, bool, nat, string, products, endpoint channels
- `ValType`: corresponding value types
- `ValType.isLinear`: channels are linear (must be used exactly once)
- `Token`, `LinCtx`: linear capability tokens and their context

### `Environments.lean` (Environments/Part1–2)
Typed environments:
- `Store`: Var → Value (runtime variable bindings)
- `SEnv`: Var → Option ValType (static typing environment)
- `Buffer`: List Value (message queue per edge)
- `Buffers`: Edge → Buffer (all message queues)
- `GEnv`: Endpoint → LocalType (current local types)
- `DEnv`: Edge → Option (List ValType) (in-flight message types per edge)

### `Coherence.lean` (Coherence/Part1–9)
The key MPST coherence proofs:
- `Consume`: how a local type evolves as buffered messages arrive
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

### `Typing.lean` (Typing/Part1–7)
Process typing judgment:
- `HasTypeProcN`: typing judgment tracking environment evolution
- `WTConfigN`: well-typed configuration predicate
- `ParSplit`: environment splitting for parallel composition
- Rules for each process construct
- `preservation_typed`, `progress_typed`: main metatheory at the typed level

### `Semantics.lean`
Operational semantics:
- `StepBase`: primitive reductions (send enqueues, recv dequeues, select, branch, newSession, assign)
- `Step`: contextual closure (seq/par evaluation contexts)
- Helper functions: `sendStep`, `recvStep`

### `Simulation.lean`
Executable simulation for protocol testing:
- `stepDecide`: decidable step function, attempts one step and returns `some C'` or `none`
- `runSteps`: execute multiple steps until stuck or fuel exhausted
- `traceSteps`: execute and collect the full trace
- `stepDecide_sound`, `stepDecide_complete`: correctness of the decision procedure

### `Preservation.lean`
The main metatheory (wrappers):
- `preservation`: TypedStep preserves WellFormed
- `progress`: WellFormed processes can step or are blocked
- `subject_reduction`: TypedStep implies Step (soundness)

### `DeadlockFreedom.lean`
Deadlock freedom infrastructure:
- `Guarded`: local type is guarded (no unproductive recursion like `μX.X`)
- `guardedDecide`: decidable checker for guardedness
- `ReachesComm`: a local type can reach a communication action
- `reachesCommDecide`: decidable checker for ReachesComm
- `Done`: configuration has terminated (all processes skip, all types end)
- `CanProgress`: configuration can take a step
- `Stuck`: neither done nor can progress
- `FairTrace`: fairness assumption for delivery
- `deadlock_free`: the main deadlock freedom theorem

### `Determinism.lean`
Determinism and confluence:
- `uniqueBranchLabelsList`: branch labels are unique
- `stepBase_det_send`, `stepBase_det_recv`: base step determinism
- `IndependentSessions`, `IndependentConfigs`: session isolation
- `diamond_independent_sessions`: diamond property for steps on disjoint sessions

### `Monitor.lean` (Monitor/Part1–2)
Proof-carrying runtime monitor:
- `MonitorState`: tracks `G`, `D`, buffers, linear context, fresh session ID supply
- `MonStep`: judgment for valid monitor transitions (send, recv, select, branch, newSession)
- `MonStep_preserves_WTMon`: valid transitions preserve well-typedness
- Untrusted code interface: present token → request action → monitor validates → returns new token

### `Spatial.lean`
Spatial type system for deployment:
- `SpatialReq`: requirement language (`netCapable`, `timeoutCapable`, `colocated`, `reliableEdge`, `conj`, `top`, `bot`)
- `Topology`: deployment topology (site assignment for roles)
- `Satisfies`: satisfaction judgment `topo |= R`
- `SpatialLe`: spatial subtyping preorder
- `spatial_le_sound`: monotonicity theorem

### `Decidability.lean`
Decidability instances:
- `instDecidableReachesComm`: decidable ReachesComm
- `instDecidableSatisfies`: decidable spatial satisfaction
- `edgeCoherent_empty_trace`, `bufferTyped_empty`: base cases

### `Deployment.lean` (Deployment/Part1–2, Part2a–2b)
Deployed protocol bundles and composition:
- `InterfaceType`: what a protocol exports/imports for composition
- `DeployedProtocol`: complete bundle with all certificates (coherence, deadlock freedom, spatial satisfaction)
- `ProtocolBundle`: lightweight bundle without proofs (for runtime)
- Composition/linking: disjoint session IDs, matching exports/imports, merged environments remain coherent

### `Examples.lean`
Concrete protocol examples with full proofs:
- `PingPong`: two-party ping-pong protocol
- `TwoBuyer`: three-party buyer protocol
- Coherence, deadlock freedom, and buffer typing demonstrated


## Proof Status

### Structure Complete

- [x] Core type definitions (LocalType, Endpoint, Edge)
- [x] Environment operations (lookup, update)
- [x] Coherence definition and preservation (EdgeCoherent, Coherent, send/recv preserved)
- [x] Process language and typing
- [x] Operational semantics
- [x] Simulation (decidable step function)
- [x] Deadlock freedom infrastructure
- [x] Runtime monitor and preservation
- [x] Determinism and session isolation
- [x] Spatial type system and decidability
- [x] Deployment bundles and composition
- [x] Worked examples (PingPong, TwoBuyer)

### Axiom Status

All prior axioms and sorries in `Effects/` are discharged. The development is axiom-free; any remaining assumptions are explicit hypotheses on theorems (e.g., the `ProgressReady` gap used to bridge to projection in Part 2).


## Key Theorems

### Subject Reduction (Preservation)
```lean
theorem preservation
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    WellFormed G D Ssh Sown store bufs P →
    WellFormed G' D' Ssh Sown' store' bufs' P'
```

Typed steps preserve well-formedness, and TypedStep soundness links back to the untyped semantics.

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

### Monitor Preservation
```lean
theorem MonStep_preserves_WTMon :
    MonStep ms ms' → WTMon ms → WTMon ms'
```

Every valid monitor transition preserves the well-typedness invariant, so the monitor can never enter an inconsistent state.


## Key Design Insights

### 1) Communication modeled like real systems: buffers are first-class state

Instead of rendezvous send/recv, the network is explicit:
* **`send` enqueues** and continues immediately
* **`recv` dequeues** from an explicit per-edge FIFO buffer
* Buffers are keyed by directed edges `(sid, sender, receiver)`

### 2) Typed "shadow buffer" (`D`) tracks in-flight messages statically

The type-level traces in `DEnv` mirror the runtime buffers:
* Runtime buffers: `Buffers : Edge → List Value`
* Type-level traces: `DEnv : Edge → Option (List ValType)`

This is what makes asynchronous fidelity provable: preservation updates both in lockstep.

### 3) Coherence is semantics-dependent via `Consume`

The `Coherent(G,D)` invariant says:
> For each edge, after consuming the queued types, the sender's and receiver's local types are compatible.

The `Consume` function operationally models how a local type evolves as buffered messages arrive.

### 4) Time in the protocol is modeled as choice, not clocks

The effect system draws a sharp line between **protocol-level time** and **clock time**:

* **Protocol-level time is choice.** A timeout, a deadline, or any time-dependent branch is represented as a `select`/`branch` pair. One label means "the timed event fired" and another means "communication arrived first." From the protocol's perspective, this is an ordinary labeled choice — the type system sees a discrete fork, not a duration.

* **Clock time is an entirely local runtime concern.** Which branch actually fires — timeout vs. message — is decided by local infrastructure: OS timers, the scheduler, the network stack. The formal model never mentions clocks, durations, or wall time. It only requires that *some* label is chosen and that the choice is communicated through the normal `select`/`branch` mechanism.

* **`SpatialReq.timeoutCapable`** bridges the two layers. It is a static, structural assertion that a deployment site *can* fire timeout events. It lives in the spatial type system (`Spatial.lean`) and is checked before execution begins — it does not introduce temporal operators into the session type system itself.

This separation keeps the entire metatheory — preservation, coherence, deadlock freedom — free of real-time reasoning while still supporting timeout-based protocols in practice. A protocol that says "Alice selects `timeout` or `ack` to Bob" is well-typed and coherent regardless of how Alice's runtime decides between the two labels.

### 5) Space in the protocol is modeled as spatial requirements with subtyping

Protocols declare *what* their deployment needs — not *where* things run. The spatial type system (`Spatial.lean`) captures this:

* **`SpatialReq`** is a small requirement language: `netCapable s` (site has network), `timeoutCapable s` (site can fire timeouts), `colocated r₁ r₂` (roles share a site), `reliableEdge r₁ r₂` (reliable transport between roles), composed with `conj`/`top`/`bot`.

* **`Topology`** is the deployment witness: it assigns roles to sites, declares reliable edges, and lists per-site capabilities. It is external data — the protocol does not compute it.

* **`Satisfies` (`topo ⊨ R`)** is the satisfaction judgment: does the topology provide what the requirement asks for? This is decidable (`satisfiesBool`).

* **`SpatialLe` (`R₁ ≤ₛ R₂`)** is a spatial subtyping preorder. `R₁ ≤ₛ R₂` means R₁ is at least as demanding as R₂ — any topology satisfying R₁ also satisfies R₂. The monotonicity theorem `spatial_le_sound` proves this. Stronger requirements yield more portable protocols; weaker requirements yield more deployment flexibility.

* **Requirement extraction** bridges session types and spatial needs: `commReq` requires network capability for both endpoints of an edge, `timedChoiceReq` requires timeout capability at the decider's site, and `edgeReq`/`endpointReq` connect `Edge`/`Endpoint` values to their spatial obligations.

Like time, space is kept out of the session type metatheory. The spatial layer is checked once at deployment time; the preservation and coherence theorems hold independently of which topology is chosen.


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
