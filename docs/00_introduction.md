# Background

This document introduces the theory behind Telltale. It covers multiparty session types, choreographic programming, and algebraic effects. These concepts explain how the system enforces type-safe distributed programming.

## Session Types

Session types encode communication protocols as types. They specify the sequence and structure of messages exchanged between processes. A session type is a contract for communication. The compiler checks that implementations follow this contract.

Traditional type systems ensure data safety. They prevent type errors like passing a string where an integer is expected. Session types extend this to communication safety. They prevent protocol errors like sending when you should receive or terminating when more messages are expected.

A session type describes a communication channel from one endpoint's perspective. The type `!String.?Int.end` means send a string, then receive an integer, then close the channel. The dual type `?String.!Int.end` means receive a string, then send an integer, then close.

These types are complementary and ensure the endpoints coordinate correctly.

## Multiparty Session Types (MPST)

Multiparty session types extend binary session types to protocols with three or more participants. Session types handle point-to-point channels. MPST handles protocols where multiple parties interact. The type system ensures all interactions remain synchronized.

MPST introduces challenges beyond binary sessions. Participants must agree on the overall protocol flow. Messages between two participants affect what other participants can do next. The type system tracks these dependencies to prevent global deadlocks.

In MPST, each participant has a local view that includes all partners. The customer type shows communication with both merchant and bank. The system ensures all views are compatible. For a deeper discussion of MPST theory, see [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf).

Advanced optimizations through asynchronous subtyping are covered in [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf). [Mechanised Subject Reduction for Multiparty Asynchronous Session Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.31) includes a mechanized Coq proof that adds a well-typed condition that fixes the original MPST formulation by Honda et al. The type theory in this crate draws from this revised formulation.

## Global Types and Projection

Global types describe protocols from a neutral perspective. They specify all interactions between all participants. Local types describe the protocol from one participant's viewpoint. Projection transforms global types into local types for each participant.

```
G = Alice -> Bob: Int.
    Bob -> Alice: {Sum: Int, Product: Int}
```

This global type projects to different local types. Alice gets `Bob!Int.Bob&{Sum: Int, Product: Int}`. Bob gets `Alice?Int.Alice⊕{Sum: Int, Product: Int}`. Each participant sees only their part of the protocol.

The projection algorithm ensures the local types are compatible. Deadlock-freedom claims in this project are assumption-scoped and theorem-specific. Typical premises include well-typedness, progress reachability, and fairness scheduling assumptions. Under those premises, participants complete without protocol communication errors.

## Lean Signatures (Core Types)

Telltale formalizes its core in Lean. The core session types are `GlobalType`, `LocalTypeR`, and `LocalTypeC`. These are the global protocol type, the recursive local type, and the coinductive local type used in bisimulation proofs.

The signatures below match the current Lean modules with namespaces preserved.

### Global types and labels (`lean/SessionTypes/GlobalType/Core.lean`)

```lean
namespace SessionTypes.GlobalType

inductive PayloadSort where
  | unit : PayloadSort
  | nat : PayloadSort
  | bool : PayloadSort
  | string : PayloadSort
  | real : PayloadSort
  | vector : Nat → PayloadSort
  | prod : PayloadSort → PayloadSort → PayloadSort
  deriving Repr, DecidableEq, BEq, Inhabited

structure Label where
  name : String
  sort : PayloadSort := PayloadSort.unit
  deriving Repr, DecidableEq, BEq, Inhabited

inductive GlobalType where
  | end : GlobalType
  | comm : String → String → List (Label × GlobalType) → GlobalType
  | mu : String → GlobalType → GlobalType
  | var : String → GlobalType
  | delegate : String → String → Nat → String → GlobalType → GlobalType
  deriving Repr, Inhabited

end SessionTypes.GlobalType
```

This file defines the global protocol structure and its label and payload types. It is the source of truth for Lean global type syntax.

### Inductive local types (`lean/SessionTypes/LocalTypeR/Core.lean`)

```lean
namespace SessionTypes.LocalTypeR

open SessionTypes.GlobalType
open SessionTypes (ValType)

inductive LocalTypeR where
  | end : LocalTypeR
  | send : String → List (Label × Option ValType × LocalTypeR) → LocalTypeR
  | recv : String → List (Label × Option ValType × LocalTypeR) → LocalTypeR
  | mu : String → LocalTypeR → LocalTypeR
  | var : String → LocalTypeR
  deriving Repr, Inhabited

end SessionTypes.LocalTypeR
```

This file defines the recursive local type used for projection and type checking. It mirrors the Rust `LocalTypeR` structure.

### Coinductive local types (`lean/SessionCoTypes/Coinductive/LocalTypeC.lean`)

```lean
namespace SessionCoTypes.Coinductive

open SessionTypes.GlobalType

inductive LocalTypeHead where
  | end  : LocalTypeHead
  | var  : String → LocalTypeHead
  | mu   : String → LocalTypeHead
  | send : String → List Label → LocalTypeHead
  | recv : String → List Label → LocalTypeHead
  deriving Repr, DecidableEq

def LocalTypeChild : LocalTypeHead → Type
  | .end       => PEmpty
  | .var _     => PEmpty
  | .mu _      => Unit
  | .send _ ls => Fin ls.length
  | .recv _ ls => Fin ls.length

def LocalTypeF : PFunctor := ⟨LocalTypeHead, LocalTypeChild⟩

abbrev LocalTypeC := PFunctor.M LocalTypeF

end SessionCoTypes.Coinductive
```

This file defines the coinductive local type encoding. It supports bisimulation proofs and coinductive reasoning.

## Well-Formedness (Lean)

Well-formedness is explicit in the Lean development.

Global types are well-formed when all of the following hold.

```lean
def GlobalType.wellFormed (g : GlobalType) : Bool :=
  g.allVarsBound && g.allCommsNonEmpty && g.noSelfComm && g.isProductive
```

This definition checks variable binding, non-empty branches, lack of self-communication, and productivity.

Intuitively:
- `allVarsBound`: recursion variables are bound
- `allCommsNonEmpty`: communications have at least one branch
- `noSelfComm`: no self-send
- `isProductive`: recursion must pass through a communication

Local types are well-formed when they are closed and contractive.

```lean
structure LocalTypeR.WellFormed (t : LocalTypeR) : Prop where
  closed : t.isClosed
  contractive : t.isContractive = true
```

This structure encodes the two core constraints for recursive local types.

Coinductive local types are well-formed when they are closed and observable.

```lean
def ClosedC (t : LocalTypeC) : Prop :=
  ∀ v, ¬ UnfoldsToVarC t v

structure WellFormedC (t : LocalTypeC) : Prop where
  closed : ClosedC t
  observable : ObservableC t
```

This structure defines the basic well-formedness conditions for coinductive local types.

## Progress Conditions (Lean)

Progress is not derived from well-formedness alone. The V2 proofs separate structural well-formedness from a progress predicate that asserts communication is reachable.

The progress predicate is:

```lean
inductive ReachesComm : GlobalType → Prop where
  | comm (sender receiver : String) (branches : List (Label × GlobalType)) :
      branches ≠ [] → ReachesComm (.comm sender receiver branches)
  | mu (t : String) (body : GlobalType) :
      ReachesComm (body.substitute t (.mu t body)) →
      ReachesComm (.mu t body)
```

This predicate states that a communication can be reached by unfolding recursion.

The associated progress theorem uses this predicate together with well-formedness and well-typedness.

```lean
def CanProgress (c : Configuration) : Prop :=
  ∃ c' act, ConfigStep c c' act

theorem deadlock_free (c : Configuration)
    (htyped : WellTypedConfig c)
    (hwf : c.globalType.wellFormed = true)
    (hcomm : ReachesComm c.globalType) :
    CanProgress c
```

Well-formedness ensures validity of recursion and structure. `ReachesComm` ensures progress is possible. Both are required to justify progress.

## Choreographic Programming

Choreographic programming builds on global types. It lets you write program logic from a global perspective. The choreography describes computations and data flow between participants. Endpoint projection generates local implementations for each participant.

```rust
choreography!(r#"
protocol Calculator =
  roles Alice, Bob
  Alice -> Bob : Value
  Bob -> Alice : Result
"#);
```

This example defines a two-role protocol in the DSL. The compiler projects this to per-role local code.

This choreography specifies the communication protocol. The system projects it into separate programs for Alice and Bob. Alice's program sends a value and receives a result. Bob's program receives a value and sends back a result.

Choreographic programming eliminates the need to manually coordinate distributed implementations. The global specification ensures all participants agree on the protocol. Type checking at the choreographic level prevents distributed system errors.

A good place to start learning more about choreographic programming is [Introduction to Choreographies](https://www.fabriziomontesi.com/files/m13_choreographies_behaviorally.pdf). For the integration with multiparty session types, see [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf).

## Algebraic Effects

Algebraic effects separate what a program does from how it does it. The effect algebra defines a set of abstract operations that a program can perform. Handlers provide concrete implementations of these operations. This separation allows the same program to run with different implementations.

In Telltale, communication operations are effects. Sending and receiving messages are abstract operations. Different handlers implement these operations differently. An in-memory handler passes messages through local channels. A network handler sends messages over TCP or WebSocket connections.

```rust
let program = Program::new()
    .send(Role::Bob, Message::Hello)
    .recv::<Message>(Role::Bob)
    .end();

// Same program, different handlers
interpret(&mut in_memory_handler, &mut endpoint, program).await;
interpret(&mut network_handler, &mut endpoint, program).await;
```

The program specifies what messages to send and receive. The handler determines how this happens. This design enables testing with local handlers and deployment with network handlers. The protocol logic remains unchanged.

## Integration in Telltale

Telltale combines these concepts into a practical system. Choreographies define distributed protocols globally. The type system ensures protocol safety through MPST. Effect handlers provide flexible execution strategies. The choreography macro parses protocol definitions, generates role and message types automatically, and creates session types for each participant through projection.

The effect system decouples protocol logic from transport mechanisms. Handlers interpret send and receive operations. Middleware can add logging, retry logic, or fault injection. The same choreography works across different deployment scenarios. Content addressing assigns cryptographic identities to all protocol artifacts, enabling memoization and structural sharing.

A bytecode VM provides an alternative execution model. The VM compiles local types to bytecode instructions and manages scheduling, buffers, and session lifecycle. The concurrency parameter N controls how many coroutines advance per scheduling round. Per-session traces are invariant over N, enabling testing at high concurrency and deployment at lower concurrency.

Topology configuration separates deployment concerns from protocol logic. Resource heaps provide explicit state management with nullifier-based consumption tracking. This integration provides both safety and flexibility through a type system that prevents protocol errors and an effect system that allows diverse implementations.

## Further Reading

See [Architecture](02_architecture.md) for system design details. See [Choreographic DSL](04_choreographic_dsl.md) for the choreography language. See [Effect Handlers](08_effect_handlers.md) for the handler system.

See [Content Addressing](16_content_addressing.md) for cryptographic protocol identities. See [Topology](20_topology.md) for deployment configuration. See [Resource Heap](17_resource_heap.md) for explicit state management. See [VM Architecture](11_vm_architecture.md) for the bytecode execution model.
