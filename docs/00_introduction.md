# Background

This document provides an introduction to the theory behind Rumpsteak-Aura. It covers multiparty session types, choreographic programming, and algebraic effects. Understanding these concepts helps explain how the system achieves type-safe distributed programming.

## Session Types

Session types encode communication protocols as types in the type system. They specify the sequence and structure of messages exchanged between processes. A session type acts as a contract that all communication must follow. The compiler verifies that implementations adhere to this contract.

Traditional type systems ensure data safety. They prevent type errors like passing a string where an integer is expected. Session types extend this to communication safety. They prevent protocol errors like sending when you should receive or terminating when more messages are expected.

A session type describes a communication channel from one endpoint's perspective. The type `!String.?Int.end` means send a string, then receive an integer, then close the channel. The dual type `?String.!Int.end` means receive a string, then send an integer, then close. These types are complementary. They ensure the endpoints coordinate correctly.

## Multiparty Session Types (MPST)

Multiparty session types extend binary session types to protocols with three or more participants. While session types handle point-to-point channels, MPST handles protocols where multiple parties interact. Each participant can communicate with multiple others. The type system ensures all interactions remain synchronized.

MPST introduces new challenges beyond binary sessions. Participants must agree on the overall protocol flow. Messages between two participants affect what other participants can do next. The type system must track these dependencies to prevent global deadlocks. Consider a three-party payment protocol where a customer requests a quote from a merchant, the merchant checks with a bank, and the bank approves or denies.

In MPST, each participant has a local view that includes all their partners. The customer's type shows communication with both merchant and bank. The system ensures all three views are compatible. For a more in-depth discussion of MPST theory, see [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf). Advanced optimizations through asynchronous subtyping are covered in [Precise Subtyping for Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf). And [Mechanised Subject Reduction for Multiparty Asynchronous Session Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.31) includes a mechanized Coq proof that adds a well-typed condition that fixes the original MPST formulation by Honda et al. The type theory in this crate draws from this revised forumulation.

## Global Types and Projection

Global types describe protocols from a neutral, third-party perspective. They specify all interactions between all participants. Local types describe the protocol from one participant's viewpoint. Projection transforms global types into local types for each participant.

```
G = Alice -> Bob: Int.
    Bob -> Alice: {Sum: Int, Product: Int}
```

This global type projects to different local types. Alice gets `Bob!Int.Bob&{Sum: Int, Product: Int}`. Bob gets `Alice?Int.Alice⊕{Sum: Int, Product: Int}`. Each participant sees only their part of the protocol.

The projection algorithm ensures the local types are compatible. If projection succeeds, the protocol is guaranteed to be deadlock-free. All participants will complete the protocol without communication errors.

## Choreographic Programming

Choreographic programming takes the global types concept further. Instead of just types, you write actual program logic from a global perspective. The choreography describes computations and data flow between participants. Endpoint projection generates local implementations for each participant.

```rust
choreography!(r#"
protocol Calculator =
  roles Alice, Bob
  Alice -> Bob : Value
  Bob -> Alice : Result
"#);
```

This choreography specifies the communication protocol. The system projects it into separate programs for Alice and Bob. Alice's program sends a value and receives a result. Bob's program receives a value and sends back a result.

Choreographic programming eliminates the need to manually coordinate distributed implementations. The global specification ensures all participants agree on the protocol. Type checking at the choreographic level prevents distributed system errors.

A good place to start learning more about choreographic programming is [Introduction to Choreographies](https://www.fabriziomontesi.com/files/m13_choreographies_behaviorally.pdf). For the integration with multiparty session types, see [Applied Choreographies](https://arxiv.org/pdf/2209.01886.pdf).

## Algebraic Effects

Algebraic effects separate what a program does from how it does it. The effect algebra defines a set of abstract operations that a program can perform. Handlers provide concrete implementations of these operations. This separation allows the same program to run with different implementations.

In Rumpsteak-Aura, communication operations are effects. Sending and receiving messages are abstract operations. Different handlers implement these operations differently. An in-memory handler passes messages through local channels. A network handler sends messages over TCP or WebSocket connections.

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

## Integration in Rumpsteak-Aura

Rumpsteak-Aura combines these concepts into a practical system. Choreographies define distributed protocols globally. The type system ensures protocol safety through MPST. Effect handlers provide flexible execution strategies. The choreography macro parses protocol definitions, generates role and message types automatically, and creates session types for each participant through projection.

The effect system decouples protocol logic from transport mechanisms. Handlers interpret send and receive operations. Middleware can add logging, retry logic, or fault injection. The same choreography works across different deployment scenarios. Content addressing assigns cryptographic identities to all protocol artifacts, enabling memoization and structural sharing.

Topology configuration separates deployment concerns from protocol logic. Resource heaps provide explicit state management with nullifier-based consumption tracking. This integration provides both safety and flexibility through a type system that prevents protocol errors and an effect system that allows diverse implementations.

## Further Reading

See [Architecture](02_architecture.md) for system design details. See [Choreographic DSL](03_choreographic_dsl.md) for the choreography language. See [Effect Handlers](06_effect_handlers.md) for the handler system.

See [Content Addressing](05_content_addressing.md) for cryptographic protocol identities. See [Topology](08_topology.md) for deployment configuration. See [Resource Heap](09_resource_heap.md) for explicit state management.
