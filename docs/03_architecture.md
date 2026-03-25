# Architecture

## Overview

Telltale compiles global protocol specifications into local session types for each participant. The system is organized as a conservation system over protocol semantics. All protocol-critical behavior reduces to six conserved properties: evidence, authority, identity, commitment, structure, and premise. See [Conservation Framework](37_conservation_framework.md) for the full design philosophy.

The architecture has three compile-time stages and two runtime paths:

1. DSL and parsing (choreographic syntax to AST)
2. Projection (global protocol to local types)
3. Code generation (local types to Rust code and effect programs)
4. Effect handler execution (async interpreter with pluggable transports)
5. Protocol-machine execution and simulation (protocol machine with scheduler and deterministic middleware)

### Runtime Layering

The execution architecture separates three concerns. The protocol machine is a deterministic small-step reducer that is the sole authority over semantic progression. The guest runtime wraps the protocol machine with typed effect interfaces and concrete handlers. The host runtime is the surrounding system that provides time, storage, network, and process lifecycle.

Typed effect interfaces form the operational vocabulary between the protocol machine and the world. Internal handlers realize scheduling, dispatch, replay, and simulation. External handlers realize storage, network, and domain-specific host integrations. Both handler domains interpret the same typed interfaces.

## Component Diagram

```mermaid
graph TB
    subgraph Input["Developer Input (Compile-Time)"]
        DSL["Choreography DSL<br/>Global Protocol Specification"]
    end

    subgraph Layer1["Layer 1: Parsing & AST Construction"]
        Parser["Parser<br/>(Pest Grammar)"]
        AST["AST<br/>Choreography + Protocol Tree"]
    end

    subgraph Layer2["Layer 2: Projection"]
        Proj["Projection Algorithm"]
        LT["Local Types<br/>(Per Role)"]
    end

    subgraph Layer3["Layer 3: Code Generation"]
        CodeGen["Code Generator"]
        Session["Generated Session Types"]
        Effects["Generated Effect Programs"]
    end

    subgraph Layer4["Layer 4: Effect Runtime"]
        Handler["Effect Handler<br/>(InMemory / Telltale)"]
        Transport["Transport Layer<br/>(Channels / Network)"]
        Exec["Running Protocol"]
    end

    subgraph Layer5["Layer 5: Protocol Machine + Simulation"]
        VMCompiler["Protocol-Machine Compiler<br/>(LocalTypeR → Bytecode)"]
        protocol machine["Protocol Machine"]
        Scheduler["Scheduler<br/>(Policy-Based)"]
        Sessions["Session Store"]
        Buffers["Bounded Buffers"]
        Middleware["Simulator Middleware<br/>(Latency / Faults / Properties / Checkpoints)"]
    end

    DSL --> Parser
    Parser --> AST
    AST --> Proj
    Proj --> LT
    LT --> CodeGen
    CodeGen --> Session
    CodeGen --> Effects
    Session --> Handler
    Effects --> Handler
    Handler --> Transport
    Transport --> Exec
    LT --> VMCompiler
    VMCompiler --> protocol machine
    protocol machine --> Scheduler
    Scheduler --> Sessions
    Sessions --> Buffers
    Middleware --> protocol machine
```

This diagram summarizes the compile time flow from DSL input to runtime execution. It also highlights the boundary between compilation, the guest runtime, and host-runtime effect handling.

## Core Components

### AST Module

The AST module is located in `rust/choreography/src/ast/`. It represents choreographies as data structures.

The main type is `Choreography`.

```rust
pub struct Choreography {
    pub name: Ident,
    pub namespace: Option<String>,
    pub roles: Vec<Role>,
    pub protocol: Protocol,
    pub attrs: HashMap<String, String>,
}
```

This struct holds the protocol name and optional namespace. It contains participating roles and the protocol tree. Metadata attributes are stored in the `attrs` field.

The `Protocol` enum defines all protocol actions.

```rust
pub enum Protocol {
    Send {
        from: Role,
        to: Role,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: Annotations,
        from_annotations: Annotations,
        to_annotations: Annotations,
    },
    Broadcast {
        from: Role,
        to_all: NonEmptyVec<Role>,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: Annotations,
        from_annotations: Annotations,
    },
    Choice {
        role: Role,
        branches: NonEmptyVec<Branch>,
        annotations: Annotations,
    },
    Let {
        name: String,
        expr: AuthorityExpr,
        linear: bool,
        continuation: Box<Protocol>,
    },
    Case {
        expr: AuthorityExpr,
        branches: NonEmptyVec<CaseBranch>,
    },
    Timeout {
        role: Role,
        duration_ms: u64,
        body: Box<Protocol>,
        on_timeout: Box<Protocol>,
        on_cancel: Option<Box<Protocol>>,
    },
    Loop { condition: Option<Condition>, body: Box<Protocol> },
    Parallel { protocols: NonEmptyVec<Protocol> },
    Rec { label: Ident, body: Box<Protocol> },
    Var(Ident),
    Publish {
        event: String,
        arg: Option<String>,
        continuation: Box<Protocol>,
    },
    Handoff {
        operation: String,
        target: Role,
        receipt: String,
        continuation: Box<Protocol>,
    },
    DependentWork {
        name: String,
        arg: Option<String>,
        required_for: String,
        continuation: Box<Protocol>,
    },
    Extension {
        extension: Box<dyn ProtocolExtension>,
        continuation: Box<Protocol>,
        annotations: Annotations,
    },
    End,
}
```

`Protocol` is a recursive tree structure. It includes support for annotations at multiple levels. Broadcasts, choices, parallel composition, recursive definitions, authority bindings, case matching, and timeouts are supported. Semantic publication, ownership handoff, and dependent work declarations support runtime lifecycle coordination.

`NonEmptyVec` is used where the DSL enforces at least one branch.

### Parser Module

The parser module is located in `rust/choreography/src/compiler/parser/`. It converts DSL text into AST using the Pest parser generator.

The parser validates role declarations and builds the protocol tree from the input text. It runs a layout preprocessor before the grammar parse. This enables layout-sensitive syntax with `->` message arrows, `=>` branch arrows, `choice Role at` branches with leading `|`, and `par` blocks.

Two entry points are available.

```rust
pub fn parse_choreography_str(input: &str) -> Result<Choreography, ParseError>
pub fn parse_choreography_file(path: &Path) -> Result<Choreography, ParseError>
```

The parser performs syntactic validation and basic semantic checks. The file-based
entry point expects the canonical `.tell` source extension.

### Projection Module

The projection module is located in `rust/choreography/src/compiler/projection.rs`. Projection transforms a global protocol into a local view for each role.

The algorithm determines what each participant should do.

```rust
pub fn project(choreography: &Choreography, role: &Role) -> Result<LocalType, ProjectionError>
```

Projection handles merging parallel branches. It also detects conflicts between branches.

### Code Generation Module

The codegen module is located in `rust/choreography/src/compiler/codegen/`. It converts local types into Rust session types and effect programs.

The generator creates compile-time type-safe protocol implementations.

```rust
pub fn generate_session_type(role: &Role, local_type: &LocalType, protocol_name: &str) -> TokenStream
pub fn generate_choreography_code(name: &str, roles: &[Role], local_types: &[(Role, LocalType)]) -> TokenStream
pub fn generate_choreography_code_with_extensions(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
    extensions: &[Box<dyn ProtocolExtension>],
) -> TokenStream
pub fn generate_choreography_code_with_dynamic_roles(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
) -> TokenStream
pub fn generate_choreography_code_with_namespacing(
    choreo: &Choreography,
    local_types: &[(Role, LocalType)],
) -> TokenStream
pub fn generate_choreography_code_with_annotations(
    name: &str,
    roles: &[Role],
    local_types: &[(Role, LocalType)],
    choreo: &Choreography,
) -> TokenStream
pub fn generate_choreography_code_with_topology(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
    inline_topologies: &[InlineTopology],
) -> TokenStream
pub fn generate_dynamic_role_support(choreography: &Choreography) -> TokenStream
pub fn generate_role_implementations(
    role: &Role,
    local_type: &LocalType,
    protocol_name: &str,
) -> TokenStream
pub fn generate_topology_integration(
    choreography: &Choreography,
    inline_topologies: &[InlineTopology],
) -> TokenStream
pub fn generate_helpers(name: &str, messages: &[MessageType]) -> TokenStream
```

The generator creates session types and role structs. It supports dynamic roles including parameterized roles and runtime management.

### Effect System

The effect system is located in `rust/choreography/src/effects/`. It decouples protocol logic from transport.

Protocols are represented as effect programs. Handlers interpret these programs.

```rust
pub trait ChoreoHandler: Send {
    type Role: RoleId;
    type Endpoint: Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> ChoreoResult<()>;
    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> ChoreoResult<M>;
    async fn choose(
        &mut self, ep: &mut Self::Endpoint, who: Self::Role, label: <Self::Role as RoleId>::Label
    ) -> ChoreoResult<()>;
    async fn offer(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> ChoreoResult<<Self::Role as RoleId>::Label>;

    async fn with_timeout<F, T>(
        &mut self, ep: &mut Self::Endpoint, at: Self::Role, dur: Duration, body: F
    ) -> ChoreoResult<T>
    where
        F: Future<Output = ChoreoResult<T>> + Send;
}
```

Handlers implement this trait to provide different execution strategies. This async handler is distinct from the synchronous `telltale_machine::model::effects::EffectHandler` used by the protocol machine.

Use [Effect Handlers and Session Types](11_effect_session_bridge.md) for protocol-machine integration guidance.

### Protocol-Machine Execution Layer

The protocol machine provides a bytecode execution model for local types. The `telltale-machine` crate compiles `LocalTypeR` into bytecode and executes it with a policy-based scheduler. The `telltale-simulator` crate wraps guest runtimes around that protocol machine with deterministic middleware for latency, faults, property monitoring, and checkpointing.

The protocol machine maintains session state with bounded message buffers. Each coroutine references its assigned program by ID. The scheduler policies are observationally equivalent per the Lean model. Nested protocol machines can be hosted inside a coroutine for hierarchical simulation.

At the embedding boundary, the protocol machine distinguishes current host ownership from protocol typing and capability admission. Production host integrations use `load_choreography_owned(...)` and `OwnedSession` for explicit session-local authority after open. Guest runtimes embed the protocol machine inside a host runtime with explicit external handlers.

Delegation and reconfiguration paths emit explicit receipts and audit records. See [Protocol Machine Architecture](12_protocol_machine_architecture.md) for details on the underlying bytecode protocol-machine architecture.

## Data Flow

This section demonstrates the transformation of a choreography through each layer.

Input choreography:
```tell
Alice
  -> Bob : Request of api.Request
Bob
  -> Alice : Response of api.Response
```

The choreography specifies a request-response pattern.

After parsing, the AST contains a nested send structure.

```rust
Protocol::Send {
    from: Alice, to: Bob, message: Request,
    continuation: Protocol::Send {
        from: Bob, to: Alice, message: Response,
        continuation: Protocol::End
    }
}
```

This represents the global protocol tree.

After projection for Alice, the local type shows send then receive.

```rust
LocalType::Send {
    to: Bob, message: Request,
    continuation: LocalType::Receive {
        from: Bob, message: Response,
        continuation: LocalType::End
    }
}
```

Alice sends a request and waits for a response.

After projection for Bob, the local type shows receive then send.

```rust
LocalType::Receive {
    from: Alice, message: Request,
    continuation: LocalType::Send {
        to: Alice, message: Response,
        continuation: LocalType::End
    }
}
```

Bob waits for a request and sends a response.

After code generation for Alice, a session type is created.

```rust
type Alice_Protocol = Send<Bob, Request, Receive<Bob, Response, End>>;
```

This session type enforces the protocol at compile time.

At runtime, the protocol-machine and generated effect boundary drive actual
communication. The older choreography-layer effect-program builder remains an
internal implementation technique, not the canonical public architecture story.

## Design Decisions

### Why Conservation

Telltale treats protocol semantics as conserved quantities rather than emergent properties. Every runtime phenomenon reduces to the conservation framework. Async execution reduces to commitment lifecycle. Race conditions reduce to authority violations. Retry logic reduces to identity and commitment. See the full reduction table in [Conservation Framework](37_conservation_framework.md).

This design eliminates classes of bugs by construction. Hidden concurrency, authority ambiguity, silent failure, late result races, and unbounded waiting all map to violations of specific conserved properties. The erasure principle removes everything that is not part of the conserved system from the programming model.

### Why Choreographic Programming

Choreographies specify the global protocol once and projection generates local code for each role. This realizes structure conservation: the compositional structure of the protocol is defined entirely by its type, and no runtime behavior can alter the protocol shape.

### Why Effect Handlers

Effect handlers are the typed operational vocabulary between the protocol machine and the world. They realize commitment conservation: every effect is a tracked commitment that must resolve to a terminal class. Internal handlers realize scheduling, dispatch, and replay. External handlers realize storage, network, and domain-specific integrations. See [Choreography Effect Handlers](09_effect_handlers.md) for the async surface and [Effect Handlers and Session Types](11_effect_session_bridge.md) for the protocol-machine boundary.

### Why Session Types

Session types provide compile-time guarantees about protocol compliance. The Rust type system enforces that each role follows their protocol correctly. Type checking prevents message ordering and payload-shape violations at compile time. Global deadlock claims remain assumption-scoped in the theory results.

### Platform Abstraction

The runtime module provides platform-specific async primitives. Native targets use tokio. WASM uses `wasm-bindgen-futures`. The same code runs on servers and in browsers.

## Extension Points

### Custom Handlers

Implement `ChoreoHandler` for choreography-layer transports. Implement `EffectHandler` for protocol-machine host integration. See [Choreography Effect Handlers](09_effect_handlers.md) and [Effect Handlers and Session Types](11_effect_session_bridge.md) for details.

### Middleware

Wrap handlers with middleware for cross-cutting concerns. Logging, metrics, and retry logic can be added as middleware. Multiple middleware layers can be stacked on a single handler.

## Implementation Organization

This page focuses on conceptual architecture: compilation stages, runtime execution paths, and why those boundaries exist.

For concrete workspace layout, crate dependency edges, per-crate responsibilities, and Lean constructor correspondence, see [Code Organization](04_code_organization.md).
