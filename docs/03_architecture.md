# Architecture

## Overview

Telltale implements choreographic programming for Rust. The system compiles global protocol specifications into local session types for each participant.

The architecture has three compile-time stages and two runtime paths:

1. DSL and parsing (choreographic syntax to AST)
2. Projection (global protocol to local types)
3. Code generation (local types to Rust code and effect programs)
4. Effect handler execution (async interpreter with pluggable transports)
5. VM execution and simulation (bytecode VM with scheduler and deterministic middleware)

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

    subgraph Layer5["Layer 5: VM + Simulation"]
        VMCompiler["VM Compiler<br/>(LocalTypeR → Bytecode)"]
        VM["Bytecode VM"]
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
    VMCompiler --> VM
    VM --> Scheduler
    Scheduler --> Sessions
    Sessions --> Buffers
    Middleware --> VM
```

This diagram summarizes the compile time flow from DSL input to runtime execution. It also highlights the boundary between compilation and effect handler execution.

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

This struct holds the protocol name and optional namespace. It contains participating roles and the protocol tree. Metadata attributes are stored in the attrs field.

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
    Loop { condition: Option<Condition>, body: Box<Protocol> },
    Parallel { protocols: NonEmptyVec<Protocol> },
    Rec { label: Ident, body: Box<Protocol> },
    Var(Ident),
    Extension {
        extension: Box<dyn ProtocolExtension>,
        continuation: Box<Protocol>,
        annotations: Annotations,
    },
    End,
}
```

Protocol is a recursive tree structure. It includes support for annotations at multiple levels. Broadcasts, choices, parallel composition, and recursive definitions are supported. `NonEmptyVec` is used where the DSL enforces at least one branch.

### Parser Module

The parser module is located in `rust/choreography/src/compiler/parser/`. It converts DSL text into AST using the Pest parser generator.

The parser validates role declarations. It builds the protocol tree from the input text.
It runs a layout preprocessor before the grammar parse. This enables layout sensitive syntax with explicit braces for empty blocks.

Two entry points are available.

```rust
pub fn parse_choreography_str(input: &str) -> Result<Choreography, ParseError>
pub fn parse_choreography_file(path: &Path) -> Result<Choreography, ParseError>
```

The parser performs syntactic validation and basic semantic checks.

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
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, label: <Self::Role as RoleId>::Label
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

Handlers implement this trait to provide different execution strategies. This async handler is distinct from the synchronous `telltale_vm::effect::EffectHandler` used by the VM.
Use [Effect Handlers and Session Types](11_effect_session_bridge.md) for VM integration guidance.

### VM Execution Layer

The VM provides a bytecode execution model for local types. The `telltale-vm` crate compiles `LocalTypeR` into bytecode and executes it with a policy-based scheduler. `telltale-simulator` wraps the VM with deterministic middleware for latency, faults, property monitoring, and checkpointing.

The VM maintains session state with bounded message buffers. Each coroutine references its assigned program by ID. The scheduler policies are observationally equivalent per the Lean model. Nested VMs can be hosted inside a coroutine for hierarchical simulation.

See [VM Architecture](12_vm_architecture.md) for details on the bytecode VM architecture.

## Data Flow

This section demonstrates the transformation of a choreography through each layer.

Input choreography:
```rust
Alice -> Bob: Request
Bob -> Alice: Response
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

At runtime, effect programs execute using handlers.

```rust
Program::new()
    .send(Bob, Request)
    .recv::<Response>(Bob)
    .end()
```

The handler interprets this program into actual communication.

## Design Decisions

### Why Choreographic Programming

Creating distributed programs typically requires writing separate implementations for each participant. This approach is error-prone and hard to verify.

Choreographies specify the global protocol once. Automatic projection generates local code for each role. This approach prevents protocol mismatches and simplifies reasoning about distributed systems.

### Why Effect Handlers

Separating protocol logic from transport enables testing and composition. The same protocol can run with different handlers without code changes.

Effect handlers provide runtime flexibility. Test handlers use in-memory communication. Production handlers use network transports.

### Why Session Types

Session types provide compile-time guarantees about protocol compliance. The Rust type system enforces that each role follows their protocol correctly.

Type checking prevents common distributed systems errors. Message ordering and payload-shape violations are caught at compile time. Global deadlock claims remain assumption-scoped in the theory results.

### Platform Abstraction

The runtime module provides platform-specific async primitives. Native targets use tokio. WASM uses wasm-bindgen-futures.

This abstraction makes the core library portable. The same code runs on servers and in browsers.

## Extension Points

### Custom Handlers

Implement `ChoreoHandler` to add new transport mechanisms. See [Choreography Effect Handlers](09_effect_handlers.md) for details.

### Middleware

Wrap handlers with middleware for cross-cutting concerns. Logging, metrics, and retry logic can be added as middleware. Middleware composes naturally.

### Custom Projections

The projection algorithm can be extended for domain-specific optimizations. Override default projection rules by implementing custom projection functions.

### Code Generation Backends

Add new code generation backends to target different session type libraries. The AST and LocalType representations are language-agnostic. Backends for other languages can be added.

## Implementation Organization

This page focuses on conceptual architecture: compilation stages, runtime execution paths, and why those boundaries exist.

For concrete workspace layout, crate dependency edges, per-crate responsibilities, and Lean constructor correspondence, see [Code Organization](04_code_organization.md).
