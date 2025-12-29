# Architecture

## Overview

Rumpsteak implements choreographic programming for Rust. The system compiles global protocol specifications into local session types for each participant.

The architecture has four main layers:

1. DSL and parsing (choreographic syntax to AST)
2. Projection (global protocol to local types)
3. Code generation (local types to Rust code)
4. Effect system (protocol execution with pluggable transports)

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

    subgraph Layer4["Layer 4: Runtime Execution"]
        Handler["Effect Handler<br/>(InMemory / Rumpsteak)"]
        Transport["Transport Layer<br/>(Channels / Network)"]
        Exec["Running Protocol"]
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
```

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

The `Protocol` enum defines all possible protocol actions.

```rust
pub enum Protocol {
    Send {
        from: Role,
        to: Role,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
        to_annotations: HashMap<String, String>,
    },
    Broadcast {
        from: Role,
        to_all: Vec<Role>,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
    },
    Choice {
        role: Role,
        branches: Vec<Branch>,
        annotations: HashMap<String, String>,
    },
    Loop { condition: Option<Condition>, body: Box<Protocol> },
    Parallel { protocols: Vec<Protocol> },
    Rec { label: Ident, body: Box<Protocol> },
    Var(Ident),
    End,
}
```

Protocol is a recursive tree structure. It includes support for annotations at multiple levels. Broadcasts and recursive definitions are supported.

### Parser Module

The parser module is located in `rust/choreography/src/compiler/parser.rs`. It converts DSL text into AST using the Pest parser generator.

The parser validates role declarations. It builds the protocol tree from the input text.

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

The codegen module is located in `rust/choreography/src/compiler/codegen.rs`. It converts local types into Rust session types and effect programs.

The generator creates compile-time type-safe protocol implementations.

```rust
pub fn generate_session_type(role: &Role, local_type: &LocalType, protocol_name: &str) -> TokenStream
pub fn generate_choreography_code(name: &str, roles: &[Role], local_types: &[(Role, LocalType)]) -> TokenStream
pub fn generate_choreography_code_with_dynamic_roles(choreography: &Choreography, local_types: &[(Role, LocalType)]) -> TokenStream
pub fn generate_dynamic_role_support(choreography: &Choreography) -> TokenStream
pub fn generate_effects_protocol(choreography: &Choreography) -> TokenStream
```

The generator creates session types and role structs. It supports dynamic roles including parameterized roles and runtime management.

### Effect System

The effect system is located in `rust/choreography/src/effects/`. It decouples protocol logic from transport.

Protocols are represented as effect programs. Handlers interpret these programs.

```rust
pub trait ChoreoHandler {
    type Role: RoleId;
    type Endpoint;

    async fn send<M>(&mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M) -> Result<()>;
    async fn recv<M>(&mut self, ep: &mut Self::Endpoint, from: Self::Role) -> Result<M>;
    async fn choose(&mut self, ep: &mut Self::Endpoint, who: Self::Role, label: Label) -> Result<()>;
    async fn offer(&mut self, ep: &mut Self::Endpoint, from: Self::Role) -> Result<Label>;
}
```

Handlers implement this trait to provide different execution strategies.

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

Type checking prevents common distributed systems errors. Deadlocks and protocol violations are caught at compile time.

### Platform Abstraction

The runtime module provides platform-specific async primitives. Native targets use tokio. WASM uses wasm-bindgen-futures.

This abstraction makes the core library portable. The same code runs on servers and in browsers.

## Extension Points

### Custom Handlers

Implement `ChoreoHandler` to add new transport mechanisms. See [Effect Handlers](05_effect_handlers.md) for details.

### Middleware

Wrap handlers with middleware for cross-cutting concerns. Logging, metrics, and retry logic can be added as middleware. Middleware composes naturally.

### Custom Projections

The projection algorithm can be extended for domain-specific optimizations. Override default projection rules by implementing custom projection functions.

### Code Generation Backends

Add new code generation backends to target different session type libraries. The AST and LocalType representations are language-agnostic. Backends for other languages can be added.

## Workspace Organization

Rumpsteak-Aura is organized as a Cargo workspace with multiple crates. All Rust code is located in the `rust/` directory.

```
rumpsteak-aura/
├── rust/                   All Rust crates
│   ├── src/                Core session types library (rumpsteak-aura crate)
│   │   ├── lib.rs          Session type primitives, channels, roles
│   │   ├── channel.rs      Async channel implementations
│   │   └── serialize.rs    Serialization support
│   ├── choreography/       Choreographic programming extensions
│   │   ├── src/
│   │   │   ├── ast/        AST definitions
│   │   │   ├── compiler/   Parser, projection, codegen
│   │   │   ├── effects/    Effect system
│   │   │   │   ├── handlers/   Handler implementations
│   │   │   │   └── middleware/ Middleware implementations
│   │   │   └── runtime.rs  Platform abstraction
│   │   ├── tests/          Integration tests
│   │   └── examples/       Example protocols
│   ├── types/              Core types (GlobalType, LocalTypeR, Label)
│   ├── theory/             Session type algorithms
│   ├── codegen/            Rust code generation
│   ├── lean-bridge/        Lean interop and validation
│   ├── fsm/                Finite state machine support
│   ├── macros/             Procedural macros
│   ├── lean-exporter/      Lean export utilities
│   └── caching/            HTTP cache case study
├── lean/                   Lean 4 verification code
├── examples/               Additional examples
│   └── wasm-ping-pong/     WASM browser example
└── docs/                   Documentation
```

### Crate Responsibilities

The `rumpsteak-aura` crate is in `rust/src/`. It provides foundation session types for type-safe asynchronous communication. This is the base dependency for all other crates.

The `rumpsteak-aura-choreography` crate provides the high-level choreographic programming layer. It includes the DSL parser, automatic projection, effect handlers, and runtime support. It builds on top of rumpsteak-aura.

The `rumpsteak-aura-fsm` crate provides finite state machine support for session types. It includes DOT parsing and subtyping verification. This is an optional dependency for advanced use cases.

The `rumpsteak-aura-macros` crate contains procedural macros. These macros are used by both rumpsteak-aura and rumpsteak-aura-choreography.

The `caching` crate is an example application. It demonstrates real-world usage with Redis and HTTP caching.
