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

Implement `ChoreoHandler` to add new transport mechanisms. See [Effect Handlers](06_effect_handlers.md) for details.

### Middleware

Wrap handlers with middleware for cross-cutting concerns. Logging, metrics, and retry logic can be added as middleware. Middleware composes naturally.

### Custom Projections

The projection algorithm can be extended for domain-specific optimizations. Override default projection rules by implementing custom projection functions.

### Code Generation Backends

Add new code generation backends to target different session type libraries. The AST and LocalType representations are language-agnostic. Backends for other languages can be added.

## Workspace Organization

Rumpsteak-Aura is organized as a Cargo workspace with multiple crates. All Rust code is located in the `rust/` directory. The crate structure mirrors the Lean formalization.

```
rumpsteak-aura/
├── rust/                   All Rust crates
│   ├── src/                Facade crate (rumpsteak-aura)
│   ├── types/              Core types (rumpsteak-types)
│   │   └── src/
│   │       ├── global.rs   GlobalType (matches Lean)
│   │       ├── local.rs    LocalTypeR (matches Lean)
│   │       ├── label.rs    Label, PayloadSort
│   │       └── action.rs   Action, LocalAction
│   ├── theory/             Session type algorithms (rumpsteak-theory)
│   │   └── src/
│   │       ├── projection.rs   Global to local projection
│   │       ├── merge.rs        Branch merging
│   │       ├── subtyping/      Sync and async subtyping
│   │       ├── duality.rs      Dual type computation
│   │       └── bounded.rs      Bounded recursion
│   ├── choreography/       DSL and effects (rumpsteak-aura-choreography)
│   │   └── src/
│   │       ├── ast/        Extended AST definitions
│   │       ├── compiler/   Parser, projection, codegen
│   │       ├── effects/    Effect handlers and middleware
│   │       └── runtime/    Platform abstraction
│   ├── lean-bridge/        Lean validation (rumpsteak-lean-bridge)
│   │   └── src/
│   │       ├── export.rs   Rust to JSON export
│   │       ├── import.rs   JSON to Rust import
│   │       └── runner.rs   Lean binary invocation
│   ├── fsm/                FSM visualization (rumpsteak-aura-fsm)
│   └── macros/             Procedural macros (rumpsteak-aura-macros)
├── lean/                   Lean 4 verification code
├── examples/               Example protocols
└── docs/                   Documentation
```

### Crate Responsibilities

The `rumpsteak-types` crate contains core type definitions. It provides `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`. These types match the Lean definitions exactly. This crate has no internal dependencies.

The `rumpsteak-theory` crate contains pure algorithms. It provides projection, merge, duality, subtyping, and well-formedness checks. This crate depends only on `rumpsteak-types`.

The `rumpsteak-aura-choreography` crate is the choreographic programming layer. It includes the DSL parser, effect handlers, code generation, and runtime support.

The `rumpsteak-lean-bridge` crate provides Lean integration. It exports Rust types to JSON and imports JSON from Lean. It includes a runner for invoking the Lean verification binary.

The `rumpsteak-aura-fsm` crate provides finite state machine support. Use it for visualization with DOT and Mermaid formats. FSM-based subtyping is also available.

The `rumpsteak-aura` crate is the main facade. It re-exports types from other crates with feature flags. Most users import from this crate.
