# Getting Started

## Installation

Add Telltale to your project dependencies.

```toml
[dependencies]
telltale = "10.0.0"
telltale-runtime = "10.0.0"
```

This adds the facade crate and the choreographic programming layer. Pinning versions keeps builds reproducible.

### Which Crate Should You Use

| If you need | Use |
|-------------|-----|
| Core session types plus facade APIs | `telltale` |
| Choreography DSL, parser, and effect handlers | `telltale-runtime` |
| Projection, merge, and subtyping algorithms | `telltale-theory` |
| Protocol-machine execution with schedulers | `telltale-machine` |
| Deterministic simulation and scenario middleware | `telltale-simulator` |
| Lean JSON import, export, and validation tools | `telltale-bridge` |
| Production transport adapters | `telltale-transport` |

This table is a quick entry point for crate selection. Use it before reading the full crate descriptions.

### Understanding the Crates

Telltale is organized as a Cargo workspace with several crates. The layout tracks the Lean formalization for shared protocol concepts.

The `telltale-types` crate contains core type definitions such as `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`. Lean includes a `delegate` constructor that is not yet exposed in Rust.

The `telltale-theory` crate contains pure algorithms for projection, merge, subtyping, and well-formedness checks. The `telltale-runtime` crate is the choreographic programming layer that provides the DSL parser, effect handlers, and code generation.

The `telltale-machine` crate provides the protocol machine and guest-runtime execution surfaces. The `telltale-simulator` crate wraps the protocol machine with deterministic middleware for testing. The `telltale-bridge` crate enables cross-validation with Lean through JSON import and export functions. The `telltale-transport` crate provides production-oriented transport adapters that integrate with choreography handlers.

The `telltale` crate is the main facade that re-exports types from other crates with feature flags. Most users need both `telltale` and `telltale-runtime` for session types and the high-level DSL.

### Feature Flags

The workspace provides granular feature flags to control dependencies and functionality.

#### Root Crate (`telltale`)

| Feature | Default | Description |
|---------|---------|-------------|
| `test-utils` | no | Testing utilities (random generation) |
| `wasm` | no | WebAssembly support |
| `theory` | no | Session type algorithms via `telltale-theory` |
| `theory-async-subtyping` | no | POPL 2021 asynchronous subtyping algorithm |
| `theory-bounded` | no | Bounded recursion strategies |
| `full` | no | Enable all optional features |

#### Theory Crate (`telltale-theory`)

| Feature | Default | Description |
|---------|---------|-------------|
| `projection` | yes | Global to local type projection |
| `duality` | yes | Dual type computation |
| `merge` | yes | Local type merging |
| `well-formedness` | yes | Type validation |
| `bounded` | yes | Bounded recursion strategies |
| `async-subtyping` | yes | POPL 2021 asynchronous subtyping |
| `sync-subtyping` | yes | Synchronous subtyping |
| `semantics` | yes | Async step semantics from ECOOP 2025 |
| `coherence` | yes | Coherence predicates |
| `full` | no | Enable all optional features |

#### Choreography Crate (`telltale-runtime`)

| Feature | Default | Description |
|---------|---------|-------------|
| `test-utils` | no | Testing utilities (random, fault injection) |
| `wasm` | no | WebAssembly support |
| `native-cli` | no | Build native CLI binaries such as `choreo-fmt` |
| `native-examples` | no | Build native examples that depend on local runtime tooling |

#### Lean Bridge Crate (`telltale-bridge`)

| Feature | Default | Description |
|---------|---------|-------------|
| `runner` | yes | `LeanRunner` for invoking Lean binary |
| `cli` | no | Command-line interface binary |
| `exporter` | no | Choreography exporter binary |
| `golden` | no | Golden file management CLI |

#### Example: Minimal Dependencies

```toml
# Just the core runtime, no algorithms
telltale = { version = "10.0.0", default-features = false }
```

This keeps the dependency surface small while enabling the core runtime.

#### Example: Full Feature Set

```toml
# Everything enabled
telltale = { version = "10.0.0", features = ["full"] }
```

This enables all optional features for the facade crate.

For WASM support, enable the `wasm` feature on the choreography crate.

```toml
telltale-runtime = { version = "10.0.0", features = ["wasm"] }
```

This enables compilation to WebAssembly targets.

## Creating a Choreography

This example shows a simple ping-pong protocol between two roles.

Define the protocol using the `tell!` macro.

```rust
use telltale::tell;

tell! {
  protocol PingPong =
    roles Alice, Bob
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}
```

The macro generates the protocol module and, when the protocol is projectable,
the session surfaces. Use `PingPong::proof_status` to inspect whether a protocol
is session-projectable or only protocol-machine executable. For advanced
scenarios requiring runtime parsing, see [Choreographic DSL](202_choreographic_dsl.md).

Run the protocol using the effect system.

```rust
use telltale::tell;

tell! {
  protocol PingPong =
    roles Alice, Bob
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}

assert!(PingPong::proof_status::SESSION_PROJECTABLE);
```

Start from `tell!` and the generated protocol/effect surfaces. The older
effect-program builder APIs still exist inside `telltale-runtime`, but
they are no longer the recommended public entrypoint.

## Core Concepts

### Choreographies

A choreography specifies a distributed protocol from a global viewpoint. Projection transforms the global view into local behavior for each role.

### Roles

Roles are participants in the protocol. Each role sends and receives messages according to their projected session type.

### Messages

Messages are data exchanged between roles. They must implement `Serialize` and `Deserialize` from the `serde` library.

### Effect Handlers

Handlers interpret choreographic effects into actual communication. Different handlers provide different transports.

The `InMemoryHandler` provides local testing. The `TelltaleHandler` provides session-based communication. WebSocket handlers provide network communication.

The `TelltaleHandler` supports two patterns. You can register built-in `TelltaleSession` pairs.

```rust
let (client_session, server_session) = TelltaleSession::pair();
client_endpoint.register_session(Role::Server, client_session);
server_endpoint.register_session(Role::Client, server_session);
```

Both endpoints now communicate through the session pair.

Alternatively, you can wrap your own sink and stream transports.

```rust
use telltale_runtime::effects::TelltaleSession;

let ws_session = TelltaleSession::from_sink_stream(websocket_writer, websocket_reader);
client_endpoint.register_session(Role::Server, ws_session);
```

Both options integrate with the same handler.

### Projection

The system projects global choreographies into local session types. Each role gets a type-safe API for their part of the protocol. This ensures communication follows the choreography specification.
