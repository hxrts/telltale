# Getting Started

## Installation

Add Telltale to your project dependencies.

```toml
[dependencies]
telltale = "*"
telltale-choreography = "*"
```

This adds the facade crate and the choreographic programming layer.

### Understanding the Crates

Telltale is organized as a Cargo workspace with several crates. The crate structure mirrors the Lean formalization for verified correspondence. The `telltale-types` crate contains core type definitions (`GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`) that match Lean exactly. The `telltale-theory` crate contains pure algorithms for projection, merge, subtyping, and well-formedness checks.

The `telltale-choreography` crate is the choreographic programming layer that provides the DSL parser, effect handlers, and code generation. The `telltale-lean-bridge` crate enables cross-validation with Lean through JSON import and export functions.

The `telltale` crate is the main facade that re-exports types from other crates with feature flags. Most users need both `telltale` and `telltale-choreography` for session types and the high-level DSL.

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

#### Choreography Crate (`telltale-choreography`)

| Feature | Default | Description |
|---------|---------|-------------|
| `test-utils` | no | Testing utilities (random, fault injection) |
| `wasm` | no | WebAssembly support |

#### Lean Bridge Crate (`telltale-lean-bridge`)

| Feature | Default | Description |
|---------|---------|-------------|
| `runner` | yes | LeanRunner for invoking Lean binary |
| `cli` | no | Command-line interface binary |
| `exporter` | no | Choreography exporter binary |
| `golden` | no | Golden file management CLI |

#### Example: Minimal Dependencies

```toml
# Just the core runtime, no algorithms
telltale = { version = "*", default-features = false }
```

This keeps the dependency surface small while enabling the core runtime.

#### Example: Full Feature Set

```toml
# Everything enabled
telltale = { version = "*", features = ["full"] }
```

This enables all optional features for the facade crate.

For WASM support, enable the wasm feature on the choreography crate.

```toml
telltale-choreography = { version = "*", features = ["wasm"] }
```

This enables compilation to WebAssembly targets.

## Creating a Choreography

This example shows a simple ping-pong protocol between two roles.

Define the choreography using the `choreography!` macro.

```rust
use telltale_choreography::choreography;

choreography!(r#"
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#);
```

The macro automatically generates role types, message types, and session types. This is the recommended approach for most use cases. For advanced scenarios requiring runtime parsing, see [Choreographic DSL](04_choreographic_dsl.md).

Run the protocol using the effect system.

```rust
use telltale_choreography::{InMemoryHandler, Program, interpret};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Role {
    Alice,
    Bob,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Message {
    Ping,
    Pong,
}

let mut handler = InMemoryHandler::new(Role::Alice);
let program = Program::new()
    .send(Role::Bob, Message::Ping)
    .recv::<Message>(Role::Bob)
    .end();

let mut endpoint = ();
let result = interpret(&mut handler, &mut endpoint, program).await?;
```

The `InMemoryHandler` provides local message passing for testing. See [Using Telltale Handlers](08_telltale_handler.md) for production handlers.

## Core Concepts

### Choreographies

A choreography specifies a distributed protocol from a global viewpoint. Projection transforms the global view into local behavior for each role.

### Roles

Roles are participants in the protocol. Each role sends and receives messages according to their projected session type.

### Messages

Messages are data exchanged between roles. They must implement `Serialize` and `Deserialize` from the serde library.

### Effect Handlers

Handlers interpret choreographic effects into actual communication. Different handlers provide different transports.

The `InMemoryHandler` provides local testing. The `TelltaleHandler` provides channel-based communication. WebSocket handlers provide network communication.

The `TelltaleHandler` supports two patterns. You can register built-in `SimpleChannel` pairs.

```rust
let (client_ch, server_ch) = SimpleChannel::pair();
client_endpoint.register_channel(Role::Server, client_ch);
server_endpoint.register_channel(Role::Client, server_ch);
```

Both endpoints now communicate through the channel pair.

Alternatively, you can wrap your own sink and stream transports.

```rust
use telltale_choreography::effects::TelltaleSession;

let ws_session = TelltaleSession::from_sink_stream(websocket_writer, websocket_reader);
client_endpoint.register_session(Role::Server, ws_session);
```

Both options integrate with the same handler.

### Projection

The system projects global choreographies into local session types. Each role gets a type-safe API for their part of the protocol. This ensures communication follows the choreography specification.
