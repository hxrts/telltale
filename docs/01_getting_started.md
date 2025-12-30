# Getting Started

## Installation

Add Rumpsteak-Aura to your project dependencies.

```toml
[dependencies]
rumpsteak-aura = "*"
rumpsteak-aura-choreography = "*"
```

This adds the main facade crate and the choreographic programming layer.

### Understanding the Crates

Rumpsteak-Aura is organized as a Cargo workspace with several crates. The crate structure mirrors the Lean formalization for verified correspondence.

The `rumpsteak-types` crate contains core type definitions. It provides `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`. These types match the Lean definitions exactly.

The `rumpsteak-theory` crate contains pure algorithms. It provides projection, merge, subtyping, and well-formedness checks. This crate has no IO or parsing dependencies.

The `rumpsteak-aura-choreography` crate is the choreographic programming layer. It provides the DSL parser, effect handlers, and code generation.

The `rumpsteak-aura-fsm` crate provides optional finite state machine support. Use it for visualization and alternative subtyping algorithms.

The `rumpsteak-lean-bridge` crate enables cross-validation with Lean. It provides JSON import and export functions.

The `rumpsteak-aura` crate is the main facade. It re-exports types from the other crates with feature flags.

Most users need both `rumpsteak-aura` and `rumpsteak-aura-choreography`. The facade provides session types. The choreography layer provides the high-level DSL.

For WASM support, enable the wasm feature.

```toml
rumpsteak-aura-choreography = { version = "0.7", features = ["wasm"] }
```

This enables compilation to WebAssembly targets.

## Creating a Choreography

This example shows a simple ping-pong protocol between two roles.

Define the choreography using the `choreography!` macro.

```rust
use rumpsteak_aura_choreography::choreography;

choreography! {
    PingPong {
        roles: Alice, Bob
        Alice -> Bob: Ping
        Bob -> Alice: Pong
    }
}
```

The macro automatically generates role types, message types, and session types. This is the recommended approach for most use cases. For advanced scenarios requiring runtime parsing, see [Choreographic DSL Parser](03_choreographic_dsl.md).

Run the protocol using the effect system.

```rust
use rumpsteak_aura_choreography::{InMemoryHandler, Program, interpret};
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

The `InMemoryHandler` provides local message passing for testing. See [Using Rumpsteak Handlers](07_rumpsteak_handler.md) for production handlers.

## Core Concepts

### Choreographies

A choreography specifies a distributed protocol from a global viewpoint. Projection transforms the global view into local behavior for each role.

### Roles

Roles are participants in the protocol. Each role sends and receives messages according to their projected session type.

### Messages

Messages are data exchanged between roles. They must implement `Serialize` and `Deserialize` from the serde library.

### Effect Handlers

Handlers interpret choreographic effects into actual communication. Different handlers provide different transports.

The `InMemoryHandler` provides local testing. The `RumpsteakHandler` provides channel-based communication. WebSocket handlers provide network communication.

The `RumpsteakHandler` supports two patterns. You can register built-in `SimpleChannel` pairs.

```rust
let (client_ch, server_ch) = SimpleChannel::pair();
client_endpoint.register_channel(Role::Server, client_ch);
server_endpoint.register_channel(Role::Client, server_ch);
```

Both endpoints now communicate through the channel pair.

Alternatively, you can wrap your own sink and stream transports.

```rust
use rumpsteak_aura_choreography::effects::RumpsteakSession;

let ws_session = RumpsteakSession::from_sink_stream(websocket_writer, websocket_reader);
client_endpoint.register_session(Role::Server, ws_session);
```

Both options integrate with the same handler.

### Projection

The system projects global choreographies into local session types. Each role gets a type-safe API for their part of the protocol. This ensures communication follows the choreography specification.
