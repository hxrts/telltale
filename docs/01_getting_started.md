# Getting Started

## Installation

Add Rumpsteak to your project (using the Aura fork):

```toml
[dependencies]
rumpsteak-aura = "0.2"
rumpsteak-aura-choreography = "0.2"
```

### Understanding the Crates

Rumpsteak-Aura is organized as a Cargo workspace with several crates:

- **`rumpsteak-aura`**: Core session types library (located in the root `src/` directory). Provides fundamental primitives for type-safe asynchronous communication, channels, and role definitions.

- **`rumpsteak-choreography`**: Choreographic programming layer (located in `choreography/`). Provides the DSL parser, automatic projection, effect handler system, and runtime support.

- **`rumpsteak-fsm`**: Optional finite state machine support for advanced session type verification.

- **`rumpsteak-macros`**: Procedural macros used internally.

**For most users**: You need both `rumpsteak-aura` and `rumpsteak-choreography`. The core library provides session types, while the choreography layer provides the high-level DSL and effect system.

**For advanced users**: If you only need low-level session types without choreographies, you can depend on just `rumpsteak-aura`.

For WASM support, add the wasm feature:

```toml
rumpsteak-aura-choreography = { version = "0.2", features = ["wasm"] }
```

## Creating a Choreography

This example shows a simple ping-pong protocol between two roles.

Define the choreography using the macro:

```rust
use rumpsteak_choreography::choreography;

choreography! {
    PingPong {
        roles: Alice, Bob
        Alice -> Bob: Ping
        Bob -> Alice: Pong
    }
}
```

The macro generates role types, message types, and session types automatically.

Run the protocol using the effect system:

```rust
use rumpsteak_choreography::{InMemoryHandler, Program, interpret};

let mut handler = InMemoryHandler::new(Role::Alice);
let program = Program::new()
    .send(Role::Bob, Message::Ping)
    .recv::<Message>(Role::Bob)
    .end();

let mut endpoint = ();
let result = interpret(&mut handler, &mut endpoint, program).await?;
```

The `InMemoryHandler` provides local message passing for testing. See [Using Rumpsteak Handlers](06_rumpsteak_handler.md) for production handlers.

## Core Concepts

### Choreographies

A choreography specifies a distributed protocol from a global viewpoint. Each role sees only their local behavior after projection.

### Roles

Roles are participants in the protocol. They send and receive messages according to their projected session type.

### Messages

Messages are data exchanged between roles. They must implement serde's `Serialize` and `Deserialize`.

### Effect Handlers

Handlers interpret choreographic effects into actual communication. Different handlers provide different transports (in-memory, session-typed channels, WebSockets).

With `RumpsteakHandler`, you can either register the built-in `SimpleChannel` pairs:

```rust
let (client_ch, server_ch) = SimpleChannel::pair();
client_endpoint.register_channel(Role::Server, client_ch);
server_endpoint.register_channel(Role::Client, server_ch);
```

or wrap your own sink/stream transports:

```rust
use rumpsteak_choreography::effects::RumpsteakSession;

let ws_session = RumpsteakSession::from_sink_stream(websocket_writer, websocket_reader);
client_endpoint.register_session(Role::Server, ws_session);
```

Both options integrate with the same handler.

### Projection

The system projects global choreographies into local session types. Each role gets a type-safe API for their part of the protocol.
