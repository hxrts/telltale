# Getting Started

## Installation

Add Rumpsteak to your project using the Aura fork.

```toml
[dependencies]
rumpsteak-aura = "*"
rumpsteak-aura-choreography = "*"
```

This adds the core session types library and the choreographic programming layer.

### Understanding the Crates

Rumpsteak-Aura is organized as a Cargo workspace with several crates.

- The `rumpsteak-aura` crate is the core session types library. It is located in the root `src/` directory. This crate provides fundamental primitives for type-safe asynchronous communication, channels, and role definitions.
- The `rumpsteak-aura-choreography` crate is the choreographic programming layer. It is located in `choreography/`. This crate provides the DSL parser, automatic projection, effect handler system, and runtime support.
- The `rumpsteak-aura-fsm` crate provides optional finite state machine support. This crate enables advanced session type verification.
- The `rumpsteak-aura-macros` crate contains procedural macros used internally.

Most users need both `rumpsteak-aura` and `rumpsteak-aura-choreography`. The core library provides session types. The choreography layer provides the high-level DSL and effect system.

Advanced users who only need low-level session types can depend on just `rumpsteak-aura`. This excludes choreography features.

For WASM support, add the wasm feature.

```toml
rumpsteak-aura-choreography = { version = "*", features = ["wasm"] }
```

This enables compilation to WebAssembly targets.

## Creating a Choreography

This example shows a simple ping-pong protocol between two roles.

Define the choreography using the DSL parser.

```rust
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

let choreography_str = r#"
    choreography PingPong {
        roles: Alice, Bob;
        Alice -> Bob: Ping;
        Bob -> Alice: Pong;
    }
"#;

let choreography = parse_choreography_str(choreography_str)?;
```

The parser generates the AST representation. This representation can be used for projection and code generation.

Run the protocol using the effect system.

```rust
use rumpsteak_aura_choreography::{InMemoryHandler, Program, interpret, RoleId};
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum Role {
    Alice,
    Bob,
}

impl RoleId for Role {
    fn name(&self) -> String {
        format!("{:?}", self)
    }
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

The `InMemoryHandler` provides local message passing for testing. See [Using Rumpsteak Handlers](06_rumpsteak_handler.md) for production handlers.

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
