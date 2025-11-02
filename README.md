# Rumpsteak (Aura)

**This is a fork of Zak Cutner's [Rumpsteak](https://github.com/zakcutner/rumpsteak) library, which adds a choreographic programming DSL which generates session typed code with an effect API.**

[![Actions](https://github.com/zakcutner/rumpsteak/workflows/Check/badge.svg)](https://github.com/zakcutner/rumpsteak/actions)
[![Crate](https://img.shields.io/crates/v/rumpsteak)](https://crates.io/crates/rumpsteak)
[![Docs](https://docs.rs/rumpsteak/badge.svg)](https://docs.rs/rumpsteak)
[![License](https://img.shields.io/crates/l/rumpsteak)](LICENSE)

Rumpsteak is a Rust framework for _safely_ and _efficiently_ implementing
[message-passing](https://doc.rust-lang.org/book/ch16-02-message-passing.html)
[asynchronous](https://rust-lang.github.io/async-book/) programs. It uses
multiparty session types to statically guarantee the absence of communication errors such as deadlocks and asynchronous subtyping to allow optimizing communications.

Multiparty session types (MPST) verify the safety of message-passing protocols, as described in [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf).
Asynchronous subtyping, introduced for MPST in [Precise Subtyping for
Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf),
verifies the reordering of messages to create more optimized implementations than are usually possible with MPST.

## Features

- Deadlock-free communication with session types.
- Integrates with `async`/`await` code.
- Supports any number of participants.
- Choreographic programming with DSL parser and automatic projection.
- Effect handler system with multiple implementations (in-memory, distributed).
- RumpsteakHandler with session state tracking.
- Middleware support (tracing, retry, metrics, fault injection).
- WebAssembly support for browser-based protocols.

## Usage

This is the Aura fork of Rumpsteak with enhanced choreographic programming support.

```toml
[dependencies]
rumpsteak-aura = { git = "https://github.com/hxrts/rumpsteak-aura" }
```

For choreographic programming:
```toml
[dependencies]
rumpsteak-choreography = { git = "https://github.com/hxrts/rumpsteak-aura" }
```

## Example

Define a protocol using the choreographic DSL:

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

Run the protocol with the effect handler system:

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

The choreography macro generates role types, message types, and session types automatically. The effect handler system decouples protocol logic from transport. Use `InMemoryHandler` for testing or `RumpsteakHandler` for production. See `docs/` for guides.

## Structure

#### `caching/`

HTTP cache case study backed by Redis.

#### `choreography/`

Choreographic programming layer for global protocol specification with automatic projection to local session types. Includes a Pest-based DSL parser for `.choreography` files with support for protocol composition, guards, annotations, and parameterized roles.

A transport-agnostic effect handler system, with `InMemoryHandler` for testing and `RumpsteakHandler` for production distributed execution. The effect handler system also provides middleware support for tracing, retry, metrics, and fault injection. Session state tracking provides metadata for debugging and monitoring. The system works in browser environments with WebAssembly support. Guides available in the `docs/` directory.

*This is the primary extension of the original version with significant enhancements.*

#### `examples/`

Examples of using Rumpsteak from popular protocols (updated to use new APIs). Includes `wasm-ping-pong/` demonstrating browser-based protocols.

#### `fsm/`

Finite state machine support for session types, including DOT parsing and subtyping verification.

#### `macros/`

Crate for procedural macros used within Rumpsteak's API.

## WebAssembly Support

Supports compilation to WebAssembly, allowing the core session types and choreography system to run in browser environments. Both the effect handlers and platform-agnostic runtime abstraction work in WASM, enabling you to implement custom network transports using `ChoreoHandler` with WebSockets, WebRTC, or other browser APIs. The `examples/wasm-ping-pong/` directory contains a working example.

To get started, run `cd examples/wasm-ping-pong && ./build.sh` (or `wasm-pack build --target web`).

## License

Licensed under the MIT [license](LICENSE).
