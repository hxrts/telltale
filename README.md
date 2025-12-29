# Rumpsteak (Aura) ♨️

Rust-based choreographic programming DSL for projecting session typed protocols.

Where did the grotesque name come from? The session type system is forked from Zak Cutner's [Rumpsteak](https://github.com/zakcutner/rumpsteak) library. This is an experiment in projecting session types from a global viewpoint. So I've added a choreographic programming DSL which generates session typed code into an effect API.**

[![Crate](https://img.shields.io/crates/v/rumpsteak-aura)](https://crates.io/crates/rumpsteak-aura)
[![Docs](https://docs.rs/rumpsteak-aura/badge.svg)](https://docs.rs/rumpsteak-aura)
[![License](https://img.shields.io/crates/l/rumpsteak-aura)](LICENSE)

Rumpsteak is a Rust framework for _safely_ and _efficiently_ implementing
message-passing asynchronous programs. It uses multiparty session types to statically guarantee the absence of communication errors such as deadlocks and asynchronous subtyping to allow optimizing communications.

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
- Formal verification of choreographic projection using Lean 4.

## Usage

This is the Aura fork of Rumpsteak with enhanced choreographic programming support.

```toml
[dependencies]
rumpsteak-aura = "*"
```

For choreographic programming:
```toml
[dependencies]
rumpsteak-aura-choreography = "*"
```

## Example

Define a protocol using the choreographic DSL:

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

Run the protocol with the effect handler system:

```rust
use rumpsteak_aura_choreography::{InMemoryHandler, Program, interpret};
use serde::{Serialize, Deserialize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Role {
    Alice,
    Bob,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
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

The choreography macro generates role types, message types, and session types automatically. The effect handler system decouples protocol logic from transport. Use `InMemoryHandler` for testing or `RumpsteakHandler` for production. `RumpsteakHandler` now accepts either the built-in `SimpleChannel` pairs via `register_channel` or any custom sink/stream transport via `RumpsteakSession::from_sink_stream` + `register_session`, so you can drop in WebSockets, QUIC streams, or other runtimes without writing a new handler. See `docs/` for guides.

## Workspace Structure

This project is organized as a Cargo workspace with multiple crates:

#### `src/` - Core Session Types (`rumpsteak-aura`)

The foundation library providing core session type primitives, async channels, role definitions, and serialization support. This is the base dependency for all other crates and implements the fundamental session types theory.

#### `choreography/` - Choreographic Programming (`rumpsteak-aura-choreography`)

Choreographic programming layer for global protocol specification with automatic projection to local session types. Includes a Pest-based DSL parser for `.choreography` files with support for protocol composition, guards, annotations, and parameterized roles.

A transport-agnostic effect handler system, with `InMemoryHandler` for testing and `RumpsteakHandler` for production distributed execution. The effect handler system also provides middleware support for tracing, retry, metrics, and fault injection. Session state tracking provides metadata for debugging and monitoring. The system works in browser environments with WebAssembly support. Guides available in the `docs/` directory.

*This is the primary extension of the original version with significant enhancements.*

#### `fsm/` - Finite State Machines (`rumpsteak-aura-fsm`)

Finite state machine support for session types, including DOT parsing and subtyping verification. Optional dependency for advanced session type analysis.

#### `macros/` - Procedural Macros (`rumpsteak-aura-macros`)

Procedural macros used by both the core library and choreography crate, including the `choreography!` macro for inline protocol definitions.

#### `lean-exporter/` - Lean Verification Exporter

Exports choreography ASTs and projected programs to JSON for formal verification in Lean 4. Used by the verification pipeline to validate projection correctness, duality, and subtyping invariants.

#### `caching/` - Example Application

HTTP cache case study backed by Redis, demonstrating real-world usage of Rumpsteak with distributed caching protocols.

#### `examples/` - Protocol Examples

Examples of using Rumpsteak from popular protocols (updated to use new APIs). Includes `wasm-ping-pong/` demonstrating browser-based protocols running in WebAssembly.

## WebAssembly Support

Supports compilation to WebAssembly, allowing the core session types and choreography system to run in browser environments. Both the effect handlers and platform-agnostic runtime abstraction work in WASM, enabling you to implement custom network transports using `ChoreoHandler` with WebSockets, WebRTC, or other browser APIs. The `examples/wasm-ping-pong/` directory contains a working example.

To get started, run `cd examples/wasm-ping-pong && ./build.sh` (or `wasm-pack build --target web`).

## Formal Verification

Choreographic projection correctness is verified using Lean. The verification pipeline validates:

- **Projection correctness**: Local types accurately represent each role's view of the global protocol
- **Duality**: Send/receive pairs are properly matched between communicating roles
- **Subtyping invariants**: Asynchronous message reordering preserves causal dependencies
- **Effect conformance**: Generated effect programs match their projected session types

The `lean/` directory contains Lean proof modules, and `lean-exporter` serializes Rust choreography ASTs to JSON for verification. Run the full pipeline with `just rumpsteak-lean-check` (requires Nix). See `docs/13_lean_verification.md` for details.

## License

Licensed under the MIT [license](LICENSE).
