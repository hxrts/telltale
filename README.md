# Rumpsteak Aura ♨️

Rust-based choreographic programming DSL for projecting session typed protocols.

Where did the grotesque name come from? The session type system is forked from Zak Cutner's [Rumpsteak](https://github.com/zakcutner/rumpsteak) library. This is an experiment in projecting session types from a global viewpoint. I've added a choreographic programming DSL which generates session typed code into an effect API.

[![Crate](https://img.shields.io/crates/v/rumpsteak-aura)](https://crates.io/crates/rumpsteak-aura)
[![Docs](https://docs.rs/rumpsteak-aura/badge.svg)](https://docs.rs/rumpsteak-aura)
[![License](https://img.shields.io/crates/l/rumpsteak-aura)](LICENSE)

`rumpsteak-aura` is a Rust framework for safely and efficiently implementing
message-passing asynchronous programs. It uses multiparty session types to statically guarantee the absence of communication errors such as deadlocks and asynchronous subtyping to allow optimizing communications.

Multiparty session types (MPST) verify the safety of message-passing protocols, as described in [A Very Gentle Introduction to Multiparty Session Types](http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf).
Asynchronous subtyping, introduced for MPST in [Precise Subtyping for
Asynchronous Multiparty Sessions](http://mrg.doc.ic.ac.uk/publications/precise-subtyping-for-asynchronous-multiparty-sessions/main.pdf),
verifies the reordering of messages to create more optimized implementations than are usually possible with MPST.

[Mechanised Subject Reduction for Multiparty Asynchronous Session Types](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.31) (ECOOP 2025) presents a mechanized Coq proof addressing flaws in the original MPST formulation by Honda et al. The authors identify that the original subject reduction theorem does not hold under asynchronous semantics due to out-of-order message delivery, and introduce a restricted theory with an additional *unstuckness* property that restores subject reduction. Their mechanization ([github.com/Tirore96/subject_reduction](https://github.com/Tirore96/subject_reduction)) includes a decidable coinductive equality for session types and a corrected projection theorem.

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

For core session types:

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
    protocol PingPong = {
        roles Alice, Bob
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

This project is organized as a Cargo workspace. All Rust crates are in the `rust/` directory:

#### `rust/src/` - Core Session Types (`rumpsteak-aura`)

The facade library providing core session type primitives (`Send`, `Receive`, `Select`, `Branch`, `End`), async channels, and role definitions. Re-exports types from other crates.

#### `rust/types/` - Type Definitions (`rumpsteak-types`)

Core type definitions matching Lean exactly: `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`. Includes content addressing infrastructure.

#### `rust/theory/` - Session Type Algorithms (`rumpsteak-theory`)

Pure algorithms for session type operations: projection, merge, duality, synchronous/asynchronous subtyping, and bounded recursion strategies.

#### `rust/choreography/` - Choreographic Programming (`rumpsteak-aura-choreography`)

Choreographic programming layer with DSL parser, automatic projection, and code generation. Includes a transport-agnostic effect handler system (`InMemoryHandler` for testing, `RumpsteakHandler` for production), middleware support (tracing, retry, metrics, fault injection), and WebAssembly support.

#### `rust/macros/` - Procedural Macros (`rumpsteak-aura-macros`)

Procedural macros including `choreography!` for inline protocol definitions.

#### `rust/lean-bridge/` - Lean Verification Bridge (`rumpsteak-lean-bridge`)

Bidirectional conversion between Rust session types and Lean-compatible JSON. The `exporter` feature adds a CLI tool that exports choreography ASTs to JSON for Lean 4 verification.

#### `examples/` - Protocol Examples

Examples demonstrating Rumpsteak usage. Includes `wasm-ping-pong/` for browser-based protocols.

## WebAssembly Support

Supports compilation to WebAssembly, allowing the core session types and choreography system to run in browser environments. Both the effect handlers and platform-agnostic runtime abstraction work in WASM, enabling you to implement custom network transports using `ChoreoHandler` with WebSockets, WebRTC, or other browser APIs. The `examples/wasm-ping-pong/` directory contains a working example.

To get started, run `cd examples/wasm-ping-pong && ./build.sh` (or `wasm-pack build --target web`).

## Formal Verification

Choreographic projection correctness is verified using Lean. The verification pipeline validates:

- **Projection correctness**: Local types accurately represent each role's view of the global protocol
- **Duality**: Send/receive pairs are properly matched between communicating roles
- **Subtyping invariants**: Asynchronous message reordering preserves causal dependencies
- **Effect conformance**: Generated effect programs match their projected session types

The `lean/` directory contains Lean proof modules, and `lean-bridge` (with the `exporter` feature) serializes Rust choreography ASTs to JSON for verification. Run the full pipeline with `just rumpsteak-lean-check` (requires Nix). See `docs/14_lean_verification.md` for details.

## License

Licensed under the MIT [license](LICENSE).
