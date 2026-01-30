# Telltale

Telltale is a framework for choreographic programming with multiparty session types. Protocols are written from a global viewpoint and automatically projected to local types for each participant. Session types guarantee the absence of deadlocks and communication errors at compile time.

The Rust implementation provides a DSL, compiler, effect handler system, and transport abstraction. A parallel Lean 4 formalization verifies projection correctness, proves safety properties (subject reduction, deadlock freedom, determinism), and models an Iris-backed session-type VM with resource algebras and separation logic.

## Example

```rust
use telltale_choreography::choreography;

choreography! {
    protocol PingPong = {
        roles Alice, Bob
        Alice -> Bob: Ping
        Bob -> Alice: Pong
    }
}
```

The macro generates role types, message types, and session types. Protocol logic is decoupled from transport through effect handlers. `InMemoryHandler` runs protocols in tests. `TelltaleHandler` connects to real transports (WebSockets, QUIC, or custom sink/stream pairs).

```rust
let program = Program::new()
    .send(Role::Bob, Message::Ping)
    .recv::<Message>(Role::Bob)
    .end();

let result = interpret(&mut handler, &mut endpoint, program).await?;
```

## Rust Crates

All Rust source lives in `rust/`.

**`telltale`** is the facade crate with session type primitives (`Send`, `Receive`, `Select`, `Branch`, `End`) and async channel abstractions.

**`telltale-types`** defines `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort` with content addressing. These definitions match the Lean formalization exactly.

**`telltale-theory`** implements projection, merge, duality, sync/async subtyping, and bounded recursion.

**`telltale-choreography`** contains the DSL parser, compiler, effect handlers, middleware (tracing, retry, metrics, fault injection), simulation infrastructure, topology configuration, and WebAssembly support.

**`telltale-macros`** provides the `choreography!` macro and derive macros for roles and messages.

**`telltale-lean-bridge`** converts between Rust session types and Lean-compatible JSON. The `exporter` feature serializes choreography ASTs for the Lean verification pipeline.

## Lean Formalization

The `lean/` directory contains six libraries organized by concern.

**SessionTypes** defines the inductive global and local type structures.

**SessionCoTypes** develops coinductive equality, bisimulation, duality, and the inductive/coinductive roundtrip bridge.

**Choreography** implements projection from global to local types and proves harmony (the projection correctness theorem).

**Semantics** defines operational rules, typing judgments, and metatheory including determinism, deadlock freedom, and subject reduction.

**Protocol** models async buffered multiparty sessions with coherence, preservation, monitors, deployment, and spatial reasoning. This library carries 35 axioms and 0 sorries.

**Runtime** is the session-type bytecode VM verified with Iris separation logic. It covers resource algebras, cancelable invariants, a cooperative scheduler, WP rules for each instruction, and an adequacy theorem connecting the VM to observable traces. Iris primitives are axiomatized as shims that retire as the upstream iris-lean library matures.

The verification pipeline runs with `just telltale-lean-check` (requires Nix).

## WebAssembly

The core session types and choreography system compile to WebAssembly. Effect handlers and the platform abstraction layer work in browser environments. See `examples/wasm-ping-pong/` for a working example.

```bash
cd examples/wasm-ping-pong && wasm-pack build --target web
```

## Building

```bash
cargo build --workspace --all-targets --all-features   # build
cargo test --workspace --all-targets --all-features     # test
cargo clippy --workspace --all-targets --all-features -- -D warnings  # lint
cd lean && lake build                                   # lean (requires nix develop)
```

## License

Licensed under the MIT [license](LICENSE).
