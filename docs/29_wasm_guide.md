# WASM Guide

This guide explains how to build and run the choreography runtime on `wasm32`. It covers feature flags, build tooling, handler compatibility, and testing.

## Overview

The `telltale-choreography` crate supports WASM targets. Core effects, handlers, and timeouts compile under `wasm32` using `wasm-bindgen-futures` and `wasm-timer`. The same `Program` and `interpret` API used on native targets works without modification. Platform differences are handled internally by the runtime module.

## What Works

In WASM builds you can use `Program`, `interpret`, and effect handlers. `InMemoryHandler` and `TelltaleHandler` are WASM compatible for local or custom transports. Middleware such as `Trace`, `Metrics`, and `Retry` is WASM compatible. `FaultInjection` is available with the `test-utils` feature.

Protocol definitions written with `choreography!` produce the same projected types on both platforms. The effect algebra is transport-agnostic. Only the lowest-level spawn and timer calls differ between native and WASM.

## Limitations

WASM is single threaded. Concurrency is async only. Direct `std::net` sockets are not available. Network transports must use browser APIs or host provided bindings.

Tokio-specific features such as `tokio::spawn` are not available. Use the `runtime::spawn` abstraction instead. File system access is also unavailable unless the host provides a binding.

## Enable WASM

Enable the `wasm` feature on the choreography crate.

```toml
[dependencies]
telltale-choreography = { version = "6.0.0", features = ["wasm"] }
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
```

The `wasm` feature enables `getrandom` support and pulls in the WASM runtime dependencies. Use a path dependency only for local workspace development.

Build with `wasm-pack` or `cargo` targets. `wasm-pack` produces a ready-to-use JavaScript package. Direct `cargo build --target wasm32-unknown-unknown` works for library crates that do not need JS bindings.

For reproducible local setup, install the same tool version used in CI.

```bash
cargo install wasm-pack --version 0.14.0 --locked
```

This installs the same `wasm-pack` version used in CI for reproducible builds.

```bash
wasm-pack build --target web
```

This produces a `pkg` directory with JavaScript bindings.

## Minimal Example

This example runs a simple request response program using `InMemoryHandler`. It defines the role, label, and message types needed by the effect system. It then builds two programs and runs them concurrently with shared channels.

The first section defines the `Role` and `Label` enums. `LabelId` requires string round-tripping via `as_str` and `from_str`. `RoleId` associates a label type and provides canonical names through `role_name`.

```rust
use serde::{Deserialize, Serialize};
use telltale_choreography::{interpret, InMemoryHandler, LabelId, Program, RoleId, RoleName};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Role {
    Client,
    Server,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Label {
    Ok,
}

impl LabelId for Label {
    fn as_str(&self) -> &'static str {
        match self {
            Label::Ok => "ok",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "ok" => Some(Label::Ok),
            _ => None,
        }
    }
}

impl RoleId for Role {
    type Label = Label;

    fn role_name(&self) -> RoleName {
        match self {
            Role::Client => RoleName::from_static("Client"),
            Role::Server => RoleName::from_static("Server"),
        }
    }
}
```

The `Message` enum carries the payload variants exchanged between roles. Both variants use `String` here, but any `Serialize + Deserialize` type works.

```rust
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
enum Message {
    Ping(String),
    Pong(String),
}
```

The `run_once` function creates shared channel maps and builds one handler per role. Each handler receives the same `Arc<Mutex<BTreeMap>>` pair so that sends from one role are visible to the other.

`Program::new()` starts a builder chain. The client sends a `Ping` and receives a response. The server receives first and replies with `Pong`. Both programs call `.end()` to close the session.

The `interpret` function drives each program through its handler. `futures::join!` runs both concurrently on the same async executor, which is compatible with both Tokio and WASM runtimes.

```rust
async fn run_once() -> Result<(), Box<dyn std::error::Error>> {
    use futures::join;
    use std::collections::BTreeMap;
    use std::sync::{Arc, Mutex};

    let channels = Arc::new(Mutex::new(BTreeMap::new()));
    let choice_channels = Arc::new(Mutex::new(BTreeMap::new()));

    let mut client =
        InMemoryHandler::with_channels(Role::Client, channels.clone(), choice_channels.clone());
    let mut server =
        InMemoryHandler::with_channels(Role::Server, channels.clone(), choice_channels.clone());

    let client_program = Program::new()
        .send(Role::Server, Message::Ping("hi".into()))
        .recv::<Message>(Role::Server)
        .end();

    let server_program = Program::new()
        .recv::<Message>(Role::Client)
        .send(Role::Client, Message::Pong("ok".into()))
        .end();

    let mut client_ep = ();
    let mut server_ep = ();

    let client_fut = interpret(&mut client, &mut client_ep, client_program);
    let server_fut = interpret(&mut server, &mut server_ep, server_program);
    let (_c, _s) = join!(client_fut, server_fut);
    Ok(())
}
```

For multi role tests, share channels by using `InMemoryHandler::with_channels` and a shared channel map. The WASM test suite in `rust/choreography/tests/wasm_integration.rs` shows larger examples. Each handler must reference the same `Arc<Mutex<BTreeMap>>` instances for messages to route correctly. The unit endpoint `()` is sufficient when no external state is needed.

## TelltaleHandler in WASM

`TelltaleHandler` works in WASM with `TelltaleSession` pairs or custom sessions. This handler manages typed endpoints and routes messages through registered sessions. It is the recommended handler for integration-level WASM tests.

```rust
use telltale_choreography::{TelltaleEndpoint, TelltaleHandler, TelltaleSession};

let (alice_session, bob_session) = TelltaleSession::pair();
let mut alice_ep = TelltaleEndpoint::new(Role::Client);
let mut bob_ep = TelltaleEndpoint::new(Role::Server);

alice_ep.register_session(Role::Server, alice_session);
bob_ep.register_session(Role::Client, bob_session);

let mut handler = TelltaleHandler::<Role, Message>::new();
```

Use your protocol message type for `Message`. The role must implement both `telltale::Role` and `RoleId`. For browser transports, build a `TelltaleSession` from a sink and stream. Register it with `TelltaleEndpoint::register_session`.

## Runtime Utilities

The runtime provides WASM aware task spawning helpers. These abstractions let the same protocol code run on both native and browser targets without conditional compilation at the call site.

```rust
use telltale_choreography::runtime::spawn;

spawn(async move {
    // task body
});
```

`spawn` uses Tokio on native targets and `wasm_bindgen_futures::spawn_local` on WASM.

## Testing

Use `wasm-bindgen-test` for WASM tests. Import the crate and annotate test functions with `#[wasm_bindgen_test]`. Tests marked with `#[wasm_bindgen_test(unsupported = test)]` run as standard `#[test]` on native targets and as WASM tests on `wasm32`.

```rust
use wasm_bindgen_test::*;
```

Repository-managed tests run under Node, not a browser driver. This avoids the need for a headless browser in CI.

```bash
just wasm-test-all
```

For ad hoc crate-level runs, use `wasm-pack test --node`. This compiles the crate for `wasm32` and executes tests in a Node environment.

See [Choreography Effect Handlers](09_effect_handlers.md) for handler details. See [Using Telltale Handlers](10_telltale_handler.md) for the channel based API.
