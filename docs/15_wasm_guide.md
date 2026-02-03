# WASM Guide

This guide explains how to build and run the choreography runtime on `wasm32`.

## Overview

The `telltale-choreography` crate supports WASM targets. Core effects, handlers, and timeouts compile under `wasm32` using `wasm-bindgen-futures` and `wasm-timer`.

## What Works

In WASM builds you can use `Program`, `interpret`, and the effect handlers. `InMemoryHandler` and `TelltaleHandler` are WASM compatible for local or custom transports. Middleware such as `Trace`, `Metrics`, `Retry`, and `FaultInjection` uses `wasm-timer` for delays.

## Limitations

WASM is single threaded, so concurrency is async only. Direct `std::net` sockets are not available, so network transports must use browser APIs or host provided bindings.

## Enable WASM

Enable the `wasm` feature on the choreography crate.

```toml
[dependencies]
telltale-choreography = { path = "../rust/choreography", features = ["wasm"] }
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
```

The `wasm` feature enables `getrandom` support and pulls in the WASM runtime dependencies.

Build with `wasm-pack` or `cargo` targets.

```bash
wasm-pack build --target web
```

This produces a `pkg` directory with JavaScript bindings.

## Minimal Example

This example runs a simple request response program using `InMemoryHandler`.

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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
enum Message {
    Ping(String),
    Pong(String),
}

async fn run_once() -> Result<(), Box<dyn std::error::Error>> {
    use futures::join;
    use std::collections::HashMap;
    use std::sync::{Arc, Mutex};

    let channels = Arc::new(Mutex::new(HashMap::new()));
    let choice_channels = Arc::new(Mutex::new(HashMap::new()));

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

For multi role tests, share channels by using `InMemoryHandler::with_channels` and a shared channel map. The WASM test suite in `rust/choreography/tests/wasm_integration.rs` shows larger examples.

## TelltaleHandler in WASM

`TelltaleHandler` works in WASM with `SimpleChannel` or custom sessions.

```rust
use telltale_choreography::{SimpleChannel, TelltaleEndpoint, TelltaleHandler};

let (alice_ch, bob_ch) = SimpleChannel::pair();
let mut alice_ep = TelltaleEndpoint::new(Role::Alice);
let mut bob_ep = TelltaleEndpoint::new(Role::Bob);

alice_ep.register_channel(Role::Bob, alice_ch);
bob_ep.register_channel(Role::Alice, bob_ch);

let mut handler = TelltaleHandler::<Role, Message>::new();
```

Use your protocol message type for `Message` and ensure the role implements both `telltale::Role` and `RoleId`. For browser transports, build a `TelltaleSession` from a sink and stream and register it with `TelltaleEndpoint::register_session`.

## Runtime Utilities

The runtime provides WASM aware task spawning helpers.

```rust
use telltale_choreography::runtime::spawn;

spawn(async move {
    // task body
});
```

`spawn` uses Tokio on native targets and `wasm_bindgen_futures::spawn_local` on WASM.

## Testing

Use `wasm-bindgen-test` for browser tests.

```rust
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);
```

Run tests with `wasm-pack test --headless --chrome`.

See [Effect Handlers](07_effect_handlers.md) for handler details and [Telltale Handler](08_telltale_handler.md) for the channel based API.
