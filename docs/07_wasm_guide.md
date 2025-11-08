# WASM Guide

## Overview

Rumpsteak's choreographic programming system compiles to WebAssembly. The core library and effect handlers work in browser environments.

WASM support enables choreographic protocols in web applications, browser-based distributed systems, and serverless edge computing.

## What Works in WASM

The following features compile and run in WASM:

Core session types and choreography system work fully. The InMemoryHandler provides local message passing for testing protocols. RumpsteakHandler now compiles for WASM and can be used with custom network transports (WebSocket, fetch API, etc.). All middleware (Trace, Metrics, Retry, FaultInjection) functions correctly. Effect system and interpreter execute normally. Timeouts use wasm-timer for cross-platform support.

## What Does Not Work in WASM

The caching example uses Redis and Hyper which are not WASM compatible.

Multi-threading is unavailable since WASM runs single-threaded.

Native file system access requires browser File APIs.

## Building for WASM

Add the wasm feature to your dependencies:

```toml
[dependencies]
rumpsteak-choreography = { version = "0.1", features = ["wasm"] }
wasm-bindgen = "0.2"
wasm-bindgen-futures = "0.4"
```

Build using wasm-pack:

```bash
wasm-pack build --target web
```

This generates a pkg directory with JavaScript bindings.

## Example Protocol

The wasm-ping-pong example demonstrates a complete browser protocol:

```rust
use wasm_bindgen::prelude::*;
use rumpsteak_choreography::{InMemoryHandler, Program, interpret};

#[wasm_bindgen]
pub async fn run_protocol(message: String) -> Result<String, JsValue> {
    let mut handler = InMemoryHandler::new(Role::Alice);
    
    let program = Program::new()
        .send(Role::Bob, Message::Ping(message))
        .recv::<Message>(Role::Bob)
        .end();
    
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await
        .map_err(|e| JsValue::from_str(&format!("{:?}", e)))?;
    
    match result.received_values.first() {
        Some(Message::Pong(response)) => Ok(response.clone()),
        _ => Err(JsValue::from_str("Expected Pong message")),
    }
}
```

The wasm_bindgen attribute exposes the function to JavaScript.

Build and run the example:

```bash
cd examples/wasm-ping-pong
./build.sh
python3 -m http.server 8000
```

Open http://localhost:8000 in a browser to run the protocol.

## Using RumpsteakHandler in WASM

RumpsteakHandler now compiles for WASM. To use it with real network transport:

```rust
use wasm_bindgen::prelude::*;
use rumpsteak_choreography::{RumpsteakHandler, RumpsteakEndpoint, SimpleChannel};

#[wasm_bindgen]
pub async fn run_distributed_protocol() -> Result<(), JsValue> {
    // Create endpoints
    let mut alice_ep = RumpsteakEndpoint::new(Role::Alice);
    let mut bob_ep = RumpsteakEndpoint::new(Role::Bob);
    
    // Option 1: use SimpleChannel (works natively and in WASM)
    let (alice_ch, bob_ch) = SimpleChannel::pair();
    alice_ep.register_channel(Role::Bob, alice_ch);
    bob_ep.register_channel(Role::Alice, bob_ch);

    // Option 2: wrap browser transports directly
    // let ws_session = RumpsteakSession::from_sink_stream(ws_writer, ws_reader);
    // alice_ep.register_session(Role::Bob, ws_session);
    
    // Create handler
    let mut handler = RumpsteakHandler::new();
    
    // Use with choreography operations
    handler.send(&mut alice_ep, Role::Bob, &message).await?;
    let response = handler.recv(&mut bob_ep, Role::Alice).await?;
    
    Ok(())
}
```

SimpleChannel uses futures::channel::mpsc which is WASM-compatible. For distributed WASM applications, implement custom channels using browser APIs.

### Async traits in WASM

The handler traits continue to use the `async_trait` macro rather than native `async fn` in traits. This keeps the traits object-safe (needed for middleware stacks such as `Trace<Retry<H>>`) and lets us share a single implementation strategy across native and WASM targets. The generated futures are still `Send`, so handlers that run under multithreaded executors behave the same way as handlers compiled for single-threaded WASM.

## Custom Network Transport

InMemoryHandler works for single-context protocols. Real distributed WASM applications need network transport.

Implement ChoreoHandler with WebSocket or fetch APIs:

```rust
use web_sys::WebSocket;
use wasm_bindgen::JsCast;

pub struct WebSocketHandler {
    role: Role,
    socket: WebSocket,
    incoming: mpsc::UnboundedReceiver<Vec<u8>>,
}

impl WebSocketHandler {
    pub fn new(role: Role, url: &str) -> Result<Self, JsValue> {
        let socket = WebSocket::new(url)?;
        let (tx, rx) = mpsc::unbounded();
        
        let onmessage = Closure::wrap(Box::new(move |e: MessageEvent| {
            // Handle incoming messages
            if let Ok(buffer) = e.data().dyn_into::<js_sys::ArrayBuffer>() {
                let bytes = js_sys::Uint8Array::new(&buffer).to_vec();
                tx.unbounded_send(bytes).ok();
            }
        }) as Box<dyn FnMut(MessageEvent)>);
        
        socket.set_onmessage(Some(onmessage.as_ref().unchecked_ref()));
        onmessage.forget();
        
        Ok(Self { role, socket, incoming: rx })
    }
}
```

With the Phase 3 handler you can skip the custom `ChoreoHandler`—wrap this
`WebSocketHandler` with `RumpsteakSession::from_sink_stream` and register it on
the endpoint instead.

For HTTP-based protocols, use the fetch API:

```rust
use web_sys::window;

async fn send_http(to: Role, msg: &Message) -> Result<()> {
    let window = window().ok_or("no window")?;
    let resp = JsFuture::from(
        window.fetch_with_str(&format!("http://server/{}", to))
    ).await?;
    Ok(())
}
```

The pattern is the same: implement ChoreoHandler using browser APIs for your transport.

## Platform Differences

The runtime module provides platform-specific functions:

```rust
use rumpsteak_choreography::runtime::{spawn, spawn_local};

spawn(async { /* task */ });  // Works on native and WASM
```

On native targets, spawn uses tokio. On WASM, it uses wasm-bindgen-futures.

Timeouts use conditional compilation:

```rust
// Native
tokio::time::timeout(duration, future).await

// WASM
use wasm_timer::Delay;
futures::select! {
    result = future => result,
    _ = Delay::new(duration) => Err(Timeout),
}
```

The library handles this automatically. Your code works on both platforms.

## Testing in WASM

Use wasm-bindgen-test for browser tests:

```rust
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
async fn test_protocol() {
    let mut handler = InMemoryHandler::new(Role::Alice);
    let program = Program::new().send(Role::Bob, Message::Test).end();
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await;
    assert!(result.is_ok());
}
```

Run tests with wasm-pack:

```bash
wasm-pack test --headless --chrome
```

The tests execute in a headless browser.

## Deployment

For production WASM deployments:

Build with release optimizations:

```bash
wasm-pack build --target web --release
```

The generated WASM is optimized for size and performance.

Serve the pkg directory with your web application. Import the JavaScript bindings:

```html
<script type="module">
    import init, { run_protocol } from './pkg/my_protocol.js';
    
    async function main() {
        await init();
        const result = await run_protocol("data");
        console.log(result);
    }
    
    main();
</script>
```

The init function loads the WASM module. Protocol functions then become available.

## Browser Compatibility

WASM support works in modern browsers:

Chrome/Chromium 90+, Firefox 88+, Safari 14+, Edge 90+.

Older browsers may require polyfills or transpilation.

## Performance

WASM execution is near-native speed for computation. Network operations have typical browser fetch/WebSocket latency.

InMemoryHandler has negligible overhead in WASM. Custom network handlers add latency from browser APIs.

The generated WASM binary size is approximately 200-300KB after optimization.

## Limitations

WASM is single-threaded. Parallel protocol execution uses async concurrency, not OS threads.

Browser security restricts some operations. Cross-origin requests need CORS configuration. WebSocket connections require proper server setup.

File system access uses browser APIs which differ from native file operations.

## Example Projects

The examples/wasm-ping-pong directory contains a complete working example.

See the build script for compilation details and the README for deployment instructions.
