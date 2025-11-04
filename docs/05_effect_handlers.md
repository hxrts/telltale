# Effect Handlers

## Overview

The effect handler system decouples protocol logic from transport implementation. Handlers interpret choreographic effects into actual communication operations.

A protocol executes by calling handler methods for each operation. Different handlers provide different execution strategies without changing protocol code.

## ChoreoHandler Trait

All handlers implement this trait:

```rust
pub trait ChoreoHandler {
    type Role: RoleId;
    type Endpoint;
    
    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> Result<()>;
    
    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> Result<M>;
    
    async fn choose(
        &mut self, ep: &mut Self::Endpoint, who: Self::Role, label: Label
    ) -> Result<()>;
    
    async fn offer(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> Result<Label>;
}
```

The `send` method transmits a message to another role. The `recv` method waits for a message from another role. The `choose` method makes a branch selection. The `offer` method receives a branch selection.

The `Endpoint` associated type holds connection state. Different handlers use different endpoint types.

### Send bounds and portability

The trait requires messages (`Serialize + Send + Sync` for `send`, `DeserializeOwned + Send` for `recv`) and handler futures (`F: Future + Send` in `with_timeout`) to be `Send`. This matches the requirements of the runtimes we target (tokio on native, single-thread executors on WASM) and keeps middleware stacks interchangeable between single- and multi-threaded deployments. Even on WASM the bounds remain, so code that is written for browsers compiles unchanged for native binaries that move work across threads.

## Built-in Handlers

### InMemoryHandler

Location: `choreography/src/effects/handlers/in_memory.rs`

Provides fast local message passing for testing. Uses futures channels internally.

Usage:

```rust
use rumpsteak_choreography::InMemoryHandler;

let mut handler = InMemoryHandler::new(Role::Alice);
```

For coordinated testing between roles:

```rust
let channels = Arc::new(Mutex::new(HashMap::new()));
let choice_channels = Arc::new(Mutex::new(HashMap::new()));

let alice = InMemoryHandler::with_channels(Role::Alice, channels.clone(), choice_channels.clone());
let bob = InMemoryHandler::with_channels(Role::Bob, channels.clone(), choice_channels.clone());
```

The shared channels enable communication between handlers in the same process.

### RumpsteakHandler

Location: `choreography/src/effects/handlers/rumpsteak.rs`

Provides production-ready session-typed channels. Uses the core Rumpsteak library for type-safe communication.

This handler enforces session types at runtime and provides strong guarantees about protocol compliance.

See `06_rumpsteak_handler.md` for complete documentation.

### RecordingHandler

Location: `choreography/src/effects/handlers/recording.rs`

Records all operations for verification and testing. Stores a log of send, recv, choose, and offer calls.

Usage:

```rust
use rumpsteak_choreography::RecordingHandler;

let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...
let events = handler.events();
assert_eq!(events[0], RecordedEvent::Send { to: Role::Bob, ... });
```

The recorded events can be inspected in tests to verify protocol behavior.

### NoOpHandler

Location: `choreography/src/effects/handler.rs`

Implements all operations as no-ops. Useful for testing protocol structure without actual communication.

```rust
let handler = NoOpHandler::<MyRole>::new();
```

All operations succeed immediately without side effects.

## Middleware

Middleware wraps handlers to add cross-cutting functionality. Multiple middleware can compose around a single handler.

### Trace

Location: `choreography/src/effects/middleware/mod.rs`

Logs all operations for debugging. Outputs send, recv, choose, and offer calls with role and message details.

Usage:

```rust
use rumpsteak_choreography::middleware::Trace;

let base_handler = InMemoryHandler::new(role);
let mut handler = Trace::new(base_handler, "Alice".to_string());
```

Each operation logs before delegating to the inner handler.

### Metrics

Location: `choreography/src/effects/middleware/metrics.rs`

Counts operations for monitoring. Tracks send_count, recv_count, choose_count, and offer_count.

Usage:

```rust
use rumpsteak_choreography::middleware::Metrics;

let base_handler = InMemoryHandler::new(role);
let mut handler = Metrics::new(base_handler);
// ... execute protocol ...
println!("Sends: {}", handler.send_count());
```

Metrics accumulate over the handler lifetime.

### Retry

Location: `choreography/src/effects/middleware/retry.rs`

Retries failed operations with exponential backoff. Only retries send operations since recv changes protocol state.

Usage:

```rust
use rumpsteak_choreography::middleware::Retry;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = Retry::new(base_handler, 3, Duration::from_millis(100));
```

The handler retries up to 3 times with delays of 100ms, 200ms, 400ms.

### FaultInjection

Location: `choreography/src/effects/middleware/fault_injection.rs`

Requires the `test-utils` feature. Injects random failures and delays for testing fault tolerance.

Usage:

```rust
use rumpsteak_choreography::middleware::FaultInjection;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = FaultInjection::new(base_handler)
    .with_failure_rate(0.1)  // 10% failure rate
    .with_delay_range(Duration::from_millis(10), Duration::from_millis(100));
```

Operations randomly fail or delay based on configured rates.

## Composing Middleware

Middleware can stack:

```rust
let handler = InMemoryHandler::new(role);
let handler = Retry::new(handler, 3, Duration::from_millis(100));
let handler = Trace::new(handler, "Alice".to_string());
let handler = Metrics::new(handler);
```

Operations flow through the stack: Metrics -> Trace -> Retry -> InMemory.

## Creating Custom Handlers

Implement `ChoreoHandler` for your transport:

```rust
pub struct MyHandler {
    role: MyRole,
    connections: HashMap<MyRole, Connection>,
}

#[async_trait]
impl ChoreoHandler for MyHandler {
    type Role = MyRole;
    type Endpoint = MyEndpoint;
    
    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> Result<()> {
        let conn = self.connections.get_mut(&to)?;
        let bytes = bincode::serialize(msg)?;
        conn.send(bytes).await?;
        Ok(())
    }
    
    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> Result<M> {
        let conn = self.connections.get_mut(&from)?;
        let bytes = conn.recv().await?;
        let msg = bincode::deserialize(&bytes)?;
        Ok(msg)
    }
    
    // Implement choose and offer...
}
```

The handler manages connection state and serialization. The endpoint type holds per-role state if needed.

## Handler Selection Guide

Use InMemoryHandler for local testing and simple protocols.

Use RumpsteakHandler for production deployments with session type guarantees.

Use RecordingHandler for test verification and debugging.

Use NoOpHandler for protocol structure testing.

Use middleware to add logging, metrics, retries, or fault injection to any handler.

## WASM Considerations

InMemoryHandler and RumpsteakHandler both work in WASM environments using futures channels.

For WASM network communication, implement a custom handler using web-sys WebSocket or fetch APIs. See `07_wasm_guide.md` for details.

## Effect Interpretation

Handlers interpret effect programs:

```rust
let program = Program::new()
    .send(Role::Bob, msg)
    .recv::<Response>(Role::Bob)
    .end();

let result = interpret(&mut handler, &mut endpoint, program).await?;
```

The `interpret` function walks the effect tree and calls handler methods for each operation. The result contains received messages and execution status.
