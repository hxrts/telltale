# Effect Handlers

## Overview

The effect handler system decouples protocol logic from transport implementation. Handlers interpret choreographic effects into actual communication operations.

A protocol executes by calling handler methods for each operation. Different handlers provide different execution strategies. Protocol code remains unchanged.

## ChoreoHandler Trait

All handlers implement this trait.

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

    async fn with_timeout<F, T>(
        &mut self, ep: &mut Self::Endpoint, at: Self::Role, dur: Duration, body: F
    ) -> Result<T>
    where
        F: Future<Output = Result<T>> + Send;
}
```

The trait defines four core methods and a timeout hook.

The `send` method transmits a message to another role. The `recv` method waits for a message from another role. The `choose` method makes a branch selection. The `offer` method receives a branch selection.

The `Endpoint` associated type holds connection state. Different handlers use different endpoint types.

### Send bounds and portability

The trait requires messages to be `Send`. The `send` method requires `Serialize + Send + Sync`. The `recv` method requires `DeserializeOwned + Send`. Handler futures require `F: Future + Send` in `with_timeout`.

This matches the requirements of target runtimes. Native targets use tokio. WASM targets use single-thread executors. The bounds keep middleware stacks interchangeable between single-threaded and multi-threaded deployments.

Code written for browsers compiles unchanged for native binaries. Work can move across threads transparently.

## Built-in Handlers

### InMemoryHandler

The InMemoryHandler is located in `rust/choreography/src/effects/handlers/in_memory.rs`. It provides fast local message passing for testing. The implementation uses futures channels internally.

Basic usage creates a handler for a single role.

```rust
use rumpsteak_aura_choreography::InMemoryHandler;

let mut handler = InMemoryHandler::new(Role::Alice);
```

This creates an Alice handler.

For coordinated testing between roles, use shared channels.

```rust
let channels = Arc::new(Mutex::new(HashMap::new()));
let choice_channels = Arc::new(Mutex::new(HashMap::new()));

let alice = InMemoryHandler::with_channels(Role::Alice, channels.clone(), choice_channels.clone());
let bob = InMemoryHandler::with_channels(Role::Bob, channels.clone(), choice_channels.clone());
```

The shared channels enable communication between handlers in the same process.

### RumpsteakHandler

The RumpsteakHandler is located in `rust/choreography/src/effects/handlers/rumpsteak.rs`. It provides production-ready session-typed channels. The implementation uses the core Rumpsteak library for type-safe communication.

This handler enforces session types at runtime. It provides strong guarantees about protocol compliance.

See [Using Rumpsteak Handlers](07_rumpsteak_handler.md) for complete documentation.

### RecordingHandler

The RecordingHandler is located in `rust/choreography/src/effects/handlers/recording.rs`. It records all operations for verification and testing. The handler stores a log of send, recv, choose, and offer calls.

Basic usage creates a recording handler.

```rust
use rumpsteak_aura_choreography::RecordingHandler;

let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...
let events = handler.events();
assert_eq!(events[0], RecordedEvent::Send { to: Role::Bob, ... });
```

The recorded events can be inspected in tests to verify protocol behavior.

### NoOpHandler

The NoOpHandler is located in `rust/choreography/src/effects/handler.rs`. It implements all operations as no-ops. This is useful for testing protocol structure without actual communication.

```rust
let handler = NoOpHandler::<MyRole>::new();
```

All operations succeed immediately without side effects.

## Middleware

Middleware wraps handlers to add cross-cutting functionality. Multiple middleware can compose around a single handler.

### Trace

The Trace middleware is located in `rust/choreography/src/effects/middleware/mod.rs`. It logs all operations for debugging. The middleware outputs send, recv, choose, and offer calls with role and message details.

Usage example shows wrapping a handler.

```rust
use rumpsteak_aura_choreography::middleware::Trace;

let base_handler = InMemoryHandler::new(role);
let mut handler = Trace::new(base_handler, "Alice".to_string());
```

Each operation logs before delegating to the inner handler.

### Metrics

The Metrics middleware is located in `rust/choreography/src/effects/middleware/metrics.rs`. It counts operations for monitoring. The middleware tracks send_count, recv_count, choose_count, and offer_count.

Usage example shows metrics collection.

```rust
use rumpsteak_aura_choreography::middleware::Metrics;

let base_handler = InMemoryHandler::new(role);
let mut handler = Metrics::new(base_handler);
// ... execute protocol ...
println!("Sends: {}", handler.send_count());
```

Metrics accumulate over the handler lifetime.

### Retry

The Retry middleware is located in `rust/choreography/src/effects/middleware/retry.rs`. It retries failed operations with exponential backoff. Only send operations are retried since recv changes protocol state.

Usage example configures retry behavior.

```rust
use rumpsteak_aura_choreography::middleware::Retry;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = Retry::new(base_handler, 3, Duration::from_millis(100));
```

The handler retries up to 3 times. Delays are 100ms, 200ms, 400ms using exponential backoff.

### FaultInjection

The FaultInjection middleware is located in `rust/choreography/src/effects/middleware/fault_injection.rs`. It requires the `test-utils` feature. The middleware injects random failures and delays for testing fault tolerance.

Usage example configures fault injection.

```rust
use rumpsteak_aura_choreography::middleware::FaultInjection;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = FaultInjection::new(base_handler)
    .with_failure_rate(0.1)
    .with_delay_range(Duration::from_millis(10), Duration::from_millis(100));
```

Operations randomly fail 10% of the time. Delays range from 10ms to 100ms.

## Composing Middleware

Middleware can stack in layers.

```rust
let handler = InMemoryHandler::new(role);
let handler = Retry::new(handler, 3, Duration::from_millis(100));
let handler = Trace::new(handler, "Alice".to_string());
let handler = Metrics::new(handler);
```

Operations flow through the stack. The order is Metrics to Trace to Retry to InMemory.

## Creating Custom Handlers

Implement `ChoreoHandler` for your transport.

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

Use middleware to add logging, metrics, retries, or fault injection. Middleware works with any handler.

## WASM Considerations

InMemoryHandler and RumpsteakHandler both work in WASM environments. They use futures channels for communication.

For WASM network communication, implement a custom handler. Use web-sys WebSocket or fetch APIs. See [WASM Guide](13_wasm_guide.md) for details.

## Effect Interpretation

Handlers interpret effect programs.

```rust
let program = Program::new()
    .send(Role::Bob, msg)
    .recv::<Response>(Role::Bob)
    .end();

let result = interpret(&mut handler, &mut endpoint, program).await?;
```

The `interpret` function walks the effect tree. It calls handler methods for each operation. The result contains received messages and execution status.
