# Choreography Effect Handlers

## Overview

This page documents the choreography-layer handler surface in `telltale-runtime`.
This surface is `ChoreoHandler`.
For protocol-machine host integration, see [Effect Handlers and Session Types](303_effect_session_bridge.md).

Effect interfaces are the typed operational vocabulary between the protocol machine and the world. They realize commitment conservation: every effect is a tracked commitment that must resolve to a terminal class. See [Conservation Framework](102_conservation_framework.md) for the full design philosophy.

`ChoreoHandler` decouples protocol logic from transport implementation at the choreography layer. Handlers interpret choreographic effects into concrete communication operations. Protocol code remains unchanged across handlers. The effect runtime normalizes `Parallel` effects to deterministic declaration order.

## Handler Domains

The effect system distinguishes two handler domains. Internal handlers are Telltale-owned and realize scheduling, dispatch, batching, replay, and simulation. External handlers are guest-runtime-facing and realize storage, network, domain checks, and other host integrations. Both domains interpret the same typed effect interfaces. Handlers may realize operational behavior, but they do not directly mutate semantic state.

## Boundary Selection

Choose the handler surface by integration level.

| Use case | Handler surface |
|---|---|
| Generated choreography code over typed messages | `ChoreoHandler` |
| Protocol-machine bytecode execution in a host runtime | `EffectHandler` |

`EffectHandler` is the integration boundary for third-party runtimes.
`ChoreoHandler` is the integration boundary for async choreography transports.

## Protocol-Machine Handler Test Path

Projects that implement `EffectHandler` should validate behavior in `telltale-simulator`.
Use `SimulationHarness` with `DirectAdapter` for host handlers.
Use `FieldAdapter` when the scenario should select the handler from built-in field parameters.

```rust
let adapter = DirectAdapter::new(&handler);
let harness = SimulationHarness::new(&adapter);
let result = harness.run(&spec)?;
```

This test path runs the same protocol-machine callback surface that production execution uses. Add `assert_contracts` checks to make replay and trace guarantees explicit in CI.

## ChoreoHandler Trait

All handlers implement this trait.

```rust
pub trait ChoreoHandler: Send {
    type Role: RoleId;
    type Endpoint: Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> ChoreoResult<()>;

    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> ChoreoResult<M>;

    async fn choose(
        &mut self, ep: &mut Self::Endpoint, who: Self::Role,
        label: <Self::Role as RoleId>::Label
    ) -> ChoreoResult<()>;

    async fn offer(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> ChoreoResult<<Self::Role as RoleId>::Label>;

    async fn with_timeout<F, T>(
        &mut self, ep: &mut Self::Endpoint, at: Self::Role, dur: Duration, body: F
    ) -> ChoreoResult<T>
    where
        F: Future<Output = ChoreoResult<T>> + Send;
}
```

The trait defines send, receive, choice, and timeout operations.
It also provides default `broadcast` and `parallel_send` helpers.

The `send` method transmits a message to another role. The `recv` method waits for a message from another role. The `choose` method makes a branch selection. The `offer` method receives a branch selection.
Nested branch, loop, timeout, and parallel interpretation returns non-duplicated receive traces.

The `Endpoint` associated type holds connection state. Different handlers use different endpoint types.

### Send bounds and portability

The trait requires messages to be `Send`. The `send` method requires `Serialize + Send + Sync`. The `recv` method requires `DeserializeOwned + Send`. Handler futures require `F: Future + Send` in `with_timeout`.

This matches the requirements of target runtimes. Native targets use tokio. WASM targets use single-thread executors. The bounds keep middleware stacks interchangeable between single-threaded and multi-threaded deployments.

Code written for browsers compiles unchanged for native binaries. Work can move across threads transparently.

## Built-in Handlers

### InMemoryHandler

The InMemoryHandler is located in `rust/runtime/src/effects/handlers/in_memory.rs`. It provides fast local message passing for testing. The implementation uses futures channels internally.

Basic usage creates a handler for a single role.

```rust
use telltale_runtime::InMemoryHandler;

let mut handler = InMemoryHandler::new(Role::Alice);
```

This creates an Alice handler.

For coordinated testing between roles, use shared channels.

```rust
let channels = Arc::new(Mutex::new(BTreeMap::new()));
let choice_channels = Arc::new(Mutex::new(BTreeMap::new()));

let alice = InMemoryHandler::with_channels(Role::Alice, channels.clone(), choice_channels.clone());
let bob = InMemoryHandler::with_channels(Role::Bob, channels.clone(), choice_channels.clone());
```

The shared channels enable communication between handlers in the same process.

### TelltaleHandler

The TelltaleHandler is located in `rust/runtime/src/effects/handlers/telltale.rs`. It provides production-ready session-typed channels. The implementation uses the core Telltale library for type-safe communication.

This handler enforces session types at runtime. It provides strong guarantees about protocol compliance.

See [Using Telltale Handlers](302_telltale_handler.md) for complete documentation.

### RecordingHandler

The RecordingHandler is located in `rust/runtime/src/effects/handlers/recording.rs`. It records all operations for verification and testing. The handler stores a log of send, recv, choose, and offer calls.

Basic usage creates a recording handler.

```rust
use telltale_runtime::RecordingHandler;

let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...
let events = handler.events();
assert!(matches!(events[0], RecordedEvent::Send { from: Role::Alice, to: Role::Bob, .. }));
```

The recorded events can be inspected in tests to verify protocol behavior.

### NoOpHandler

The NoOpHandler is located in `rust/runtime/src/effects/handler.rs`. It implements send and choose as no-ops and returns errors for recv and offer. This is useful for testing protocol structure without actual communication.

```rust
let handler = NoOpHandler::<MyRole>::new();
```

Send and choose succeed immediately without side effects. Recv and offer return transport errors.

## Middleware

Middleware wraps handlers to add cross-cutting functionality. Multiple middleware can compose around a single handler.

### Trace

The Trace middleware is located in `rust/runtime/src/effects/middleware/trace.rs`. It logs all operations for debugging. The middleware outputs send, recv, choose, and offer calls with role and message details.

Usage example shows wrapping a handler.

```rust
use telltale_runtime::Trace;

let base_handler = InMemoryHandler::new(role);
let mut handler = Trace::with_prefix(base_handler, "Alice");
```

Each operation logs before delegating to the inner handler.

### Metrics

The Metrics middleware is located in `rust/runtime/src/effects/middleware/metrics.rs`. It counts operations for monitoring. The middleware tracks `send_count`, `recv_count`, and `error_count`.

Usage example shows metrics collection.

```rust
use telltale_runtime::Metrics;

let base_handler = InMemoryHandler::new(role);
let mut handler = Metrics::new(base_handler);
// ... execute protocol ...
println!("Sends: {}", handler.send_count());
```

Metrics accumulate over the handler lifetime.

### Retry

The Retry middleware is located in `rust/runtime/src/effects/middleware/retry.rs`. It retries failed operations with exponential backoff. Only send operations are retried since recv changes protocol state.

Usage example configures retry behavior.

```rust
use telltale_runtime::Retry;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = Retry::with_config(base_handler, 3, Duration::from_millis(100));
```

The handler retries up to 3 times. Delays are 100ms, 200ms, 400ms using exponential backoff.

### FaultInjection

The FaultInjection middleware is located in `rust/runtime/src/effects/middleware/fault_injection.rs`. It requires the `test-utils` feature. The middleware injects random failures and delays for testing fault tolerance.

Usage example configures fault injection.

```rust
use telltale_runtime::effects::middleware::FaultInjection;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = FaultInjection::new(base_handler, 0.1)
    .with_delays(Duration::from_millis(10), Duration::from_millis(100));
```

Send operations randomly fail 10% of the time. Delays range from 10ms to 100ms. Fault injection only affects `send` operations. The `recv`, `choose`, and `offer` methods delegate directly to the inner handler.

## Composing Middleware

Middleware can stack in layers.

```rust
let handler = InMemoryHandler::new(role);
let handler = Retry::with_config(handler, 3, Duration::from_millis(100));
let handler = Trace::with_prefix(handler, "Alice");
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
    ) -> ChoreoResult<()> {
        let conn = self.connections.get_mut(&to)?;
        let bytes = bincode::serialize(msg)?;
        conn.send(bytes).await?;
        Ok(())
    }

    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> ChoreoResult<M> {
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

Use TelltaleHandler for production deployments with session type guarantees.

Use RecordingHandler for test verification and debugging.

Use NoOpHandler for protocol structure testing.

Use middleware to add logging, metrics, retries, or fault injection. Middleware works with any handler.

## WASM Considerations

InMemoryHandler and TelltaleHandler both work in WASM environments. They use futures channels for communication.

For WASM network communication, implement a custom handler. Use web-sys WebSocket or fetch APIs. See [WASM Guide](804_wasm_guide.md) for details.

## Parameterized Roles

Parameterized roles remain a choreography-level feature of the DSL and AST. Projection and interpretation still require concrete role values at execution time. Wildcard, symbolic, and unresolved range forms are not interpreted directly by `ChoreoHandler`. Resolve participant sets during choreography construction or initialization, then build effect programs over concrete `RoleId` values.

Topology constraints validate concrete deployments against role family bounds.

```rust
use telltale_runtime::topology::{Topology, parse_topology};

let config = r#"
    topology Prod for Protocol {
        role_constraints {
            Witness: min = 3, max = 10
        }
    }
"#;

let topology = parse_topology(config)?.topology;
topology.validate_family("Witness", 5)?;
```

Run this check before execution to ensure the concrete participant set matches deployment expectations.

## Effect Interpretation

Handlers interpret the protocol-machine and generated effect boundary. For
normal application code, start from `tell!`, implement the generated
`Protocol::effects::*` traits, and let the protocol-machine/runtime drive the
requests. The lower-level choreography interpreter remains an internal
implementation surface.
