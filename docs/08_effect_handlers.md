# Effect Handlers

## Overview

The effect handler system decouples protocol logic from transport implementation. Handlers interpret choreographic effects into actual communication operations.

A protocol executes by calling handler methods for each operation. Different handlers provide different execution strategies. Protocol code remains unchanged.

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
use telltale_choreography::InMemoryHandler;

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

### TelltaleHandler

The TelltaleHandler is located in `rust/choreography/src/effects/handlers/telltale.rs`. It provides production-ready session-typed channels. The implementation uses the core Telltale library for type-safe communication.

This handler enforces session types at runtime. It provides strong guarantees about protocol compliance.

See [Using Telltale Handlers](09_telltale_handler.md) for complete documentation.

### RecordingHandler

The RecordingHandler is located in `rust/choreography/src/effects/handlers/recording.rs`. It records all operations for verification and testing. The handler stores a log of send, recv, choose, and offer calls.

Basic usage creates a recording handler.

```rust
use telltale_choreography::RecordingHandler;

let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...
let events = handler.events();
assert_eq!(events[0], RecordedEvent::Send { to: Role::Bob, ... });
```

The recorded events can be inspected in tests to verify protocol behavior.

### NoOpHandler

The NoOpHandler is located in `rust/choreography/src/effects/handler.rs`. It implements send and choose as no-ops and returns errors for recv and offer. This is useful for testing protocol structure without actual communication.

```rust
let handler = NoOpHandler::<MyRole>::new();
```

Send and choose succeed immediately without side effects. Recv and offer return transport errors.

## Middleware

Middleware wraps handlers to add cross-cutting functionality. Multiple middleware can compose around a single handler.

### Trace

The Trace middleware is located in `rust/choreography/src/effects/middleware/trace.rs`. It logs all operations for debugging. The middleware outputs send, recv, choose, and offer calls with role and message details.

Usage example shows wrapping a handler.

```rust
use telltale_choreography::middleware::Trace;

let base_handler = InMemoryHandler::new(role);
let mut handler = Trace::with_prefix(base_handler, "Alice");
```

Each operation logs before delegating to the inner handler.

### Metrics

The Metrics middleware is located in `rust/choreography/src/effects/middleware/metrics.rs`. It counts operations for monitoring. The middleware tracks send_count, recv_count, choose_count, and offer_count.

Usage example shows metrics collection.

```rust
use telltale_choreography::middleware::Metrics;

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
use telltale_choreography::middleware::Retry;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = Retry::with_config(base_handler, 3, Duration::from_millis(100));
```

The handler retries up to 3 times. Delays are 100ms, 200ms, 400ms using exponential backoff.

### FaultInjection

The FaultInjection middleware is located in `rust/choreography/src/effects/middleware/fault_injection.rs`. It requires the `test-utils` feature. The middleware injects random failures and delays for testing fault tolerance.

Usage example configures fault injection.

```rust
use telltale_choreography::middleware::FaultInjection;
use std::time::Duration;

let base_handler = InMemoryHandler::new(role);
let mut handler = FaultInjection::new(base_handler, 0.1)
    .with_delays(Duration::from_millis(10), Duration::from_millis(100));
```

Operations randomly fail 10% of the time. Delays range from 10ms to 100ms.

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

Use TelltaleHandler for production deployments with session type guarantees.

Use RecordingHandler for test verification and debugging.

Use NoOpHandler for protocol structure testing.

Use middleware to add logging, metrics, retries, or fault injection. Middleware works with any handler.

## WASM Considerations

InMemoryHandler and TelltaleHandler both work in WASM environments. They use futures channels for communication.

For WASM network communication, implement a custom handler. Use web-sys WebSocket or fetch APIs. See [WASM Guide](21_wasm_guide.md) for details.

## Role Family Resolution

For protocols with parameterized roles (wildcards and ranges), use `ChoreographicAdapter` for role family resolution.

### ChoreographicAdapter Trait

The adapter trait provides methods for resolving role families at runtime.

```rust
pub trait ChoreographicAdapter: Sized {
    type Role: RoleId;
    type Error;

    /// Resolve all instances of a parameterized role family.
    fn resolve_family(&self, family: &str) -> Result<Vec<Self::Role>, Self::Error>;

    /// Resolve a range of role instances [start, end).
    fn resolve_range(&self, family: &str, start: u32, end: u32)
        -> Result<Vec<Self::Role>, Self::Error>;

    /// Get the number of instances in a role family.
    fn family_size(&self, family: &str) -> Result<usize, Self::Error>;

    /// Broadcast a message to all roles in the list.
    async fn broadcast<M: Message>(&mut self, to: &[Self::Role], msg: M)
        -> Result<(), Self::Error>;

    /// Collect messages from all roles in the list.
    async fn collect<M: Message>(&mut self, from: &[Self::Role])
        -> Result<Vec<M>, Self::Error>;
}
```

These methods resolve role families and support fan out and fan in messaging. Generated code uses them when a protocol includes wildcard or range roles.

### TestAdapter for Role Families

The `TestAdapter` implements `ChoreographicAdapter` for testing protocols with role families.

```rust
use telltale_choreography::runtime::test_adapter::TestAdapter;

// Create adapter with configured role family
let witnesses: Vec<Role> = (0..5).map(Role::Witness).collect();
let adapter = TestAdapter::new(Role::Coordinator)
    .with_family("Witness", witnesses);

// Resolve all witnesses
let all = adapter.resolve_family("Witness")?;  // 5 witnesses

// Resolve subset for threshold operations
let threshold = adapter.resolve_range("Witness", 0, 3)?;  // 3 witnesses

// Get family size
let size = adapter.family_size("Witness")?;  // 5
```

`TestAdapter` keeps role families in memory and is intended for local tests.

### Broadcast and Collect

For one-to-many and many-to-one communication patterns:

```rust
// Broadcast to all witnesses
let witnesses = adapter.resolve_family("Witness")?;
adapter.broadcast(&witnesses, SigningRequest { ... }).await?;

// Collect responses from threshold
let threshold = adapter.resolve_range("Witness", 0, 3)?;
let responses: Vec<PartialSignature> = adapter.collect(&threshold).await?;
```

Use these helpers for one to many and many to one exchanges in role family protocols.

### Execution Hints

Annotations like `@parallel` and `@min_responses(N)` control how broadcast and collect operations execute. These are deployment hints, not protocol semantics. They affect code generation without changing the session type.

```
@parallel Coordinator -> Witness[*] : SignRequest
@min_responses(3) Witness[*] -> Coordinator : PartialSignature
```

The `@parallel` annotation causes generated code to use `futures::future::join_all()` for concurrent execution instead of sequential iteration.

The `@min_responses(N)` annotation generates threshold checking. The collect operation succeeds if at least N responses arrive. Fewer responses result in an `InsufficientResponses` error.

Execution hints are extracted from annotations and passed separately to code generation. This keeps the `LocalType` pure for Lean verification while enabling runtime optimizations.

```rust
use telltale_choreography::ast::{ExecutionHints, ChoreographyWithHints};

// Extract hints from a parsed choreography
let with_hints = ChoreographyWithHints::from_choreography(choreography);

// Hints are available for codegen
let hints = &with_hints.hints;
if hints.is_parallel(&path) {
    // Generate parallel code
}
```

Default behavior without hints is sequential execution with all responses required.

### Topology Validation

Role family constraints can be validated against topology configuration.

```rust
use telltale_choreography::topology::Topology;

let config = r#"
    topology Prod for Protocol {
        role_constraints {
            Witness: min = 3, max = 10
        }
    }
"#;

let topology = Topology::parse(config)?.topology;

// Validate resolved family meets constraints
let count = adapter.family_size("Witness")?;
topology.validate_family("Witness", count)?;
```

Run this check during initialization to ensure deployment configuration matches the resolved family size.

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
