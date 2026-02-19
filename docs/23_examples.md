# Examples

This document points to the example programs and common usage patterns.

## Example Index

Top level examples in `examples/`:

- `adder.rs` for a simple request response protocol
- `alternating_bit.rs` for a reliable message delivery pattern
- `client_server_log.rs` for logging in a client server protocol
- `ring.rs` and `ring_choice.rs` for ring topologies and branching
- `double_buffering.rs` and `elevator.rs` for multi step coordination
- `fft.rs` for distributed computation
- `oauth.rs` for a multi role authentication flow
- `wasm-ping-pong/` for browser builds

Advanced examples live under `examples/advanced_features/` and runnable bundles under `examples/running_examples/`.

## Common Patterns

### Request Response

```rust
choreography!(r#"
protocol RequestResponse =
  roles Client, Server
  Client -> Server : Request
  Server -> Client : Response
"#);
```

Use this pattern when the client waits for a reply before continuing.

### Choice

```rust
choreography!(r#"
protocol ChoicePattern =
  roles Client, Server
  case choose Server of
    Accept ->
      Server -> Client : Confirmation
    Reject ->
      Server -> Client : Rejection
"#);
```

Only the deciding role selects the branch. Other roles react to that choice.

### Loops

```rust
choreography!(r#"
protocol LoopPattern =
  roles Client, Server
  loop repeat 5
    Client -> Server : Request
    Server -> Client : Response
"#);
```

Use bounded loops for batch workflows or retries.

### Parallel Branches

```rust
choreography!(r#"
protocol ParallelPattern =
  roles Coordinator, Worker1, Worker2
  branch
    Coordinator -> Worker1 : Task
  branch
    Coordinator -> Worker2 : Task
"#);
```

Parallel branches must be independent in order to remain well formed.

## Testing Patterns

### Unit Test With InMemoryHandler

```rust
#[tokio::test]
async fn test_send_only() {
    let mut handler = InMemoryHandler::new(Role::Alice);
    let program = Program::new()
        .send(Role::Bob, TestMessage)
        .end();

    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await;
    assert!(result.is_ok());
}
```

Use `InMemoryHandler::with_channels` and shared channel maps when a test needs both send and receive.

### Integration Test With TelltaleHandler

```rust
#[tokio::test]
async fn test_session_types() {
    let (alice_ch, bob_ch) = SimpleChannel::pair();

    let mut alice_ep = TelltaleEndpoint::new(Role::Alice);
    alice_ep.register_channel(Role::Bob, alice_ch);

    let mut bob_ep = TelltaleEndpoint::new(Role::Bob);
    bob_ep.register_channel(Role::Alice, bob_ch);

    let mut handler = TelltaleHandler::<Role, Message>::new();
    // run protocol on both endpoints
}
```

This pattern validates the channel based handler without custom transports. Ensure the role type implements both `telltale::Role` and `RoleId`.

### RecordingHandler

```rust
let handler = RecordingHandler::new(Role::Alice);
let events = handler.events();
```

`RecordingHandler` captures send, recv, choose, and offer events for assertions. It does not generate values, so use it for structural tests.

### Fault Injection

Fault injection is available behind the `test-utils` feature.

```rust
let base = InMemoryHandler::new(Role::Alice);
let mut handler = FaultInjection::new(base, 0.1);
```

Use this to validate retry behavior and error handling.

## Running Examples

Run a single example with Cargo.

```bash
cargo run --example adder
```

The `wasm-ping-pong` example uses its own build script.

```bash
cd examples/wasm-ping-pong
./build.sh
```

See the comments in each example file for setup requirements.
