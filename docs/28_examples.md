# Examples

This document points to the example programs and common usage patterns. Each example demonstrates a specific protocol shape or runtime feature. The choreography DSL examples show global protocol definitions. The testing pattern examples show how to validate protocol behavior in unit and integration tests.

## Example Index

All examples compile against the workspace. Simple linear protocols use the `choreography!` macro. Protocols with recursion, branching, or infinite types use the manual session type API.

Top level examples in `examples/`:

- `three_adder.rs` — three-party sum via `choreography!` macro
- `ring.rs` — three-node ring topology via `choreography!` macro
- `double_buffering.rs` — producer-consumer coordination via `choreography!` macro
- `adder.rs` — recursive two-party adder with Add loop and Bye exit (manual API)
- `alternating_bit.rs` — reliable delivery with ACK branching (manual API)
- `oauth.rs` — three-party authentication with nested choices (manual API)
- `ring_choice.rs` — ring with per-hop branching and infinite types (manual API)
- `client_server_log.rs` — three-party protocol with infinite logging loop (manual API)
- `elevator.rs` — three-role infinite state machine (manual API)
- `fft.rs` — eight-role FFT butterfly network (manual API)
- `async_subtyping.rs` — async-subtyping checks and subtype relation examples
- `bounded_recursion.rs` — bounded recursion strategies with configurable depth
- `wasm-ping-pong/` — browser builds using `wasm-pack`

## Common Patterns

The following patterns cover the core choreography constructs. Each pattern uses the `choreography!` macro with a raw string protocol definition. The macro parses the protocol, validates role declarations, and generates projection code.

### Request Response

```rust
choreography!(r#"
protocol RequestResponse =
  roles Client, Server
  Client
    -> Server : Request of api.Request
  Server
    -> Client : Response of api.Response
"#);
```

The `choreography!` macro parses the protocol string at compile time. Each message line declares a sender, receiver, label, and optional payload type. Projection produces one local session type per role.

### Choice

```rust
choreography!(r#"
protocol ChoicePattern =
  roles Client, Server
  choice at Server
    | Accept ->
        Server
          -> Client : Confirmation
    | Reject ->
        Server
          -> Client : Rejection
"#);
```

Only the deciding role selects the branch. Other roles react to that choice. The `choice at` clause names the selecting participant. Each branch label must be distinct within the choice block.

### Loops

```rust
choreography!(r#"
protocol LoopPattern =
  roles Client, Server
  loop repeat 5
    Client
      -> Server : Request
    Server
      -> Client : Response
"#);
```

Use bounded loops for batch workflows or retries. The `repeat` count sets an upper iteration limit. The body runs sequentially within each iteration.

### Parallel Branches

```rust
choreography!(r#"
protocol ParallelPattern =
  roles Coordinator, Worker1, Worker2
  par
    | Coordinator
        -> Worker1 : Task
    | Coordinator
        -> Worker2 : Task
"#);
```

Parallel branches must be independent in order to remain well formed. Each branch operates on a disjoint set of roles. The runtime executes branches concurrently when possible.

## Testing Patterns

Three handler types support different test scenarios. `InMemoryHandler` is the simplest, operating with in-process channels. `TelltaleHandler` uses `TelltaleSession` pairs for typed bidirectional communication. `RecordingHandler` captures events without executing real transport.

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

`InMemoryHandler::new` creates isolated channels for send-only tests. Use `InMemoryHandler::with_channels` and shared channel maps when a test needs both send and receive. The `interpret` function drives each effect step through the handler.

### Integration Test With TelltaleHandler

```rust
#[tokio::test]
async fn test_session_types() {
    let (alice_session, bob_session) = TelltaleSession::pair();

    let mut alice_ep = TelltaleEndpoint::new(Role::Alice);
    alice_ep.register_session(Role::Bob, alice_session);

    let mut bob_ep = TelltaleEndpoint::new(Role::Bob);
    bob_ep.register_session(Role::Alice, bob_session);

    let mut handler = TelltaleHandler::<Role, Message>::new();
    // run protocol on both endpoints
}
```

This pattern validates the session-based handler without custom transports. The role type must implement both `telltale::Role` and `RoleId`. `TelltaleSession::pair` returns two linked endpoints that relay messages in both directions.

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

Use this to validate retry behavior and error handling. The second argument is the failure probability per operation. Enable this by adding `features = ["test-utils"]` on `telltale-choreography` in test builds.

## Running Examples

Run a single example with Cargo. Each example is a standalone binary that demonstrates the protocol end to end.

```bash
cargo run --example adder
```

This compiles and runs the `adder` example, which demonstrates a simple two-party request response protocol.

The `wasm-ping-pong` example uses its own build script. It produces a browser-loadable WASM module.

```bash
cd examples/wasm-ping-pong
./build.sh
```

See the comments in each example file for setup requirements. For WASM-specific guidance, see [WASM Guide](29_wasm_guide.md).
