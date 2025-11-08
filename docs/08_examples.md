# Examples

## Example Index

### Basic Protocols

adder.rs: Simple addition service with client and server roles.

alternating_bit.rs: Alternating bit protocol for reliable message delivery.

client_server_log.rs: Client-server interaction with logging.

ring.rs: Ring topology with sequential message passing.

### Advanced Protocols

three_adder.rs: Three-party protocol with coordination.

oauth.rs: OAuth authentication flow between client, authorization server, and resource server.

double_buffering.rs: Producer-consumer with double buffering.

elevator.rs: Multi-floor elevator control protocol.

fft.rs: Distributed Fast Fourier Transform computation.

### Choice and Branching

ring_choice.rs: Ring topology with choice points.

choreography.rs: Protocol demonstrating choice constructs.

### WASM

wasm-ping-pong: Browser-based ping-pong protocol. See examples/wasm-ping-pong/README.md for details.

`RumpsteakEndpoint` supports either `register_channel` (SimpleChannel) or
`register_session`. Use `RumpsteakSession::from_sink_stream` when an example
needs to speak over WebSockets or other custom transports.

## Common Patterns

### Request-Response

Client sends request to server. Server processes and sends response back.

```rust
let program = Program::new()
    .send(Role::Server, Request { query: "data" })
    .recv::<Response>(Role::Server)
    .end();
```

Use this pattern for synchronous operations where client waits for server.

### Choice

One role decides between branches. Other roles react to the decision.

```rust
let program = Program::new()
    .choose(Role::Server, Label("accept"))
    .send(Role::Server, Confirmation)
    .end();
```

The chooser calls choose with a label. Other participants use offer to learn the choice.

### Sequential Messages

Send multiple messages in sequence. Each message may depend on previous responses.

```rust
let program = Program::new()
    .send(Role::Peer, Message1)
    .recv::<Ack>(Role::Peer)
    .send(Role::Peer, Message2)
    .recv::<Ack>(Role::Peer)
    .end();
```

This pattern provides acknowledgment after each step.

### Multi-Party Coordination

Three or more roles coordinate. Messages flow between different pairs.

```rust
let program = Program::new()
    .recv::<Offer>(Role::Buyer)
    .send(Role::Seller, Offer)
    .recv::<Response>(Role::Seller)
    .send(Role::Buyer, Response)
    .end();
```

The coordinator role mediates between other participants.

### Loops

Repeat protocol steps. Loop condition determines when to stop.

```rust
let loop_body = Program::new()
    .send(Role::Server, Request)
    .recv::<Response>(Role::Server);

let program = Program::new()
    .with_loop(loop_body, 5)  // Repeat 5 times
    .end();
```

Use loops for batch processing or iterative protocols.

### Parallel Composition

Execute independent protocol branches concurrently.

```rust
let branch1 = Program::new()
    .send(Role::Worker1, Task)
    .end();

let branch2 = Program::new()
    .send(Role::Worker2, Task)
    .end();

let program = Program::new()
    .parallel(vec![branch1, branch2])
    .end();
```

Branches must not conflict. Different recipients allow parallel execution.

### Timeout Protection

Wrap operations with timeouts to handle unresponsive peers.

```rust
let inner = Program::new()
    .recv::<Message>(Role::Peer)
    .end();

let program = Program::new()
    .with_timeout(Role::Self_, Duration::from_secs(5), inner)
    .end();
```

The operation fails with Timeout error if duration elapses.

## Testing Patterns

### Unit Test with InMemoryHandler

Test protocol logic without network:

```rust
#[tokio::test]
async fn test_protocol() {
    let mut handler = InMemoryHandler::new(Role::Alice);
    let program = Program::new()
        .send(Role::Bob, TestMessage)
        .end();
    
    let mut endpoint = ();
    let result = interpret(&mut handler, &mut endpoint, program).await;
    assert!(result.is_ok());
}
```

InMemoryHandler provides fast deterministic testing.

### Integration Test with RumpsteakHandler

Test actual session-typed communication:

```rust
#[tokio::test]
async fn test_session_types() {
    let (alice_ch, bob_ch) = SimpleChannel::pair();
    
    let mut alice_ep = RumpsteakEndpoint::new(Role::Alice);
    alice_ep.register_channel(Role::Bob, alice_ch);
    
    let mut bob_ep = RumpsteakEndpoint::new(Role::Bob);
    bob_ep.register_channel(Role::Alice, bob_ch);
    
    // Run protocol with both endpoints
}
```

This tests real message passing with session type checking.

### Verification with RecordingHandler

Verify protocol execution sequence:

```rust
let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...

let events = handler.events();
assert_eq!(events[0], RecordedEvent::Send { to: Role::Bob, ... });
assert_eq!(events[1], RecordedEvent::Recv { from: Role::Bob, ... });
```

RecordingHandler captures operation history for assertions.

### Fault Injection Testing

Test error handling with FaultInjection middleware:

```rust
let base = InMemoryHandler::new(Role::Alice);
let mut handler = FaultInjection::new(base)
    .with_failure_rate(0.1);

// Protocol should handle 10% random failures
```

Use this to verify retry logic and error recovery.

## Running Examples

Navigate to the example and run with cargo:

```bash
cargo run --example adder
```

Some examples require specific setup. Check comments at the top of each file.

The wasm-ping-pong example has its own build script:

```bash
cd examples/wasm-ping-pong
./build.sh
```

See individual example files for detailed documentation.
