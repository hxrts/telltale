# Examples

## Example Index

### Basic Protocols

The `adder.rs` example shows a simple addition service. It uses client and server roles.

The `alternating_bit.rs` example implements the alternating bit protocol. This provides reliable message delivery.

The `client_server_log.rs` example demonstrates client-server interaction. It includes logging functionality.

The `ring.rs` example shows ring topology. Messages pass sequentially through the ring.

### Advanced Protocols

The `three_adder.rs` example shows a three-party protocol. It includes coordination logic.

The `oauth.rs` example implements OAuth authentication flow. It uses client, authorization server, and resource server roles.

The `double_buffering.rs` example shows producer-consumer pattern. It uses double buffering for efficiency.

The `elevator.rs` example implements multi-floor elevator control. The protocol coordinates elevator movements.

The `fft.rs` example shows distributed Fast Fourier Transform. Computation is distributed across roles.

### Choice and Branching

The `ring_choice.rs` example shows ring topology with choice points. Roles make decisions at each node.

The `choreography.rs` example demonstrates choice constructs. It shows branching patterns.

### WASM

The `wasm-ping-pong` example runs in browsers. It shows browser-based ping-pong protocol. See examples/wasm-ping-pong/README.md for details.

`RumpsteakEndpoint` supports two patterns. Use `register_channel` for `SimpleChannel`. Use `register_session` for custom transports. Call `RumpsteakSession::from_sink_stream` for WebSockets or other transports.

## Common Patterns

### Request-Response

Client sends request to server. Server processes and sends response back.

```rust
choreography! {
    RequestResponse {
        roles: Client, Server
        
        Client -> Server: Request
        Server -> Client: Response
    }
}
```

Use this pattern for synchronous operations. Client waits for server response.

### Choice

One role decides between branches. Other roles react to the decision.

```rust
choreography! {
    ChoicePattern {
        roles: Client, Server
        
        choice Server {
            accept: {
                Server -> Client: Confirmation
            }
            reject: {
                Server -> Client: Rejection
            }
        }
    }
}
```

The deciding role chooses which branch to execute. Other participants react accordingly.

### Sequential Messages

Send multiple messages in sequence. Each message may depend on previous responses.

```rust
choreography! {
    SequentialMessages {
        roles: Client, Server
        
        Client -> Server: Message1
        Server -> Client: Ack
        Client -> Server: Message2
        Server -> Client: Ack
    }
}
```

This pattern provides acknowledgment after each step.

### Multi-Party Coordination

Three or more roles coordinate. Messages flow between different pairs.

```rust
choreography! {
    MultiPartyCoordination {
        roles: Buyer, Coordinator, Seller
        
        Buyer -> Coordinator: Offer
        Coordinator -> Seller: Offer
        Seller -> Coordinator: Response
        Coordinator -> Buyer: Response
    }
}
```

The coordinator role mediates between other participants.

### Loops

Repeat protocol steps. Loop condition determines when to stop.

```rust
choreography! {
    LoopPattern {
        roles: Client, Server
        
        loop (count: 5) {
            Client -> Server: Request
            Server -> Client: Response
        }
    }
}
```

Use loops for batch processing or iterative protocols. This example repeats 5 times.

### Parallel Composition

Execute independent protocol branches concurrently.

```rust
choreography! {
    ParallelPattern {
        roles: Coordinator, Worker1, Worker2
        
        parallel {
            Coordinator -> Worker1: Task
        |
            Coordinator -> Worker2: Task
        }
    }
}
```

Branches must not conflict. Different recipients allow parallel execution.

### Timeout Protection

Use annotations to specify timeouts for handling unresponsive peers.

```rust
choreography! {
    TimeoutPattern {
        roles: Client, Server
        
        [@timeout = 5000]
        Client -> Server: Request
        
        [@timeout = 5000]
        Server -> Client: Response
    }
}
```

The operation fails with timeout error if duration elapses. Timeout annotations are in milliseconds.

## Testing Patterns

### Unit Test with InMemoryHandler

Test protocol logic without network.

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

Test actual session-typed communication.

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

Verify protocol execution sequence.

```rust
let mut handler = RecordingHandler::new(Role::Alice);
// ... execute protocol ...

let events = handler.events();
assert_eq!(events[0], RecordedEvent::Send { to: Role::Bob, ... });
assert_eq!(events[1], RecordedEvent::Recv { from: Role::Bob, ... });
```

RecordingHandler captures operation history for assertions.

### Fault Injection Testing

Test error handling with FaultInjection middleware.

```rust
let base = InMemoryHandler::new(Role::Alice);
let mut handler = FaultInjection::new(base)
    .with_failure_rate(0.1);

// Protocol should handle 10% random failures
```

Use this to verify retry logic and error recovery.

## Running Examples

Navigate to the example and run with cargo.

```bash
cargo run --example adder
```

Some examples require specific setup. Check comments at the top of each file.

The wasm-ping-pong example has its own build script.

```bash
cd examples/wasm-ping-pong
./build.sh
```

See individual example files for detailed documentation.
