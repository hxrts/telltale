# Examples

This document points to the example programs and common usage patterns. Each example demonstrates a specific protocol shape or runtime feature. The repo intentionally has two example families:

- projection examples, where `tell!` demonstrates global protocol structure and projected session surfaces
- generated-interface examples, where `effect` declarations are the source of truth for the Rust host boundary

## Example Index

All examples compile against the workspace. Use the projection examples when you
want to inspect session projection and endpoint code. Use the
generated-interface examples when you want to follow the target architecture:
protocol-visible orchestration in Telltale, host realization in Rust.

Top level examples in `examples/`:

- `three_adder.rs` — three-party sum via `tell!`
- `ring.rs` — three-node ring topology via `tell!`
- `double_buffering.rs` — producer-consumer coordination via `tell!`
- `adder.rs` — recursive two-party adder
- `alternating_bit.rs` — reliable delivery with ACK branching
- `oauth.rs` — three-party authentication with nested choices
- `ring_choice.rs` — ring with per-hop branching and infinite types
- `client_server_log.rs` — three-party protocol with infinite logging loop
- `elevator.rs` — three-role infinite state machine
- `fft.rs` — eight-role FFT butterfly network
- `generated_effect_interfaces.rs` — use canonical Rust handler traits and request/outcome enums emitted from `effect` declarations
- `async_subtyping.rs` — async-subtyping checks and subtype relation examples
- `bounded_recursion.rs` — bounded recursion strategies with configurable depth
- `wasm-ping-pong/` — browser builds using `wasm-pack`

Generated-interface examples in `rust/choreography/examples/`:

- `authority_surface.rs` — inspect `effect` declarations and proof-backed parser metadata
- `telltale_client_server.rs` and `three_party_negotiation.rs` — runtime-oriented examples behind `native-examples`

## Common Patterns

The following patterns cover the core protocol constructs for projection
examples. `tell!` parses the DSL at compile time, validates the proof-backed
surface, and emits sessions only when the protocol is session-projectable.

### Request Response

```rust
use telltale::tell;

tell! {
  protocol RequestResponse =
    roles Client, Server
    Client -> Server : Request(api.Request)
    Server -> Client : Response(api.Response)
}
```

Each message line declares a sender, receiver, label, and optional payload type.
Projection produces one local session type per role when
`RequestResponse::proof_status::SESSION_PROJECTABLE` is `true`.

### Choice

```rust
use telltale::tell;

tell! {
  protocol ChoicePattern =
    roles Client, Server
    choice at Server
      | Accept ->
          Server -> Client : Confirmation
      | Reject ->
          Server -> Client : Rejection
}
```

Only the deciding role selects the branch. Other roles react to that choice. The `choice at` clause names the selecting participant. Each branch label must be distinct within the choice block.

### Loops

```rust
use telltale::tell;

tell! {
  protocol LoopPattern =
    roles Client, Server
    loop repeat 5
      Client -> Server : Request
      Server -> Client : Response
}
```

Use bounded loops for batch workflows or retries. The `repeat` count sets an upper iteration limit. The body runs sequentially within each iteration.

### Parallel Branches

```rust
use telltale::tell;

tell! {
  protocol ParallelPattern =
    roles Coordinator, Worker1, Worker2
    par
      | Coordinator -> Worker1 : Task
      | Coordinator -> Worker2 : Task
}
```

Parallel branches must be independent in order to remain well formed. Each branch operates on a disjoint set of roles. The runtime executes branches concurrently when possible.

## Generated Effect Interfaces

Use the generated-interface path when the example needs typed effect boundaries
or richer host/runtime integration. In these examples, the DSL remains the
source of truth and Rust supplies handler implementations directly against the
generated traits.

```rust
use telltale::tell;

tell! {
    type CommitError =
      | NotReady
      | TimedOut

    type alias ReadyWitness = { epoch : Int, issuedBy : Role }
    type alias CommitReceipt = { commitId : String, publishedBy : Role }

    effect Runtime
      authoritative ready : Session -> Result CommitError ReadyWitness
      command publish : ReadyWitness -> Result CommitError CommitReceipt

    protocol CommitFlow uses Runtime =
      roles Coordinator, Worker
      Coordinator -> Worker : Commit
}

use CommitFlow::effects;

struct Host;

impl effects::Runtime for Host {
    fn ready(&mut self, _input: effects::Session) -> Result<effects::ReadyWitness, effects::CommitError> {
        Ok(effects::ReadyWitness { epoch: 7, issued_by: effects::Role::new("Coordinator") })
    }

    fn publish(&mut self, witness: effects::ReadyWitness) -> Result<effects::CommitReceipt, effects::CommitError> {
        Ok(effects::CommitReceipt {
            commit_id: format!("commit-{}", witness.epoch),
            published_by: witness.issued_by,
        })
    }
}

let mut host = Host;
assert_eq!(CommitFlow::proof_status::STRONGEST_TIER, "session_projectable");
let presence = effects::Runtime::handle(
    &mut host,
    effects::RuntimeRequest::Ready(effects::Session::new("commit-7")),
);
assert!(matches!(presence, effects::RuntimeOutcome::Ready(Ok(_))));
```

This produces canonical host-facing request/outcome enums and handler traits
directly from the declared `effect` surface. `Protocol::proof_status` reports
which generated surfaces are available. File export remains tooling-only and is
no longer the primary developer path.

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
