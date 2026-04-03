# Examples

This document points to the example programs and common usage patterns. Each example demonstrates a specific protocol shape or runtime feature. The repo intentionally has two example families:

- projection examples, where `tell!` demonstrates global protocol structure and projected session surfaces
- generated-interface examples, where `effect` declarations are the source of truth for the Rust host boundary

## Example Index

All examples compile against the workspace. Use the projection examples when you
want to inspect session projection and endpoint code. Use the
generated-interface examples when you want to follow the target architecture:
protocol-visible orchestration in Telltale, host realization in Rust.

Protocol examples in `examples/protocols/`:

- `adder.rs`: recursive two-party adder
- `alternating_bit.rs`: reliable delivery with ACK branching
- `double_buffering.rs`: producer-consumer coordination via `tell!`
- `fft.rs`: eight-role FFT butterfly network
- `ring.rs`: three-node ring topology via `tell!`
- `ring_choice.rs`: ring with per-hop branching and infinite types
- `ring_max.rs`: ring maximum with broadcast announcement
- `three_adder.rs`: three-party sum via `tell!`

Effect-boundary examples in `examples/effects/`:

- `client_server_log.rs`: logging decisions at the host boundary
- `commitment_lifecycle.rs`: commitment, profile-driven progress, and agreement/finality metadata
- `elevator.rs`: authority handoff and publication metadata
- `generated_effect_interfaces.rs`: canonical generated Rust effect traits and semantic metadata
- `map_reduce.rs`: structured fan-out/fan-in work with host compute boundaries
- `oauth.rs`: authentication and authorization decisions at the effect boundary
- `reactive_signal.rs`: reactive signal subscription/current-value/publish interface
- `three_buyers.rs`: pricing and affordability decisions at the host boundary
- `travel_agency.rs`: evidence binding, typed failure with case/of, and timeout
- `wasm/`: browser integration via generated effects

Theory examples in `examples/theory/`:

- `async_subtyping.rs`: async-subtyping checks and subtype relation examples
- `bounded_recursion.rs`: bounded recursion strategies with configurable depth

Generated-interface examples in `rust/runtime/examples/`:

- `authority_surface.rs`:inspect `effect` declarations and proof-backed parser metadata
- `telltale_client_server.rs` and `three_party_negotiation.rs`:runtime-oriented examples behind `native-examples`

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
    Client -> Server : Request of api.Request
    Server -> Client : Response of api.Response
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
    choice Server at
      | Accept =>
          Server -> Client : Confirmation
      | Reject =>
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

  type alias ReadyWitness =
  {
    epoch : Int
    issuedBy : Role
  }

  type alias CommitReceipt =
  {
    commitId : String
    publishedBy : Role
  }

  effect Runtime
    authoritative ready : Session -> Result CommitError ReadyWitness
    {
      class : authoritative
      progress : may_block
      region : fragment
      agreement_use : required
      reentrancy : reject_same_fragment
    }
    command publish : ReadyWitness -> Result CommitError CommitReceipt
    {
      class : best_effort
      progress : immediate
      region : session
      agreement_use : required
      reentrancy : allow
    }

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
let ready = effects::runtime::operation("ready").unwrap();
assert!(ready.architecturally_legal());
let presence = effects::Runtime::handle(
    &mut host,
    effects::RuntimeRequest::Ready(effects::Session::new("commit-7")),
);
assert!(matches!(presence, effects::RuntimeOutcome::Ready(Ok(_))));
```

This produces canonical host-facing request/outcome enums, handler traits, and
generated semantic metadata directly from the declared `effect` surface. Use
`Protocol::effects` as the single import boundary. Per-interface metadata lives
under `Protocol::effects::<effect_name_in_snake_case>`. `Protocol::proof_status`
reports which generated proof-backed surfaces are available. File export
remains tooling-only and is no longer the primary developer path.

## Semantic Highlights

When you want a concrete semantic feature, start here:

- commitment: `examples/effects/commitment_lifecycle.rs`
- authority, publication, and materialization: `examples/effects/generated_effect_interfaces.rs`
- structured concurrency: `examples/effects/map_reduce.rs`
- profile-driven progress: `examples/effects/commitment_lifecycle.rs`
- reusable domain agreement profiles: `examples/effects/commitment_lifecycle.rs`
- reactive host boundaries: `examples/effects/reactive_signal.rs`

`commitment_lifecycle.rs` is the repo's explicit example of a domain-defined
agreement scheme similar in shape to Aura's provisional / soft-safe /
finalized model. It demonstrates how downstream systems can keep their own
agreement vocabulary while lowering onto Telltale's generic agreement,
evidence, visibility, and progress core.

## Testing Patterns

For canonical tests, exercise the generated `tell!` surface directly:

- compile-time checks:
  assert on `Protocol::proof_status`
- effect-boundary checks:
  implement `Protocol::effects::*` traits against deterministic host fixtures
- semantic checks:
  assert over `Protocol::commitments`, `Protocol::agreements`, and
  `Protocol::authority`
- protocol-machine checks:
  use the protocol-machine and bridge test suites for replay/parity/runtime
  behavior

Low-level choreography-interpreter tests still exist inside
`rust/runtime/tests/` as implementation coverage for that crate, but they
are not the public testing model that examples should teach.

## Running Examples

Run a single example with Cargo. Each example is a standalone binary that demonstrates the protocol end to end.

```bash
cargo run --example adder
```

This compiles and runs the `adder` example, which demonstrates a simple two-party request response protocol.

The `wasm` example crate uses its own harness. It can build the browser package, run a deterministic Node smoke check, and serve the demo locally.

```bash
cd examples/wasm
./harness.sh run
```

See the comments in each example file for setup requirements. For WASM-specific guidance, see [WASM Guide](804_wasm_guide.md).
