# Getting Started

## Installation

Choose dependencies based on the integration path you need.
For most application code using the compile-time DSL, start with the facade crate.

```toml
[dependencies]
telltale = "11.0.0"
```

This gives you the root session-type surface and the `tell!` macro.
Add other crates only when you need a lower-level integration path.

## Which Crate Should You Use

Use this table to pick the right entry point.

| If you need | Use |
|---|---|
| facade APIs plus the `tell!` macro | `telltale` |
| runtime parsing, validated ASTs, projection, and integration artifacts | `telltale-language` |
| async choreography handlers and topology/runtime support | `telltale-runtime` |
| pure theory algorithms | `telltale-theory` |
| protocol-machine execution in a host runtime | `telltale-machine` |
| deterministic simulation and host-handler testing | `telltale-simulator` |
| Lean JSON import, export, and validation tools | `telltale-bridge` |
| production choreography transports | `telltale-transport` |

The important split is between the shared frontend and the execution layers.
`telltale-language` is the shared frontend.
`telltale-runtime` and `telltale-machine` are different execution paths.

## Understanding the Crates

`telltale-types` contains the core protocol data model.
It defines `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`, and content-addressing support.
Lean still includes a `delegate` constructor that is not exposed in the Rust core `GlobalType`.

`telltale-language` is the shared choreography frontend.
It owns the AST, parser, validation, projection to frontend `LocalType`, ordered annotation extraction, and integration helpers such as `compile_choreography(...)`.
Use this crate when you need to parse or inspect DSL at runtime without going through macros.

`telltale-runtime` is the choreography-layer runtime.
It provides async `ChoreoHandler` integration, topology support, testing helpers, and tooling such as `choreo-fmt` and `effect-scaffold`.
`telltale-machine` provides the protocol machine and guest-runtime execution surfaces.

`telltale-simulator` wraps the protocol machine with deterministic middleware for testing.
`telltale-bridge` supports Rust↔Lean conversion and validation.
`telltale-transport` provides first-party transport implementations for choreography-layer systems.

## Feature Flags

The workspace uses feature flags to control optional algorithms and target support.
The root crate keeps its default surface small.

#### `telltale`

| Feature | Default | Description |
|---|---|---|
| `test-utils` | no | testing utilities |
| `wasm` | no | WebAssembly support |
| `theory` | no | enable `telltale-theory` re-exports |
| `theory-async-subtyping` | no | enable asynchronous subtyping helpers |
| `theory-bounded` | no | enable bounded recursion helpers |
| `full` | no | enable all optional root features |

#### `telltale-theory`

| Feature | Default | Description |
|---|---|---|
| `projection` | yes | global-to-local projection |
| `duality` | yes | dual type computation |
| `merge` | yes | local merge operations |
| `well-formedness` | yes | theory validation predicates |
| `bounded` | yes | bounded recursion strategies |
| `async-subtyping` | yes | asynchronous subtyping |
| `sync-subtyping` | yes | synchronous subtyping |
| `semantics` | yes | async step semantics |
| `coherence` | yes | coherence predicates |
| `full` | no | enable all optional theory features |

#### `telltale-runtime`

| Feature | Default | Description |
|---|---|---|
| `test-utils` | no | runtime testing utilities |
| `wasm` | no | WebAssembly support |
| `native-cli` | no | build `choreo-fmt` and `effect-scaffold` |
| `native-examples` | no | build runtime examples that require native tooling |

#### `telltale-bridge`

| Feature | Default | Description |
|---|---|---|
| `runner` | yes | enable Lean runner support |
| `cli` | no | build the main bridge CLI |
| `exporter` | no | build the choreography exporter binary |
| `golden` | no | build the golden-file CLI |

### Minimal Root Dependency

```toml
telltale = { version = "11.0.0", default-features = false }
```

This keeps the dependency surface small while preserving the core facade crate.

### Root Crate With Theory Support

```toml
telltale = { version = "11.0.0", features = ["theory"] }
```

This adds the theory re-exports to the facade crate.

### Runtime CLI Tooling

```toml
telltale-runtime = { version = "11.0.0", features = ["native-cli"] }
```

Enable this when you want binaries such as `choreo-fmt` or `effect-scaffold`.
It is not required for normal library usage.

## First Protocol With `tell!`

For compile-time protocol definitions, `tell!` is the main public entry point.

```rust
use telltale::tell;

tell! {
  protocol PingPong =
    roles Alice, Bob
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}

assert!(PingPong::proof_status::SESSION_PROJECTABLE);
```

This defines a simple two-role protocol.
The macro generates the protocol module and, when the protocol is projectable, the session surfaces for that protocol.

## Runtime Parsing Without Macros

Use the shared frontend when protocol text is loaded at runtime or when another tool needs validated artifacts.

```rust
use telltale_language::compile_choreography;

let compiled = compile_choreography(
    "protocol PingPong =\n  roles Alice, Bob\n  Alice -> Bob : Ping\n  Bob -> Alice : Pong\n",
)?;

let local_types = compiled.try_local_type_r_map()?;
let global_type = compiled.try_global_type()?;
```

This path parses, validates, and projects the choreography once.
It is the right entry point for downstream integrations that need AST access, ordered annotations, or theory-facing artifacts.

## Core Concepts

### Choreographies

A choreography describes the protocol from a global viewpoint.
Projection turns that global description into per-role local behavior.
This is the main abstraction behind the Telltale DSL.

### Roles

Roles are the participants in the protocol.
Each role sends and receives messages according to its projected local type.
Generated session surfaces enforce those obligations at the type level when projection succeeds.

### Messages

Messages are the data exchanged between roles.
At the choreography layer, message payloads typically use `serde` serialization.
At the protocol-machine layer, host integration works through typed effect requests and outcomes instead.

### Handler Boundaries

Telltale exposes two main handler surfaces.
Use `ChoreoHandler` for generated choreography code in `telltale-runtime`.
Use `EffectHandler` for protocol-machine host integration in `telltale-machine`.

If you implement protocol-machine `EffectHandler`, validate it through `SimulationHarness` in `telltale-simulator`.
That is the supported deterministic test path for host integrations.

## Related Docs

- [Architecture](104_architecture.md)
- [Code Organization](105_code_organization.md)
- [Choreographic DSL](202_choreographic_dsl.md)
- [Choreography Effect Handlers](301_effect_handlers.md)
- [Effect Handlers and Session Types](303_effect_session_bridge.md)
- [Simulation Overview](501_simulation_overview.md)
