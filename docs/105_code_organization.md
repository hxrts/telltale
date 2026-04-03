# Code Organization

This document describes the current implementation layout of the repository.
It covers workspace structure, crate responsibilities, and the main dependency directions between crates.
For the conceptual system design, see [Architecture](104_architecture.md).

## Workspace Layout

The repository root contains the facade crate, the Cargo workspace definition, the Lean formalization, and the documentation tree.
Most Rust implementation crates live under `rust/`.

```text
telltale/
├── Cargo.toml
├── rust/
│   ├── src/                root facade crate source
│   ├── types/              telltale-types
│   ├── theory/             telltale-theory
│   ├── language/           telltale-language
│   ├── macros/             telltale-macros
│   ├── runtime/            telltale-runtime
│   ├── machine/            telltale-machine
│   ├── simulator/          telltale-simulator
│   ├── bridge/             telltale-bridge
│   ├── transport/          telltale-transport
│   └── lints/              telltale-lints
├── lean/
├── docs/
└── examples/
```

This layout reflects the current workspace member list in the root `Cargo.toml`.
`external-demo` and `external-demo-macros` are excluded from the workspace.
They live at the repository root as separate example crates.

## Dependency Shape

The workspace is organized around a small set of stable directions.
`telltale-types` is the shared foundation crate.
`telltale-language` is the shared choreography frontend.

The main direct dependency directions are:

- `telltale-types` is used by `telltale-theory`, `telltale-language`, `telltale-machine`, `telltale-simulator`, `telltale-runtime`, `telltale-transport`, and the root `telltale` crate.
- `telltale-theory` is used by `telltale-machine`, `telltale-runtime`, `telltale-bridge`, and the root `telltale` crate behind features.
- `telltale-language` is used by `telltale-macros`, `telltale-runtime`, and the root `telltale` crate.
- `telltale-macros` is used by `telltale-runtime` and the root `telltale` crate.
- `telltale-machine` is used by `telltale-simulator`, `telltale-bridge`, and the root `telltale` crate.
- The root `telltale` crate is used by `telltale-runtime` as a facade dependency.
- `telltale-runtime` is used by `telltale-bridge` through optional features and by `telltale-transport`.

The important organizational change is that the shared frontend now lives in `telltale-language`.
`telltale-runtime` is no longer the right crate to describe as the main DSL parser and projection layer.

## Crate Responsibilities

### telltale-types

`telltale-types` is the foundational data-model crate.
It defines `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`, fixed-point numeric support, and content-addressing infrastructure.
It has no dependencies on other workspace crates.

The content-addressing layer is also here.
`DefaultContentHasher` is the central policy alias for content hashing and currently resolves to BLAKE3.
The `sha256` feature enables explicit SHA-256 helper types as an alternative.

### telltale-theory

`telltale-theory` contains pure session-type algorithms.
Its core responsibilities are projection support, merge, duality, well-formedness, bounded recursion strategies, subtyping, semantics, and coherence predicates.
It does not own parsing or runtime execution.

This crate depends only on `telltale-types`.
It is the algorithm layer consumed by the machine, runtime, bridge, and optional root-crate theory features.
Projection memoization uses the content-addressing facilities from `telltale-types`.

### telltale-language

`telltale-language` is the shared choreography frontend.
It owns the DSL AST, parsing, validation, projection to frontend `LocalType`, code generation helpers, effect-interface scaffolding support, and integration helpers such as `compile_choreography(...)` and `CompiledChoreography`.

Downstream integrations that need validated ASTs, projected locals, ordered annotation records, or theory-facing artifact export should start here.
This crate is now the canonical frontend layer for both first-party and downstream integrations.
It depends on `telltale-types` and no other workspace crate.

### telltale-macros

`telltale-macros` provides the procedural macro surface.
It exports `tell!`, `session`, `Role`, `Roles`, and `Message`.
It depends on `telltale-language` for the shared frontend behavior used by the macro expansion path.

The `tell!` macro is the main compile-time DSL entry point for inline choreographies.
It generates the protocol module, typed effect surfaces, and projectable session surfaces where that correspondence exists.
Macro correctness is guarded by operational tests rather than a mechanized proof.

### telltale-machine

`telltale-machine` provides the protocol machine and guest-runtime surfaces.
It compiles `LocalTypeR` into bytecode and executes it with bounded buffers, scheduler policies, observability, and protocol-machine semantic objects.
It is the canonical semantic core used by the simulator and by direct host embeddings.

The main public front doors are `telltale_machine::model` and `telltale_machine::runtime`.
`model` exposes execution, effect, scheduler, state, semantic-object, and transition vocabulary.
`runtime` exposes loading, admission, and runner surfaces such as `CodeImage`, `ProtocolMachine`, `GuestRuntime`, and `OwnedSession`.

### telltale-simulator

`telltale-simulator` wraps the protocol machine with deterministic testing and simulation infrastructure.
It provides runner entry points, `SimulationHarness`, scenario parsing, field/environment hooks, fault injection, network modeling, property checks, checkpoints, replay artifacts, and distributed simulation helpers.

This crate depends directly on `telltale-machine` and `telltale-types`.
It is the preferred test path for third-party implementations of protocol-machine `EffectHandler`.
Its generated-effect helpers exist as adjacent APIs, but the main integration path is still `SimulationHarness`.

### telltale-runtime

`telltale-runtime` is the choreography-layer runtime crate.
It provides the async `ChoreoHandler` path, effect interpretation, topology and transport abstractions, testing utilities, formatting tooling, and other runtime support for generated choreography code.

This crate also re-exports parts of the shared frontend for convenience, but it does not replace `telltale-language` as the canonical frontend layer.
Its `util/` module now contains platform-facing helpers such as spawn, clock, RNG, and synchronization support.
Its `heap/` module now includes a dedicated `encoding.rs` layer for canonical heap bytes and tagged hashing preimages, plus published conformance vectors in `rust/runtime/tests/data/heap_vectors_v1.json`.

### telltale-bridge

`telltale-bridge` is the Rust↔Lean bridge crate.
It provides export, import, schema handling, protocol-machine trace normalization, semantic-object conversion, and runner-driven cross-validation surfaces.
Optional features enable CLI and runner workflows.

This crate depends directly on `telltale-types` and `telltale-machine`.
It also uses `telltale-theory` and `telltale-runtime` behind optional features and in development workflows.

### telltale-transport

`telltale-transport` provides first-party production transport implementations.
Today it is centered on TCP transport support over the choreography-layer transport abstractions from `telltale-runtime`.
It depends on `telltale-runtime` and `telltale-types`.

This crate should be read as a transport implementation layer, not as the main protocol frontend or runtime semantic core.
Its job is to realize transport contracts for deployed choreography-layer systems.

### telltale-lints

`telltale-lints` contains custom linting support built on `syn`, `quote`, and `proc_macro2`.
It is a small support crate and does not currently define central protocol semantics.
Its role is repository-specific static analysis rather than protocol execution.

### telltale

The root `telltale` crate is the facade crate at the repository root.
It re-exports session-core types, the macro surface, selected shared-frontend APIs, and optional theory features.
It also exposes the root session-type library and DSL support used by many examples.

Notably, the root crate now re-exports `compile_choreography(...)`, `compile_choreography_ast(...)`, `CompiledChoreography`, ordered annotation helpers, and `parse_choreography_str(...)`.
This makes the facade crate a reasonable entry point for smaller integrations, while `telltale-language` remains the authoritative frontend crate.

## Selected Workspace Binaries

Some important tooling surfaces are shipped as binaries inside workspace crates.

- `effect-scaffold` in `telltale-runtime` exports generated effect-family files and simulator scaffolds.
- `choreo-fmt` in `telltale-runtime` formats choreography sources and can expose lowering explanations.
- `lean-bridge`, `lean-bridge-exporter`, and `golden` in `telltale-bridge` support validation and bridge workflows.
- `run` and `replay` in `telltale-simulator` support scenario execution and replay.

These binaries are generated surfaces & tooling.
They are not the primary conceptual entry points for the architecture itself.

## Lean Correspondence

The strongest direct constructor correspondence is between `telltale-types` and the foundational Lean session-type definitions.
That shared core covers `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`.
This is the main type-level bridge between Rust and Lean.

The current correspondence table for the shared core is:

| Lean Type | Rust Type | File |
|---|---|---|
| `GlobalType.end` | `GlobalType::End` | `rust/types/src/global.rs` |
| `GlobalType.comm p q bs` | `GlobalType::Comm { sender, receiver, branches }` | `rust/types/src/global.rs` |
| `GlobalType.mu t G` | `GlobalType::Mu { var, body }` | `rust/types/src/global.rs` |
| `GlobalType.var t` | `GlobalType::Var(String)` | `rust/types/src/global.rs` |
| `LocalTypeR.end` | `LocalTypeR::End` | `rust/types/src/local.rs` |
| `LocalTypeR.send q bs` | `LocalTypeR::Send { partner, branches }` | `rust/types/src/local.rs` |
| `LocalTypeR.recv p bs` | `LocalTypeR::Recv { partner, branches }` | `rust/types/src/local.rs` |
| `LocalTypeR.mu t T` | `LocalTypeR::Mu { var, body }` | `rust/types/src/local.rs` |
| `LocalTypeR.var t` | `LocalTypeR::Var(String)` | `rust/types/src/local.rs` |
| `PayloadSort.unit` | `PayloadSort::Unit` | `rust/types/src/global.rs` |
| `Label` | `Label { name, sort }` | `rust/types/src/label.rs` |

Lean still includes a `delegate` constructor in `GlobalType` that is not exposed in the Rust core `GlobalType`.
That remains a known parity gap in the shared foundational type layer.
The larger proof and runtime correspondence story is documented in [Lean Verification](701_lean_verification.md) and [Rust-Lean Bridge and Parity](703_rust_lean_parity.md).

## Related Docs

- [Architecture](104_architecture.md)
- [Theory](103_theory.md)
- [Choreographic DSL](202_choreographic_dsl.md)
- [Content Addressing](801_content_addressing.md)
- [Lean Verification](701_lean_verification.md)
- [Rust-Lean Bridge and Parity](703_rust_lean_parity.md)
