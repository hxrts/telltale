# API Reference

This document provides a high level map of the public APIs. For full signatures, use the crate level `lib.rs` files and generated rustdoc.

## Core Crates

### `telltale`

Core session type library with channel primitives and macros.

Key exports:

- `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`
- `Role`, `Roles`, `Message` derive macros
- Channel traits and session state types

See `rust/src/lib.rs` for the full list of re exports.

### `telltale-types`

Type definitions shared across the stack.

Key exports:

- `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`
- `ContentId`, `Sha256Hasher`, `ContentStore`, `KeyedContentStore`
- Merge and projection helpers in `rust/types/src`

See `rust/types/src/lib.rs` for re exports.

### `telltale-choreography`

Choreographic DSL, projection, and effect execution.

Key exports:

- AST types: `Choreography`, `Protocol`, `Role`, `MessageType`
- Effect system: `Program`, `ProgramBuilder`, `interpret`, `interpret_extensible`
- Handlers: `ChoreoHandler`, `InMemoryHandler`, `TelltaleHandler`
- Topology: `Topology`, `TopologyHandler`, `TransportType`
- Heap: `Heap`, `Resource`, `MerkleTree`, `HeapCommitment`
- Extensions: `ExtensionRegistry`, `GrammarExtension`, `ProtocolExtension`

See `rust/choreography/src/lib.rs` for the full export surface.

### `telltale-vm`

Bytecode VM for executing projected local types.

Key exports:

- `VM`, `VMConfig`, `SchedPolicy`, `SimClock`
- `Instr`, `Value`, `SessionStore`, `SessionId`
- Effect boundary: `EffectHandler`, `SendDecision`, `AcquireDecision`
- Effect trace and replay: `RecordingEffectHandler`, `ReplayEffectHandler`, `EffectTraceEntry`
- Topology and output metadata: `TopologyPerturbation`, `OutputConditionHint`
- `VMBackend` and `NestedVMHandler`

See `rust/vm/src/lib.rs` for the full API.
See [Effect Handlers and Session Types](10_effect_session_bridge.md) for integration-boundary guidance.

### `telltale-simulator`

Simulation utilities built on the VM.

Key exports:

- `Trace` and `StepRecord` in `rust/simulator/src/trace.rs`
- Runner functions in `rust/simulator/src/runner.rs`
- Scenario types in `rust/simulator/src/scenario.rs`

### `telltale-lean-bridge`

Lean bridge for JSON export, import, and validation.

Key exports:

- `global_to_json`, `local_to_json`, `json_to_global`, `json_to_local`
- `LeanRunner`, `Validator`, `ValidationResult`

See [Lean-Rust Bridge](19_lean_rust_bridge.md) for details.

## Guidance

When you need an exact signature, open the crate `lib.rs` and follow re exports to the module definition. This keeps the reference accurate as the API evolves.
