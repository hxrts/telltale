# API Reference

This document provides a high level map of the public APIs. For full signatures, use the crate level `lib.rs` files and generated rustdoc.

## Core Crates

### `telltale`

Core session type library with channel primitives and macros.

Key exports:

- `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`
- `Role`, `Roles`, `Message` derive macros
- Channel traits and session state types

See `rust/src/lib.rs` for the full list of re-exports.

### `telltale-types`

Type definitions shared across the stack.

Key exports:

- `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`
- `ContentId`, `Sha256Hasher`, `ContentStore`, `KeyedContentStore`
- Merge and projection helpers in `rust/types/src`

See `rust/types/src/lib.rs` for re-exports.

### `telltale-choreography`

Choreographic DSL, projection, and effect execution.

Key exports:

- AST types: `Choreography`, `Protocol`, `Role`, `MessageType`
- Effect system: `Program`, `ProgramBuilder`, `interpret`
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
- `VMBackend` and `NestedVMHandler`

Module access (not re-exported at crate root):
- Effect boundary: `telltale_vm::effect::EffectHandler`, `SendDecision`, `AcquireDecision`
- Effect trace: `telltale_vm::effect::RecordingEffectHandler`, `ReplayEffectHandler`
- Loader: `telltale_vm::loader::CodeImage`

See `rust/vm/src/lib.rs` for the full API.
See [Effect Handlers and Session Types](11_effect_session_bridge.md) for integration-boundary guidance.

### `telltale-simulator`

Simulation utilities built on the VM.

Key exports:

- Harness surface in `rust/simulator/src/harness.rs`:
  `HostAdapter`, `DirectAdapter`, `MaterialAdapter`, `HarnessSpec`, `HarnessConfig`, `SimulationHarness`

Module access (not re-exported at crate root):
- `telltale_simulator::trace::Trace`, `StepRecord`
- `telltale_simulator::runner::run`, `run_concurrent`, `run_with_scenario`, `ChoreographySpec`
- `telltale_simulator::scenario::Scenario`
- Contract checks in `rust/simulator/src/contracts.rs`:
  `ContractCheckConfig`, `ContractCheckReport`, `evaluate_contracts`, `assert_contracts`
- Preset helpers in `rust/simulator/src/presets.rs`
- Material handlers and factory:
  `IsingHandler`, `HamiltonianHandler`, `ContinuumFieldHandler`, `handler_from_material`
  in `rust/simulator/src/material_handlers/`

### `telltale-lean-bridge`

Lean bridge for JSON export, import, and validation.

Key exports:

- `global_to_json`, `local_to_json`, `json_to_global`, `json_to_local`
- `LeanRunner`, `Validator`, `ValidationResult`

See [Lean-Rust Bridge](24_lean_rust_bridge.md) for details.

## Guidance

When you need an exact signature, open the crate `lib.rs` and follow re-exports to the module definition. This keeps the reference accurate as the API evolves.
