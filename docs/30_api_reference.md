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
- Merge helpers (`merge`, `merge_all`, `can_merge`) and canonical-serialization utilities

See `rust/types/src/lib.rs` for re-exports.

### `telltale-theory`

Session-type algorithms and executable theory checks.

Key exports:

- Projection: `project`, `project_all`, `MemoizedProjector`
- Merge, duality, well-formedness, and semantics checks
- Subtyping surfaces (feature-gated): `async_subtype`, `sync_subtype`

See `rust/theory/src/lib.rs` for the complete feature-gated API.

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

### `telltale-machine`

Protocol-machine and guest-runtime surfaces for executing projected local types.

Canonical public modules:

- `telltale_machine::model`
- `telltale_machine::runtime`
- `telltale_machine::semantics`

Key exports:

- `ProtocolMachine`, `ProtocolMachineConfig`, `GuestRuntime`, `SchedPolicy`, `SimClock`
- `Instr`, `Value`, `SessionStore`, `SessionId`
- `OwnedSession`, `EffectHandler`, and `NestedProtocolMachineHandler`
- canonical semantic objects:
  `OperationInstance`, `OutstandingEffect`, `SemanticHandoff`,
  `TransformationObligation`,
  `AuthoritativeRead`, `ObservedRead`, `MaterializationProof`,
  `CanonicalHandle`, `PublicationEvent`, `ProgressContract`,
  `ProgressTransition`,
  `ProtocolMachineSemanticObjects`
- runtime introspection:
  `operation_instances()`, `outstanding_effects()`, `semantic_objects()`,
  `progress_contracts()`, `progress_transitions()`, `publication_events()`,
  `require_authoritative_read()`,
  `require_canonical_handle()`, `semantic_audit_log()`,
  `canonical_replay_fragment()`

`GuestRuntime` is the Telltale-owned runtime instantiated around the protocol
machine. `EffectHandler` is the host-runtime boundary implemented by embedders
and simulators.

Module access (not re-exported at crate root):
- Effect boundary:
  `telltale_machine::model::effects::EffectHandler`, `EffectRequest`, `EffectOutcome`,
  `EffectInterfaceMetadata`, `EffectExchangeRecord`, `SendDecision`, `SendDecisionInput`
- Effect trace: `telltale_machine::model::effects::RecordingEffectHandler`, `ReplayEffectHandler`
- Loader: `telltale_machine::runtime::loader::CodeImage`
- Runtime runner: `telltale_machine::runtime::runner::{ProtocolMachine, GuestRuntime, StepResult, RunStatus}`
- Semantics: `telltale_machine::semantics::exec::{ExecResult, ExecStatus, StepPack}`

See `rust/machine/src/lib.rs` for the full API.
See [Effect Handlers and Session Types](11_effect_session_bridge.md) for integration-boundary guidance.

### `telltale-simulator`

Simulation utilities built on the protocol machine.

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

### `telltale-bridge`

Lean bridge for JSON export, import, and validation.

Key exports:

- `global_to_json`, `local_to_json`, `json_to_global`, `json_to_local`
- `LeanRunner`, `Validator`, `ValidationResult`
- `ProtocolMachineSemanticObjects` and semantic-object schema helpers

See [Lean-Rust Bridge](24_lean_rust_bridge.md) for details.

### `telltale-transport`

Production transport implementations for choreography topologies.

Key exports:

- `TcpTransport`, `TcpTransportConfig`, `TransportState`
- Resolver and factory surfaces: `EnvResolver`, `StaticResolver`, `TcpTransportFactory`
- Re-exported transport traits/types: `Transport`, `TransportError`, `TransportResult`, `RoleName`

See `rust/transport/src/lib.rs` for the current public surface.

## Guidance

When you need an exact signature, open the crate `lib.rs` and follow re-exports to the module definition. This keeps the reference accurate as the API evolves.
