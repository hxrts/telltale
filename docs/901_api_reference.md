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

Generated `tell!` APIs use one canonical effect-boundary import style:

- import `Protocol::effects`
- `effects::Runtime` for host traits
- `effects::RuntimeRequest` / `effects::RuntimeOutcome` for typed dispatch
- `effects::runtime::operation("ready")` or `effects::runtime::READY` for
  generated per-operation semantic metadata
- `Protocol::proof_status` for theorem-pack, tier, parity, and
  agreement/finality metadata

### `telltale-types`

Type definitions shared across the stack.

Key exports:

- `GlobalType`, `LocalTypeR`, `Label`, `PayloadSort`
- `ContentId`, `Blake3Hasher`, `ContentStore`, `KeyedContentStore`
- `DefaultContentHasher` and `DefaultContentId` for central content-hash policy
- `Sha256Hasher` and `ContentIdSha256` when the `sha256` feature is enabled
- Merge helpers (`merge`, `merge_all`, `can_merge`) and canonical-serialization utilities

See `rust/types/src/lib.rs` for re-exports.

### `telltale-theory`

Session-type algorithms and executable theory checks.

Key modules:

- Projection: `telltale_theory::projection::{project, project_all, MemoizedProjector}`
- Merge, duality, well-formedness, and semantics checks
- Subtyping (feature-gated): `telltale_theory::subtyping::{async_subtype, sync_subtype}`

Exports are module-scoped, not re-exported at crate root. See `rust/theory/src/lib.rs` for the complete feature-gated API.

### `telltale-runtime`

Choreographic DSL, projection, and effect execution.

Key exports:

- AST types: `Choreography`, `Protocol`, `Role`, `MessageType`
- Effect system: `Program`, `ProgramBuilder`, `interpret`
- Handlers: `ChoreoHandler`, `InMemoryHandler`, `TelltaleHandler`
- Topology: `Topology`, `TopologyHandler`, `TransportType`
- Heap: `Heap`, `DefaultHeapHasher`, `Hasher`, `Resource`, `ResourceId`,
  `CanonicalHeapEncoding`, `CanonicalHeapEncoder`, `HEAP_ENCODING_MAGIC`,
  `HEAP_ENCODING_VERSION`, `resource_leaf_hash`, `nullifier_leaf_hash`,
  `merkle_node_hash`, `MerkleTree`, `HeapCommitment`
- Heap preimage helpers (module-scoped, not at crate root):
  `telltale_runtime::heap::{resource_id_preimage, resource_leaf_preimage,
  nullifier_leaf_preimage, merkle_node_preimage, heap_commitment_preimage}`
- Extensions: `ExtensionRegistry`, `GrammarExtension`, `ProtocolExtension`

See `rust/runtime/src/lib.rs` for the full export surface.

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
- proof-aligned effect algebra:
  `EffectSemanticClass`, `EffectRetryShape`, `EffectCompositionPolicy`
  `EffectResponsibilityDomain`
- canonical semantic objects:
  `OperationInstance`, `OutstandingEffect`, `SemanticHandoff`,
  `TransformationObligation`,
  `AuthoritativeRead`, `ObservedRead`, `MaterializationProof`,
  `CanonicalHandle`, `PublicationEvent`, `Region`, `ProgressContract`,
  `ProgressTransition`,
  `ProtocolMachineSemanticObjects`
- first-class capability/finalization taxonomy:
  `ProtocolCriticalCapabilityClass`,
  `ProtocolCriticalCapabilityLifecycleState`,
  `ProtocolCriticalCapabilityArtifact`,
  `ProtocolCriticalCapabilityLifecycleRecord`,
  `ProtocolMachineFinalization`,
  `FinalizationPath`,
  `FinalizationReadClass`,
  `FinalizationStage`
- proof-carrying runtime profiles:
  `ProtocolMachineExecutionProfile`, `ProtocolMachineFairnessAssumption`,
  `ProtocolMachineAdmissibilityClass`,
  `ProtocolMachineEscalationWindowClass`
- runtime introspection (methods on `ProtocolMachine` / `GuestRuntime`):
  `operation_instances()`, `outstanding_effects()`, `semantic_objects()`,
  `progress_contracts()`, `progress_transitions()`, `publication_events()`,
  `require_authoritative_read()`,
  `require_canonical_handle()`, `protocol_machine_finalization()`,
  `capability_lifecycle_audit_log()`, `semantic_audit_log()`,
  `canonical_replay_fragment()`

`GuestRuntime` is the Telltale-owned runtime instantiated around the protocol
machine. `EffectHandler` is the host-runtime boundary implemented by embedders
and simulators.

Module access (not re-exported at crate root):
- Effect boundary:
  `telltale_machine::model::effects::EffectHandler`, `EffectRequest`, `EffectOutcome`,
  `EffectInterfaceMetadata`, `EffectExchangeRecord`, `EffectCompositionPolicy`
  `EffectSemanticClass`, `EffectRetryShape`, `EffectResponsibilityDomain`,
  `SendDecision`, `SendDecisionInput`
  The typed internal durability request is `EffectRequestBody::WalSync`.
- Effect trace: `telltale_machine::model::effects::RecordingEffectHandler`, `ReplayEffectHandler`
- Durability:
  `telltale_machine::model::durability::{AgreementWal, AgreementWalArtifact, AgreementWalEntry, AgreementWalHandler, EvidenceIdResolver, EvidenceOutcomeCache, EvidenceOutcomeCacheArtifact, EvidenceOutcomeCacheEntry, EvidencePersistenceHandler, DurableRecoveryMetadata, FileAgreementWal, FileEvidenceOutcomeCache, InMemoryAgreementWal, InMemoryEvidenceOutcomeCache, PersistedDurabilityArtifact, PersistedDurabilityPayload, WalSyncMode, WalSyncRequest}`
  These are the authoritative typed contracts for durable agreement WALs, evidence outcome caches, recovery metadata, and the internal `wal_sync` durability boundary.
  Helper/generated/viewer surfaces should consume projections of these artifacts rather than defining peer durable state.
- Child-effect aggregation: `EffectCompositionPolicy` is a secondary sibling-effect algebra used beneath parent agreement contracts, not the top-level agreement model
- Loader: `telltale_machine::runtime::loader::CodeImage`
- Runtime contracts:
  `telltale_machine::runtime::failure::{RuntimeContracts, ProtocolMachineExecutionProfile}`
- Runtime runner: `telltale_machine::runtime::runner::{ProtocolMachine, GuestRuntime, StepResult, RunStatus}`
- Semantics: `telltale_machine::semantics::exec::{ExecResult, ExecStatus, StepPack}`

See `rust/machine/src/lib.rs` for the full API.
See [Effect Handlers and Session Types](303_effect_session_bridge.md) for integration-boundary guidance.

### `telltale-simulator`

Simulation utilities built on the protocol machine.

Key exports:

- Harness surface in `rust/simulator/src/harness.rs`:
  `HostAdapter`, `DirectAdapter`, `FieldAdapter`, `HarnessSpec`, `HarnessConfig`, `SimulationHarness`,
  `BatchConfig`, `BatchRunResult`
  `FieldAdapter::from_scenario(...)` requires built-in scenario field params.
  Generic harness runs may omit `Scenario.field` when the adapter supplies its own initial states or environment models.
  `SimulationHarness::run_batch(...)` and `run_batch_with(...)` preserve input-order results while parallelizing independent runs.

Module access (not re-exported at crate root):
- `telltale_simulator::trace::Trace`, `StepRecord`
- `telltale_simulator::runner::run`, `run_concurrent`, `run_with_scenario`, `ChoreographySpec`
- `telltale_simulator::scenario::{Scenario, ExecutionSpec, ExecutionBackend, ResolvedExecution, ResolvedExecutionBackend}`
- `telltale_simulator::generated::{GeneratedEffectScenario, GeneratedEffectScenarioBuilder, GeneratedEffectSimulationReport, ScenarioEffectDisposition, ScenarioEffectResult, ScenarioEffectStep}`
  Helper-only generated-effect support. `GeneratedEffectSimulationReport` exposes helper accessors, not authoritative replay or theorem-classification fields.
- `telltale_simulator::{CheckpointArtifact, PersistedReplayArtifact, PersistedReplayPayload}`
  Typed persisted replay/checkpoint wrappers for on-disk simulator artifacts.
  Durable agreement WALs and recovery metadata intentionally remain machine-level typed contracts instead of simulator helper exports.
- `telltale_viewer::{SemanticComparisonResult, TheoremAwareCounterexample, DeterministicSweepReport, ExperimentSuiteReport, EffectTraceArtifact, MinimizationResult, ViewerExtensionManifest}`
  Shared viewer/webapp tooling surfaces for comparison, counterexamples, sweeps, effects, minimization, and downstream overlays.
- Contract checks in `rust/simulator/src/contracts.rs`:
  `ContractCheckConfig`, `ContractCheckReport`, `evaluate_contracts`, `assert_contracts`
- Preset helpers in `rust/simulator/src/presets.rs`
- Field handlers and factory:
  `IsingHandler`, `HamiltonianHandler`, `ContinuumFieldHandler`, `handler_from_field`
  in `rust/simulator/src/field_handlers/`

### `telltale-bridge`

Lean bridge for JSON export, import, and validation.

Key exports:

- `global_to_json`, `local_to_json`, `json_to_global`, `json_to_local`
- `LeanRunner`, `Validator`, `ValidationResult`
- `HeapParityRunner`, `HeapParityOutput`
- `ProtocolMachineSemanticObjects` and semantic-object schema helpers
  These come from the same canonical semantic-object family as `telltale_machine::model::semantic_objects`, not a bridge-local duplicate.

See [Rust-Lean Bridge and Parity](802_rust_lean_parity.md) for details.

### `telltale-transport`

Production transport implementations for choreography topologies.

Key exports:

- `TcpTransport`, `TcpTransportConfig`, `TransportState`
- Resolver and factory surfaces: `EnvResolver`, `StaticResolver`, `TcpTransportFactory`
- Re-exported transport traits/types: `Transport`, `TransportError`, `TransportResult`, `RoleName`

See `rust/transport/src/lib.rs` for the current public surface.

## Guidance

When you need an exact signature, open the crate `lib.rs` and follow re-exports to the module definition. This keeps the reference accurate as the API evolves.
