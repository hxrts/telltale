# Semantic Runtime Name Parity

This file is the canonical cross-check for shared Lean and Rust semantic/runtime
object names.

Rules:

- Shared semantic/runtime objects keep the same PascalCase type name in Lean and Rust.
- Field names may differ only by language casing convention:
  Lean uses `camelCase`; Rust uses `snake_case`.
- Proof-only Lean packaging objects and Rust-only operational wrappers are listed
  separately and are not parity targets.

## Shared Semantic Object Inventory

Lean source of truth:
[lean/Runtime/protocol machine/Model/SemanticObjects/Core.lean](../lean/Runtime/protocol machine/Model/SemanticObjects/Core.lean)

Rust source of truth:
[rust/machine/src/semantic_objects.rs](../rust/machine/src/semantic_objects.rs)

| Shared object | Lean | Rust | Status |
|---|---|---|---|
| Operation instance | `OperationInstance` | `OperationInstance` | Exact name match |
| Outstanding effect | `OutstandingEffect` | `OutstandingEffect` | Exact name match |
| Semantic handoff | `SemanticHandoff` | `SemanticHandoff` | Exact name match |
| Transformation obligation | `TransformationObligation` | `TransformationObligation` | Exact name match |
| Authoritative read | `AuthoritativeRead` | `AuthoritativeRead` | Exact name match |
| Observed read | `ObservedRead` | `ObservedRead` | Exact name match |
| Materialization proof | `MaterializationProof` | `MaterializationProof` | Exact name match |
| Canonical handle | `CanonicalHandle` | `CanonicalHandle` | Exact name match |
| Publication event | `PublicationEvent` | `PublicationEvent` | Exact name match |
| Progress contract | `ProgressContract` | `ProgressContract` | Exact name match |
| Progress transition | `ProgressTransition` | `ProgressTransition` | Exact name match |
| Semantic object bundle | `ProtocolMachineSemanticObjects` | `ProtocolMachineSemanticObjects` | Exact name match |

## Shared Enum / Status Inventory

| Shared enum | Lean | Rust | Status |
|---|---|---|---|
| Operation phase | `OperationPhase` | `OperationPhase` | Exact name match |
| Outstanding effect status | `OutstandingEffectStatus` | `OutstandingEffectStatus` | Exact name match |
| Authoritative read kind | `AuthoritativeReadKind` | `AuthoritativeReadKind` | Exact name match |
| Authoritative read lifecycle | `AuthoritativeReadLifecycle` | `AuthoritativeReadLifecycle` | Exact name match |
| Canonical handle kind | `CanonicalHandleKind` | `CanonicalHandleKind` | Exact name match |
| Publication observer class | `PublicationObserverClass` | `PublicationObserverClass` | Exact name match |
| Publication status | `PublicationStatus` | `PublicationStatus` | Exact name match |
| Progress state | `ProgressState` | `ProgressState` | Exact name match |

## Casing Cross-Check

Representative field mappings:

| Lean field | Rust field |
|---|---|
| `operationId` | `operation_id` |
| `ownerId` | `owner_id` |
| `effectIds` | `effect_ids` |
| `terminalPublication` | `terminal_publication` |
| `handlerIdentity` | `handler_identity` |
| `completedAtTick` | `completed_at_tick` |
| `publicationId` | `publication_id` |
| `observerClass` | `observer_class` |
| `proofRef` | `proof_ref` |
| `lastOrderingKey` | `last_ordering_key` |
| `lastProgressTick` | `last_progress_tick` |
| `escalatedAtTick` | `escalated_at_tick` |

No shared object discovered in this pass had unexplained name drift beyond
Lean-vs-Rust casing.

## Lean-Only Proof Packaging Names

These are canonical Lean proof/runtime packaging objects. They are intentional
Lean-only surfaces, so they are not expected to have direct Rust runtime peers.

- `ProtocolMachineInvariantSpace`
- `ProtocolMachineTheoremPack`
- `ProtocolMachineRuntimeContracts`
- `ProtocolMachineLivenessBundle`
- `ProtocolMachineSchedulerBundle`
- `ProtocolMachineEnvelopeAdherenceProtocol`
- `ProtocolMachineEnvelopeAdmissionProtocol`
- `ProtocolMachineBridgePremises`
- `CoroutineViewEquiv`
- `protocolMachinePotential`

## Rust-Only Operational Wrapper Names

These are canonical Rust operational or embedding surfaces. They are intentional
Rust-only wrappers, so they are not expected to have direct Lean theorem peers.

- `GuestRuntime`
- `ThreadedGuestRuntime`
- `ExternalHandler`
- `ProtocolMachine`
- `ProtocolMachineConfig`
- `ProtocolMachineState`
- `ProtocolMachineError`
- `ProtocolMachineRunner`
- `ProtocolMachineRunInput`
- `ProtocolMachineRunOutput`
- `ProtocolMachineReplayBundle`
- `GuestRuntimeDecl`

## Maintenance Rule

When a shared semantic/runtime object is added, renamed, split, or removed:

1. Update the Lean definition in `lean/Runtime/protocol machine/Model/SemanticObjects/Core.lean`.
2. Update the Rust definition in `rust/machine/src/semantic_objects.rs`.
3. Update the bridge schema in `rust/lean-bridge/src/semantic_objects.rs`.
4. Update this parity inventory in the same change.
