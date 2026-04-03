# Lean Verification

This document summarizes the current Lean implementation surface and the proof APIs consumed by runtime gates.

## Source of Truth

Verification scale and proof-hole status are tracked by generated reports.

| Source | Purpose |
|---|---|
| [Lean Verification Code Map](../lean/CODE_MAP.md) | generated library map with file counts and module inventory |
| `just escape` | machine check for axiom and sorry budget |

These generated artifacts are the canonical sources for current scale and proof-hole status.

## Library Layers

The Lean tree is organized as a layered stack.

| Layer | Main content |
|---|---|
| SessionTypes | global and local syntax, de Bruijn forms, conversions |
| SessionCoTypes | coinductive equality, bisimulation, decidable regular checks |
| Choreography | projection, blindness, erasure, harmony |
| Semantics | small-step semantics, determinism, deadlock surfaces |
| Protocol | coherence, typing, monitoring, deployment composition |
| Runtime | protocol-machine model, semantics, runtime adapters, theorem-pack APIs |
| Distributed | FLP, CAP, quorum, synchrony, Nakamoto, reconfiguration, safety families |
| Classical | transported queueing and stochastic theorem families |
| ClassicalAnalysis | real-analysis-backed concrete models used by classical transport |
| IrisExtraction | runtime proof extraction and ghost logic bridge |

## Protocol-Machine Model and Runtime Surfaces

The protocol-machine model is centered under `lean/Runtime/ProtocolMachine`.

| Surface | Location |
|---|---|
| Core instruction and state model | `Runtime/ProtocolMachine/Model/*` |
| Executable semantics | `Runtime/ProtocolMachine/Semantics/*` |
| Runtime adapters and monitor | `Runtime/ProtocolMachine/Runtime/*` |
| Composition and domain instances | `Runtime/ProtocolMachine/Composition.lean` |

The effect model uses the current split `EffectRuntime` and `EffectSpec`. Monitor typing lives in `Runtime/ProtocolMachine/Runtime/Monitor.lean`.

## Semantic Objects Model

The semantic objects layer lives under `Runtime/ProtocolMachine/Model/SemanticObjects/`.

| Surface | Location |
|---|---|
| Identity, ownership, observed-read discipline | `Runtime/ProtocolMachine/Model/SemanticObjects/Core.lean`, `Invariants.lean` |
| Deferred-effect admissibility and stale late-result rejection | `Runtime/ProtocolMachine/Model/SemanticObjects/OutstandingEffects.lean`, `OutstandingEffectsLemmas.lean` |
| Semantic handoff activation and delegation bridge | `Runtime/ProtocolMachine/Model/SemanticObjects/SemanticHandoffTransition.lean`, `SemanticHandoffLemmas.lean` |
| Authoritative-read commitment and publication projection | `Runtime/ProtocolMachine/Model/SemanticObjects/AuthoritativeReadsPublication.lean`, `AuthoritativeReadsPublicationLemmas.lean` |
| Materialization-proof adequacy and canonical-handle adequacy | `Runtime/ProtocolMachine/Model/SemanticObjects/MaterializationSuccess.lean`, `MaterializationSuccessLemmas.lean` |
| First-class capability/finalization and runtime-upgrade facade | `lean/Runtime/Proofs/CapabilityModel.lean`, `lean/Runtime/Tests/ProtocolMachineRunner.lean` |
| Progress-contract semantics and escalation lemmas | `Runtime/ProtocolMachine/Model/SemanticObjects/ProgressContracts.lean`, `ProgressContractsLemmas.lean` |
| Transformation-local obligation bundles | `Runtime/ProtocolMachine/Model/SemanticObjects/TransformationLocalObligations.lean`, `TransformationLocalObligationsLemmas.lean` |
| Replay-failure exactness | `Runtime/ProtocolMachine/Model/SemanticObjects/ReplayFailureExactness.lean`, `ReplayFailureExactnessLemmas.lean` |
| Cross-target progress and dependent work | `Runtime/ProtocolMachine/Model/SemanticObjects/CrossTargetProgressDependentWork.lean`, `CrossTargetProgressDependentWorkLemmas.lean` |

Semantic-object theorem families attach to theorem-pack proof spaces through `Runtime/Proofs/InvariantSpace.lean` via `SemanticObjectWitnessBundle`.

## Proof Packs and Admission APIs

Runtime proof inventory is exported through theorem-pack modules.

| Surface | Purpose |
|---|---|
| `Runtime/Proofs/TheoremPack/API.lean` | public theorem-pack facade and runtime gate aliases |
| `Runtime/Proofs/TheoremPack/Inventory.lean` | capability inventory keys and determinism extension |
| `Runtime/Proofs/TheoremPack/ReleaseConformance.lean` | release gate and replay conformance report |
| `Runtime/Adequacy/EnvelopeCore/AdmissionLogic.lean` | admission soundness, completeness, diagnostics vocabulary |

These APIs are consumed by Rust runtime gates and composition admission checks.

The capability/finalization bridge surface is also consumed directly by the
strict correspondence lane through `inspectCapabilityModel`, which keeps the
Lean model for finalization paths and runtime-upgrade artifacts in executable
alignment with Rust.

## Premise-Scoped Interfaces

Some surfaces are intentionally premise-scoped.

| Interface class | Example |
|---|---|
| Threaded refinement beyond `n = 1` | `ThreadedRoundRefinementPremises` |
| Envelope admission and profile diagnostics | admission protocol structures in `AdmissionLogic.lean` |
| Mixed-profile runtime gates | theorem-pack and runtime-contract capability checks |

These are explicit interfaces and not unconditional global theorems.

## Distributed and Classical Reach

Distributed and classical families are part of the active theorem-pack space. They are not side notes.

Distributed families include FLP, CAP, quorum geometry, partial synchrony, responsiveness, Nakamoto security, reconfiguration, atomic broadcast, accountable safety, failure detectors, data availability, coordination, CRDT, Byzantine safety, consensus envelope, and failure envelope.

Classical transport families include Foster-Lyapunov, MaxWeight, large deviations, mean-field, heavy-traffic, mixing, fluid limits, concentration bounds, Little's law, and functional CLT.

## Runtime Alignment Lanes

Lean and Rust alignment is checked by automation lanes.

| Lane | Command |
|---|---|
| Runtime capability gates | `just check-capability-gates` |
| Release conformance | `just check-release-conformance` |
| Protocol-machine parity suite | `just check-parity --suite` |
| Type and schema parity | `just check-parity --types` |
| Conformance-specific parity lane | `just check-parity --conformance` |
| Consolidated parity lane | `just check-parity --all` |

## Related Docs

- [Protocol Machine Architecture](401_protocol_machine_architecture.md)
- [Rust-Lean Parity](703_rust_lean_parity.md)
- [Lean-Rust Bridge](702_lean_rust_bridge.md)
- [Capability and Admission](602_capability_admission.md)
- [Distributed and Classical Families](706_distributed_classical_families.md)
