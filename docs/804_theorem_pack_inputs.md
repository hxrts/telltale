# Theorem Pack Inputs

This document catalogs every input that can contribute to a `ProtocolMachineTheoremPack`. The pack is the capability surface consumed by release gates, runtime admission paths, and conformance reports. All theorem-pack artifacts are derived from one `ProtocolMachineInvariantSpaceWithProfiles` by `buildProtocolMachineTheoremPack` in `lean/Runtime/Proofs/TheoremPack/Build.lean`.

## Pack Shape

`ProtocolMachineTheoremPack` is a record of `Option` artifact fields, one per theorem family. Inputs arrive in two shapes. Invariant-space inputs attach via API setters on the combined space. Optional profile inputs attach via family-specific `with*` setters and are consumed by the builder.

The combined invariant space is `ProtocolMachineInvariantSpaceWithProfiles` in `lean/Runtime/Proofs/TheoremPack/Profiles.lean`. It extends the distributed-profile space and adds a `classical` profile record. Two projection views (`toDistributedSpace`, `toClassicalSpace`) let builders consume the distributed or classical subset in isolation.

## Core Invariant-Space Inputs

Three input families enter the pack directly from the invariant space. They do not require a distributed or classical profile.

| Family | Source field | API setter | Inventory key |
|---|---|---|---|
| termination | `liveness?` | `withLivenessBundle` | `termination` |
| output condition soundness | `outputConditionWitness?` | `withOutputCondition` | `output_condition_soundness` |
| semantic objects | `semanticObjectWitnesses?` | `withSemanticObjectWitnesses` | `semantic_object_*` |

Termination artifacts use `Adapters.toLivenessBundle?` from `lean/Runtime/Proofs/Adapters/Progress.lean` and the theorem `protocol_machine_termination_from_invariant_space`. Output-condition artifacts lift soundness from `outputConditionWitness?` into `OutputConditionArtifact`. Semantic-object artifacts are built by `SemanticObjectArtifacts.ofWitnessBundle` and cover core invariants, outstanding effects, semantic handoffs, authoritative-read publication, materialization success, progress contracts, effect contracts, replay failure exactness, cross-target progress-dependent work, and transformation-local obligations.

## Distributed Families

Distributed profile wrappers are defined in `lean/Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean`. Each family attaches through a `with*` setter on the combined space.

| Family | Profile setter | Inventory key |
|---|---|---|
| FLP lower bound | `withFLP` | `flp_lower_bound` |
| FLP impossibility | `withFLP` | `flp_impossibility` |
| CAP impossibility | `withCAP` | `cap_impossibility` |
| quorum geometry | `withQuorumGeometry` | `quorum_geometry_safety` |
| partial synchrony | `withPartialSynchrony` | `partial_synchrony_liveness` |
| responsiveness | `withResponsiveness` | `responsiveness` |
| Nakamoto security | `withNakamoto` | `nakamoto_security` |
| reconfiguration | `withReconfiguration` | `reconfiguration_safety` |
| atomic broadcast | `withAtomicBroadcast` | `atomic_broadcast_ordering` |
| accountable safety | `withAccountableSafety` | `accountable_safety` |
| failure detectors | `withFailureDetectors` | `failure_detector_boundaries` |
| data availability | `withDataAvailability` | `data_availability_retrievability` |
| coordination | `withCoordination` | `coordination_characterization` |
| CRDT envelope family | `withCRDT` | `crdt_envelope_and_equivalence` |
| CRDT op-core erasure | `withCRDTErasure` | (stored in pack as `crdtErasure?`) |
| triangle of forgetting | `withTriangleOfForgetting` | `triangle_of_forgetting_impossibility` |
| Byzantine safety | `withByzantineSafety` | `byzantine_safety_characterization` |
| consensus envelope | `withConsensusEnvelope` | `consensus_envelope` |
| failure envelope | `withFailureEnvelope` | `failure_envelope` |
| protocol machine envelope adherence | `withProtocolMachineEnvelopeAdherence` | `protocol_machine_envelope_adherence` |
| protocol machine envelope admission | `withProtocolMachineEnvelopeAdmission` | `protocol_machine_envelope_admission` |
| protocol envelope bridge | `withProtocolEnvelopeBridge` | `protocol_envelope_bridge` |

Three inventory keys are derived from other profiles and have no distinct setter. `calm_characterization` is derived from the coordination profile. `crdt_monotonicity` is derived from the CRDT profile. `effect_interface_bridge` is derived from the conjunction of `protocolMachineEnvelopeAdherence?` and `protocolEnvelopeBridge?`.

## Classical Families

Classical wrappers are defined in `lean/Runtime/Proofs/Adapters/Classical.lean`. Each classical family has a per-family setter on `ProtocolMachineInvariantSpaceWithProfiles`. `withClassicalProfiles` remains available as a batch replacement API when a caller wants to replace the whole `ClassicalProfiles` record.

| Family | Setter | Wrapper type | Inventory key |
|---|---|---|---|
| Foster-Lyapunov | `withFoster` | `FosterProfile` | `classical_foster` |
| MaxWeight | `withMaxWeight` | `MaxWeightProfile` | `classical_maxweight` |
| large deviations | `withLDP` | `LDPProfile` | `classical_ldp` |
| mean-field | `withMeanField` | `MeanFieldProfile` | `classical_mean_field` |
| heavy-traffic | `withHeavyTraffic` | `HeavyTrafficProfile` | `classical_heavy_traffic` |
| mixing time | `withMixing` | `MixingProfile` | `classical_mixing` |
| fluid limit | `withFluid` | `FluidProfile` | `classical_fluid` |
| concentration bounds | `withConcentration` | `ConcentrationProfile` | `classical_concentration` |
| Little's law | `withLittlesLaw` | `LittlesLawProfile` | `classical_littles_law` |
| functional CLT | `withFunctionalCLT` | `FunctionalCLTProfile` | `classical_functional_clt` |
| spectral-gap termination | `withSpectralGap` | `SpectralGapProfile` | `classical_spectral_gap_termination` |

Classical artifacts carry small semantic obligations such as Lyapunov descent, backpressure optimality, or mixing-time bounds. They do not assert stronger system-level claims beyond their declared assumptions.

## Execution Profile

`ProtocolMachineExecutionProfile` is the proof-carrying execution context derived from the invariant space. It fixes fairness assumptions, admissibility classes, escalation-window classes, a theorem-pack eligibility list, and a necessity catalog. The builder function is `ProtocolMachineInvariantSpaceWithProfiles.executionProfile`.

Fairness assumptions enumerate `scheduleConfluence`, `starvationFreedom`, and `livenessFairness`. Admissibility classes cover `localEnvelope`, `shardedEnvelope`, and `protocolEnvelopeBridge`. Escalation-window classes cover `progressContractBounded`, `admissionComplexityBounded`, and `protocolBridgeBounded`.

The execution profile also carries a list of `TransportNecessityProfile` values. `executionProfile_necessity_hardened_of_all_proven_necessary` and `executionProfile_necessity_minimal_basis_of_hardened_and_oracles` lift per-profile necessity into catalog-level hardening and minimal-basis closure. Both theorems are stated in `lean/Runtime/Proofs/TheoremPack/Profiles.lean`.

## Proof-Carrying Metadata

`ProofCarryingArtifactMetadata` summarizes profile, progress, and envelope metadata alongside each pack.

| Component | Record | Source |
|---|---|---|
| execution profile and eligibility | `ProfileArtifactMetadata` | execution profile on the combined space |
| progress contracts and failure taxonomy | `ProgressArtifactMetadata` | semantic-object witnesses |
| envelope adherence, admission, bridge | `EnvelopeArtifactMetadata` | derived distributed profiles |

`ProofCarryingArtifactMetadata.ofInvariantSpace` assembles these from the combined space and the three envelope-presence booleans. Metadata inventory keys are enumerated in `proofCarryingMetadataInventory` in `lean/Runtime/Proofs/TheoremPack/Inventory.lean`.

## Inventory and Capability Keys

`theoremInventory` in `lean/Runtime/Proofs/TheoremPack/Inventory.lean` projects the pack into a flat list of `(key, Bool)` pairs. Keys cover termination, output-condition soundness, every distributed family, every classical family, the effect-interface bridge, and each semantic-object component. Release and admission paths consume this inventory rather than the pack directly.

`theoremInventoryWithDeterminism` augments the inventory with determinism-policy booleans. The semantic-object sub-inventory is produced by `SemanticObjectArtifacts.inventory` and folds each semantic witness into a capability key under the `semantic_object_*` prefix.

## Admission Boundary

`transportedTheoremBoundaryInventory` in `lean/Runtime/Proofs/TheoremPack/AdmissionBoundary.lean` tags each inventory key with a `TransportedTheoremUsageClass`. The class distinguishes black-box premise use, runtime-critical instantiated premises, and documentation-only references.

`runtimeCriticalTransportedTheoremBoundaryInventory` narrows the ledger to families that gate runtime admission. `rustRuntimeCriticalTransportedTheoremKeys` and `leanRuntimeCriticalTransportedTheoremKeys` expose the Rust and Lean subsets consumed by admission paths. `runtimeCriticalTransportedTheoremsExplicit_true` certifies that the Rust and Lean lists agree.

### Transport Contracts

Theorem-backed distributed claims also require selected transport contracts. The Rust machine consumes `RuntimeTransportContract` values as semantic evidence, not as TCP-, TLS-, or key-management-specific implementation details. Concrete transport crates are responsible for mapping their configured mode into those fields.

The standard protocol-origin profile requires role-addressed routing, authenticated peers, per-peer FIFO delivery, fail-closed unknown-role handling, and no message synthesis. For `telltale-transport`, `TcpTransportConfig::runtime_transport_contract()` maps pre-shared-key TCP to `authenticated_peers = true` and trusted-network TCP to `authenticated_peers = false`. Trusted-network contracts are intentionally rejected for theorem-pack profiles that depend on authenticated protocol origins.

## Release Conformance

`buildReleaseConformanceReport` in `lean/Runtime/Proofs/TheoremPack/ReleaseConformance.lean` assembles a `ReleaseConformanceReport` from the pack and a replay trace. Report fields include the theorem inventory, a transformation-eligibility snapshot, replay conformance, cross-target failure-envelope witness presence, restart-adequacy witness presence, and single-thread, multi-thread, and sharded evidence flags. `releaseBuildGate` derives the build-gate Boolean from the report when release-tagged.

Optimization transformations are enumerated by `RuntimeTransformationEnvelopeClass`. The four classes are `schedulerPermutation`, `waveWidening`, `effectReordering`, and `failureReplayNormalization`. `transformationClassRequiredCapabilities` defines the inventory keys each class requires, and `transformationClassEligible` is the inventory gate.

`CertifiedReplayEquivalenceClass` pairs a transformation class with a certificate reference. `defaultCertifiedReplayClasses` is the canonical list admitted by release gates. `replayConformsToClasses` is the per-class replay gate used by the build gate.

## Capability API Gates

`lean/Runtime/Proofs/TheoremPack/API.lean` exposes the runtime capability gates that consume the pack.

| Gate | Artifact requirement |
|---|---|
| `canAdmitShardPlacement` | `protocolEnvelopeBridge?` |
| `canLiveMigrate` | `protocolEnvelopeBridge?` |
| `canRefinePlacement` | `protocolEnvelopeBridge?` |
| `canRelaxReordering` | `protocolEnvelopeBridge?` |
| `canUseMixedDeterminismProfiles` | `protocolMachineEnvelopeAdherence?` and `protocolMachineEnvelopeAdmission?` |
| `canOperateUnderByzantineEnvelope` | `byzantineSafety?` and `protocolMachineEnvelopeAdherence?` |
| `canAutoscaleOrRepartition` | `protocolEnvelopeBridge?` |

Rust admission paths in `rust/machine/src/runtime_contracts.rs` and `rust/machine/src/composition.rs` consume these gates as executable admission checks. `claimedCapabilitiesWithinInventory` verifies that a list of declared capability tags is supported by the pack capabilities. `envelopeCapabilitySnapshot` extracts the envelope subset used by conformance reports.

## Assumption Discipline

Each family carries a proof-bearing semantic profile. Completed families avoid final-theorem witness fields. Profiles expose smaller laws such as delivery and ordering facts, quorum geometry, timed-run predicates, CRDT laws, chain growth and quality, shard reconstruction, or slashable-evidence construction.

Capability bits indicate that the theorem-pack builder derived the corresponding artifact from a profile. They do not imply stronger claims outside the family assumption bundle or an explicit documented trust boundary.

## Runtime Admission Impact

Runtime features that require profile evidence are gate-controlled. Examples include mixed determinism profiles, Byzantine envelope operation, autoscaling and repartition requests, and placement refinement. Gate aliases are provided in `lean/Runtime/Proofs/TheoremPack/API.lean`. Rust runtime admission paths consume these aliases.

## Related Docs

- [Lean Verification](801_lean_verification.md)
- [Capability Admission](702_capability_admission.md)
- [Theorem Program](803_theorem_program.md)
- [Verification Inventory](902_verification_inventory.md)
- [Glossary and Notation Index](903_glossary_notation.md)
