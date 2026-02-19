# Distributed and Classical Families

This document summarizes the distributed and classical theorem families exposed by the Lean runtime proof stack.

## Distributed Families

Distributed profile wrappers are defined in `lean/Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean` and attached through profile setters.

| Family | Wrapper type | Inventory key |
|---|---|---|
| FLP impossibility | `FLPProfile` | `flp_impossibility` |
| CAP impossibility | `CAPProfile` | `cap_impossibility` |
| quorum geometry | `QuorumGeometryProfile` | `quorum_geometry_safety` |
| partial synchrony | `PartialSynchronyProfile` | `partial_synchrony_liveness` |
| responsiveness | `ResponsivenessProfile` | `responsiveness` |
| Nakamoto security | `NakamotoProfile` | `nakamoto_security` |
| reconfiguration | `ReconfigurationProfile` | `reconfiguration_safety` |
| atomic broadcast | `AtomicBroadcastProfile` | `atomic_broadcast_ordering` |
| accountable safety | `AccountableSafetyProfile` | `accountable_safety` |
| failure detectors | `FailureDetectorsProfile` | `failure_detector_boundaries` |
| data availability | `DataAvailabilityProfile` | `data_availability_retrievability` |
| coordination | `CoordinationProfile` | `coordination_characterization` |
| CRDT envelope family | `CRDTProfile` | `crdt_envelope_and_equivalence` |
| Byzantine safety family | `ByzantineSafetyProfile` | `byzantine_safety_characterization` |
| consensus envelope family | `ConsensusEnvelopeProfile` | `consensus_envelope` |
| failure envelope family | `FailureEnvelopeProfile` | `failure_envelope` |
| VM adherence family | `VMEnvelopeAdherenceProfile` | `vm_envelope_adherence` |
| VM admission family | `VMEnvelopeAdmissionProfile` | `vm_envelope_admission` |
| protocol bridge family | `ProtocolEnvelopeBridgeProfile` | `protocol_envelope_bridge` |

## Classical Families

Classical wrappers are defined in `lean/Runtime/Proofs/Adapters/Classical.lean`.

| Family | Wrapper type | Inventory key |
|---|---|---|
| Foster-Lyapunov | `FosterProfile` | `classical_foster` |
| MaxWeight | `MaxWeightProfile` | `classical_maxweight` |
| large deviations | `LDPProfile` | `classical_ldp` |
| mean-field | `MeanFieldProfile` | `classical_mean_field` |
| heavy-traffic | `HeavyTrafficProfile` | `classical_heavy_traffic` |
| mixing time | `MixingProfile` | `classical_mixing` |
| fluid limit | `FluidProfile` | `classical_fluid` |
| concentration bounds | `ConcentrationProfile` | `classical_concentration` |
| Little's law | `LittlesLawProfile` | `classical_littles_law` |
| functional CLT | `FunctionalCLTProfile` | `classical_functional_clt` |

These profiles are transported into theorem artifacts by adapter constructors and theorem-pack builders.

## Theorem-Pack Integration

The combined builder is in `lean/Runtime/Proofs/TheoremPack/Build.lean`.

Optional artifacts are assembled into `VMTheoremPack` and then summarized by `theoremInventory` in `lean/Runtime/Proofs/TheoremPack/Inventory.lean`. This inventory is the capability surface used by release and admission checks.

## Runtime Admission Impact

Runtime features that require profile evidence are gate-controlled.

Examples include mixed determinism profiles, Byzantine envelope operation, autoscaling and repartition requests, and placement refinement. Gate aliases are provided in `lean/Runtime/Proofs/TheoremPack/API.lean` and consumed in Rust runtime admission paths.

## Assumption Discipline

Each family carries explicit premises in its protocol wrapper and theorem object.

Capability bits indicate that a witness exists for the corresponding theorem family under that profile. They do not imply stronger claims outside the family assumption bundle.

## Related Docs

- [Lean Verification](18_lean_verification.md)
- [Capability and Admission](25_capability_admission.md)
- [Theorem Program](26_theorem_program.md)
