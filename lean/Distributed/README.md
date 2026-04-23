# Distributed Theorem Pack Status

This directory contains distributed theorem families consumed by the runtime
theorem-pack layer. The current end-to-end attachment path is:

1. Distributed family core theorem or protocol record.
2. Runtime profile alias in
   [`Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean`](../Runtime/Proofs/Adapters/Distributed/ProfileWrappers.lean).
3. Artifact schema in
   [`Runtime/Proofs/TheoremPack/Artifacts.lean`](../Runtime/Proofs/TheoremPack/Artifacts.lean).
4. Artifact builder case in
   [`Runtime/Proofs/TheoremPack/Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean).
5. Profile-attachment example in
   [`Runtime/Proofs/Examples/DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean).

## Status Legend

`complete` means the pack proves its exported theorem from semantic evidence and
has a runtime theorem-pack example. `semantic core only` means useful semantic
proofs exist, but runtime profiles still need stronger derived evidence.
`profile shell` means the runtime profile mostly transports theorem-shaped
evidence. `placeholder` means some exported guarantee is vacuous or backed by
`True`-style assumptions.

## Pack Inventory

| Pack | Status | Semantic Source | Profile Type | Artifact Type | Builder / Example |
|------|--------|-----------------|--------------|---------------|-------------------|
| FLP | profile shell | [`Families/FLP/Core.lean`](Families/FLP/Core.lean) | `FLPProfile` | `FLPLowerBoundArtifact`, `FLPImpossibilityArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| CAP | profile shell | [`Families/CAP/Core.lean`](Families/CAP/Core.lean) | `CAPProfile` | `CAPImpossibilityArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| QuorumGeometry | semantic core only | [`Families/QuorumGeometry/Core.lean`](Families/QuorumGeometry/Core.lean) | `QuorumGeometryProfile` | `QuorumGeometryArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| PartialSynchrony | profile shell | [`Families/PartialSynchrony/Core.lean`](Families/PartialSynchrony/Core.lean) | `PartialSynchronyProfile` | `PartialSynchronyArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| Responsiveness | profile shell | [`Families/Responsiveness/Core.lean`](Families/Responsiveness/Core.lean) | `ResponsivenessProfile` | `ResponsivenessArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| Nakamoto | placeholder | [`Families/Nakamoto/Core.lean`](Families/Nakamoto/Core.lean) | `NakamotoProfile` | `NakamotoArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| Reconfiguration | placeholder | [`Families/Reconfiguration/Core.lean`](Families/Reconfiguration/Core.lean) | `ReconfigurationProfile` | `ReconfigurationArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| AtomicBroadcast | profile shell | [`Families/AtomicBroadcast/Core.lean`](Families/AtomicBroadcast/Core.lean) | `AtomicBroadcastProfile` | `AtomicBroadcastArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| AccountableSafety | profile shell | [`Families/AccountableSafety/Core.lean`](Families/AccountableSafety/Core.lean) | `AccountableSafetyProfile` | `AccountableSafetyArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| FailureDetectors | placeholder | [`Families/FailureDetectors/Core.lean`](Families/FailureDetectors/Core.lean) | `FailureDetectorsProfile` | `FailureDetectorsArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| DataAvailability | profile shell | [`Families/DataAvailability/Core.lean`](Families/DataAvailability/Core.lean) | `DataAvailabilityProfile` | `DataAvailabilityArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| Coordination / CALM | placeholder | [`Families/Coordination/Core.lean`](Families/Coordination/Core.lean) | `CoordinationProfile` | `CoordinationArtifact`, `CALMArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| CRDT | profile shell | [`Families/CRDT/Core.lean`](Families/CRDT/Core.lean) | `CRDTProfile` | `CRDTArtifact`, `CRDTMonotonicityArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| TriangleOfForgetting | semantic core only | [`Families/TriangleOfForgetting/Core.lean`](Families/TriangleOfForgetting/Core.lean) | `TriangleOfForgettingProfile` | `TriangleOfForgettingArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| ByzantineSafety | semantic core only | [`Families/ByzantineSafety/Core.lean`](Families/ByzantineSafety/Core.lean) | `ByzantineSafetyProfile` | `ByzantineSafetyArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |
| ConsensusEnvelope | profile shell | [`Model/ConsensusEnvelope.lean`](Model/ConsensusEnvelope.lean) | `ConsensusEnvelopeProfile` | `ConsensusEnvelopeArtifact` | [`Build.lean`](../Runtime/Proofs/TheoremPack/Build.lean), [`DistributedProfiles.lean`](../Runtime/Proofs/Examples/DistributedProfiles.lean) |

## Current Completion Boundary

No distributed family is currently marked `complete`. The runtime theorem-pack
attachment path exists, but many profiles still carry theorem-shaped evidence or
depend on vacuous placeholders. The work plan in `work/_1.md` is the checklist
for moving each pack from `placeholder` or `profile shell` to `complete`.
