import Runtime.Proofs.InvariantSpace
import Distributed.Families.FLP
import Distributed.Families.CAP
import Distributed.Families.QuorumGeometry
import Distributed.Families.PartialSynchrony
import Distributed.Families.Responsiveness
import Distributed.Families.Nakamoto
import Distributed.Families.Reconfiguration
import Distributed.Families.AtomicBroadcast
import Distributed.Families.AccountableSafety
import Distributed.Families.FailureDetectors
import Distributed.Families.DataAvailability
import Distributed.Families.Coordination
import Distributed.Families.CRDT
import Distributed.Model.ConsensusEnvelope
import Runtime.Adequacy.EnvelopeCore

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed.ProfileWrappers

Distributed impossibility/lower-bound profile wrappers attached to VM invariant spaces.
-/

/-
The Problem. Distributed-theory families (FLP, CAP, quorum geometry, synchrony
variants, and envelope theorem packs) need a uniform representation that can be
attached to the VM invariant space.

Solution Structure. Defines profile wrappers, canonical constructors, and the
distributed-profile bundle carried by `VMInvariantSpaceWithDistributed`.
-/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Distributed Family Profile Wrappers -/

/-- FLP profile wrapper for invariant-space attachment. -/
structure FLPProfile where
  protocol : Distributed.FLP.ImpossibilityProtocol

/-- CAP profile wrapper for invariant-space attachment. -/
structure CAPProfile where
  protocol : Distributed.CAP.ImpossibilityProtocol

/-- Quorum-geometry profile wrapper for invariant-space attachment. -/
structure QuorumGeometryProfile where
  protocol : Distributed.QuorumGeometry.SafetyProtocol

/-- Partial-synchrony liveness profile wrapper for invariant-space attachment. -/
structure PartialSynchronyProfile where
  protocol : Distributed.PartialSynchrony.LivenessProtocol

/-- Responsiveness profile wrapper for invariant-space attachment. -/
structure ResponsivenessProfile where
  protocol : Distributed.Responsiveness.ResponsiveProtocol

/-- Nakamoto-security profile wrapper for invariant-space attachment. -/
structure NakamotoProfile where
  protocol : Distributed.Nakamoto.SecurityProtocol

/-- Reconfiguration profile wrapper for invariant-space attachment. -/
structure ReconfigurationProfile where
  protocol : Distributed.Reconfiguration.ReconfigurationProtocol

/-- Atomic-broadcast profile wrapper for invariant-space attachment. -/
structure AtomicBroadcastProfile where
  protocol : Distributed.AtomicBroadcast.AtomicBroadcastProtocol

/-- Accountable-safety profile wrapper for invariant-space attachment. -/
structure AccountableSafetyProfile where
  protocol : Distributed.AccountableSafety.AccountableProtocol

/-- Failure-detector boundary profile wrapper for invariant-space attachment. -/
structure FailureDetectorsProfile where
  protocol : Distributed.FailureDetectors.BoundaryProtocol

/-- Data-availability profile wrapper for invariant-space attachment. -/
structure DataAvailabilityProfile where
  protocol : Distributed.DataAvailability.DAProtocol

/-- Coordination-characterization profile wrapper for invariant-space attachment. -/
structure CoordinationProfile where
  protocol : Distributed.Coordination.CoordinationProtocol

/-- CRDT theorem-family profile wrapper for invariant-space attachment. -/
structure CRDTProfile where
  protocol : Distributed.CRDT.CRDTProtocol

/-- Consensus-envelope theorem-family profile wrapper for invariant-space attachment. -/
structure ConsensusEnvelopeProfile where
  protocol : Distributed.ConsensusEnvelope.ConsensusEnvelopeProtocol

/-- Failure-envelope theorem-family profile wrapper for invariant-space attachment. -/
structure FailureEnvelopeProfile where
  protocol : Runtime.Adequacy.FailureEnvelopeProtocol

/-- VM envelope-adherence theorem-family profile wrapper for invariant-space attachment. -/
structure VMEnvelopeAdherenceProfile where
  protocol : Runtime.Adequacy.VMEnvelopeAdherenceProtocol

/-- VM envelope-admission theorem-family profile wrapper for invariant-space attachment. -/
structure VMEnvelopeAdmissionProfile where
  protocol : Runtime.Adequacy.VMEnvelopeAdmissionProtocol

/-- Protocol envelope-bridge theorem-family profile wrapper for invariant-space attachment. -/
structure ProtocolEnvelopeBridgeProfile where
  Protocol : Type
  Placement : Type
  Deployment : Type
  State : Type
  Obs : Type
  bundle :
    Runtime.Adequacy.ProtocolEnvelopeBridgeBundle
      Protocol Placement Deployment State Obs

/-! ## Canonical Impossibility Constructors -/

/-- Canonical FLP-class distributed profile constructor.
The `ImpossibilityProtocol` type enforces asynchronous deterministic crash-resilient
assumption packaging structurally. -/
def asyncDeterministicCrashResilientProfile
    (protocol : Distributed.FLP.ImpossibilityProtocol) : FLPProfile :=
  { protocol := protocol }

/-- Canonical CAP-class distributed profile constructor.
The `ImpossibilityProtocol` type enforces async partition-tolerant assumption packaging
structurally. -/
def partitionTolerantAsyncProfile
    (protocol : Distributed.CAP.ImpossibilityProtocol) : CAPProfile :=
  { protocol := protocol }

/-! ## Distributed Profile Bundles -/

/-- Optional distributed-theory profiles attached to an invariant space. -/
structure DistributedProfiles where
  flp? : Option FLPProfile := none
  cap? : Option CAPProfile := none
  quorumGeometry? : Option QuorumGeometryProfile := none
  partialSynchrony? : Option PartialSynchronyProfile := none
  responsiveness? : Option ResponsivenessProfile := none
  nakamoto? : Option NakamotoProfile := none
  reconfiguration? : Option ReconfigurationProfile := none
  atomicBroadcast? : Option AtomicBroadcastProfile := none
  accountableSafety? : Option AccountableSafetyProfile := none
  failureDetectors? : Option FailureDetectorsProfile := none
  dataAvailability? : Option DataAvailabilityProfile := none
  coordination? : Option CoordinationProfile := none
  crdt? : Option CRDTProfile := none
  consensusEnvelope? : Option ConsensusEnvelopeProfile := none
  failureEnvelope? : Option FailureEnvelopeProfile := none
  vmEnvelopeAdherence? : Option VMEnvelopeAdherenceProfile := none
  vmEnvelopeAdmission? : Option VMEnvelopeAdmissionProfile := none
  protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeProfile := none

/-- VM invariant space extended with optional distributed-theory profiles. -/
structure VMInvariantSpaceWithDistributed
    (store₀ : SessionStore ν) (State : Type v)
    extends VMInvariantSpace (ν := ν) store₀ State where
  distributed : DistributedProfiles := {}

end

end Adapters
end Proofs
end Runtime
