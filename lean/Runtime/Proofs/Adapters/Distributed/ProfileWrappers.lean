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
import Distributed.Families.ByzantineSafety
import Distributed.Model.ConsensusEnvelope
import Runtime.Adequacy.EnvelopeCore

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed.ProfileWrappers

Distributed impossibility/lower-bound profile wrappers attached to protocol machine invariant spaces.
-/

/-
The Problem. Distributed-theory families (FLP, CAP, quorum geometry, synchrony
variants, and envelope theorem packs) need a uniform representation that can be
attached to the protocol machine invariant space.

Solution Structure. Defines profile wrappers, canonical constructors, and the
distributed-profile bundle carried by `ProtocolMachineInvariantSpaceWithDistributedProfiles`.
-/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Distributed Family Profile Aliases -/

/-- Canonical FLP profile carried by the invariant space. -/
abbrev FLPProfile := Distributed.FLP.ImpossibilityProtocol

/-- Canonical CAP profile carried by the invariant space. -/
abbrev CAPProfile := Distributed.CAP.ImpossibilityProtocol

/-- Canonical quorum-geometry profile carried by the invariant space. -/
abbrev QuorumGeometryProfile := Distributed.QuorumGeometry.SafetyProtocol

/-- Canonical partial-synchrony profile carried by the invariant space. -/
abbrev PartialSynchronyProfile := Distributed.PartialSynchrony.LivenessProtocol

/-- Canonical responsiveness profile carried by the invariant space. -/
abbrev ResponsivenessProfile := Distributed.Responsiveness.ResponsiveProtocol

/-- Canonical Nakamoto-security profile carried by the invariant space. -/
abbrev NakamotoProfile := Distributed.Nakamoto.SecurityProtocol

/-- Canonical reconfiguration profile carried by the invariant space. -/
abbrev ReconfigurationProfile := Distributed.Reconfiguration.ReconfigurationProtocol

/-- Canonical atomic-broadcast profile carried by the invariant space. -/
abbrev AtomicBroadcastProfile := Distributed.AtomicBroadcast.AtomicBroadcastProtocol

/-- Canonical accountable-safety profile carried by the invariant space. -/
abbrev AccountableSafetyProfile := Distributed.AccountableSafety.AccountableProtocol

/-- Canonical failure-detector boundary profile carried by the invariant space. -/
abbrev FailureDetectorsProfile := Distributed.FailureDetectors.BoundaryProtocol

/-- Canonical data-availability profile carried by the invariant space. -/
abbrev DataAvailabilityProfile := Distributed.DataAvailability.DAProtocol

/-- Canonical coordination-characterization profile carried by the invariant space. -/
abbrev CoordinationProfile := Distributed.Coordination.CoordinationProtocol

/-- Canonical CRDT theorem-family profile carried by the invariant space. -/
abbrev CRDTProfile := Distributed.CRDT.CRDTProtocol

/-- Canonical Byzantine-safety theorem-family profile carried by the invariant space. -/
abbrev ByzantineSafetyProfile := Distributed.ByzantineSafety.SafetyProtocol

/-- Canonical consensus-envelope theorem-family profile carried by the invariant space. -/
abbrev ConsensusEnvelopeProfile := Distributed.ConsensusEnvelope.ConsensusEnvelopeProtocol

/-- Canonical failure-envelope theorem-family profile carried by the invariant space. -/
abbrev FailureEnvelopeProfile := Runtime.Adequacy.FailureEnvelopeProtocol

/-- Canonical protocol machine envelope-adherence theorem-family profile carried by the invariant space. -/
abbrev ProtocolMachineEnvelopeAdherenceProfile := Runtime.Adequacy.ProtocolMachineEnvelopeAdherenceProtocol

/-- Canonical protocol machine envelope-admission theorem-family profile carried by the invariant space. -/
abbrev ProtocolMachineEnvelopeAdmissionProfile := Runtime.Adequacy.ProtocolMachineEnvelopeAdmissionProtocol

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
  byzantineSafety? : Option ByzantineSafetyProfile := none
  consensusEnvelope? : Option ConsensusEnvelopeProfile := none
  failureEnvelope? : Option FailureEnvelopeProfile := none
  protocolMachineEnvelopeAdherence? : Option ProtocolMachineEnvelopeAdherenceProfile := none
  protocolMachineEnvelopeAdmission? : Option ProtocolMachineEnvelopeAdmissionProfile := none
  protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeProfile := none

/-- protocol machine invariant space extended with optional distributed-theory profiles. -/
structure ProtocolMachineInvariantSpaceWithDistributedProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends ProtocolMachineInvariantSpace (ν := ν) store₀ State where
  distributed : DistributedProfiles := {}

end

end Adapters
end Proofs
end Runtime
