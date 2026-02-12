import Runtime.Proofs.Adapters.Distributed.ProfileWrappers

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Distributed.ProfileSetters

Attachment helpers for adding distributed profiles to VM invariant spaces.
-/

/-
The Problem. Call sites need focused helpers for attaching distributed profile
witnesses to a `VMInvariantSpaceWithDistributed`.

Solution Structure. Provides strongly-named setters grouped by profile family,
plus a single bulk attachment helper for constructing the full profile bundle.
-/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-! ## Base Profile Setters -/

/-- Attach an FLP profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FLPProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with flp? := some p } }

/-- Attach a CAP profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CAPProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with cap? := some p } }

/-! ## Bulk Profile Setter -/

/-- Attach distributed profiles in one step (profile composition helper). -/
def VMInvariantSpaceWithDistributed.withProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (flp? : Option FLPProfile)
    (cap? : Option CAPProfile)
    (quorumGeometry? : Option QuorumGeometryProfile := none)
    (partialSynchrony? : Option PartialSynchronyProfile := none)
    (responsiveness? : Option ResponsivenessProfile := none)
    (nakamoto? : Option NakamotoProfile := none)
    (reconfiguration? : Option ReconfigurationProfile := none)
    (atomicBroadcast? : Option AtomicBroadcastProfile := none)
    (accountableSafety? : Option AccountableSafetyProfile := none)
    (failureDetectors? : Option FailureDetectorsProfile := none)
    (dataAvailability? : Option DataAvailabilityProfile := none)
    (coordination? : Option CoordinationProfile := none)
    (crdt? : Option CRDTProfile := none)
    (consensusEnvelope? : Option ConsensusEnvelopeProfile := none)
    (failureEnvelope? : Option FailureEnvelopeProfile := none)
    (vmEnvelopeAdherence? : Option VMEnvelopeAdherenceProfile := none)
    (vmEnvelopeAdmission? : Option VMEnvelopeAdmissionProfile := none)
    (protocolEnvelopeBridge? : Option ProtocolEnvelopeBridgeProfile := none) :
    VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed :=
      { flp? := flp?
      , cap? := cap?
      , quorumGeometry? := quorumGeometry?
      , partialSynchrony? := partialSynchrony?
      , responsiveness? := responsiveness?
      , nakamoto? := nakamoto?
      , reconfiguration? := reconfiguration?
      , atomicBroadcast? := atomicBroadcast?
      , accountableSafety? := accountableSafety?
      , failureDetectors? := failureDetectors?
      , dataAvailability? := dataAvailability?
      , coordination? := coordination?
      , crdt? := crdt?
      , consensusEnvelope? := consensusEnvelope?
      , failureEnvelope? := failureEnvelope?
      , vmEnvelopeAdherence? := vmEnvelopeAdherence?
      , vmEnvelopeAdmission? := vmEnvelopeAdmission?
      , protocolEnvelopeBridge? := protocolEnvelopeBridge?
      } }

/-! ## Liveness and Chain Family Setters -/

/-- Attach a quorum-geometry profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : QuorumGeometryProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with quorumGeometry? := some p } }

/-- Attach a partial-synchrony profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : PartialSynchronyProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with partialSynchrony? := some p } }

/-- Attach a responsiveness profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ResponsivenessProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with responsiveness? := some p } }

/-- Attach a Nakamoto-security profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : NakamotoProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with nakamoto? := some p } }

/-- Attach a reconfiguration profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ReconfigurationProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with reconfiguration? := some p } }

/-- Attach an atomic-broadcast profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : AtomicBroadcastProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with atomicBroadcast? := some p } }

/-! ## Envelope and Auxiliary Family Setters -/

/-- Attach an accountable-safety profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : AccountableSafetyProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with accountableSafety? := some p } }

/-- Attach a failure-detector profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FailureDetectorsProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with failureDetectors? := some p } }

/-- Attach a data-availability profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : DataAvailabilityProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with dataAvailability? := some p } }

/-- Attach a coordination profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CoordinationProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with coordination? := some p } }

/-- Attach a CRDT theorem-family profile to a distributed-extended invariant space. -/
def VMInvariantSpaceWithDistributed.withCRDT
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : CRDTProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with crdt? := some p } }

/-! ### Consensus and Failure Envelope Families -/

/-- Attach a consensus-envelope theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withConsensusEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ConsensusEnvelopeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with consensusEnvelope? := some p } }

/-- Attach a failure-envelope theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : FailureEnvelopeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with failureEnvelope? := some p } }

/-! ### VM Envelope and Protocol-Bridge Families -/

/-- Attach a VM envelope-adherence theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withVMEnvelopeAdherence
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : VMEnvelopeAdherenceProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with vmEnvelopeAdherence? := some p } }

/-- Attach a VM envelope-admission theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withVMEnvelopeAdmission
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : VMEnvelopeAdmissionProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with vmEnvelopeAdmission? := some p } }

/-- Attach a protocol-envelope-bridge theorem-family profile to a distributed space. -/
def VMInvariantSpaceWithDistributed.withProtocolEnvelopeBridge
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithDistributed (ν := ν) store₀ State)
    (p : ProtocolEnvelopeBridgeProfile) : VMInvariantSpaceWithDistributed store₀ State :=
  { space with distributed := { space.distributed with protocolEnvelopeBridge? := some p } }

end

end Adapters
end Proofs
end Runtime
