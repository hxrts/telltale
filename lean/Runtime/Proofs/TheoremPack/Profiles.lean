import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Distributed
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.CompileTime.DeterminismApi

set_option autoImplicit false

/-! # Runtime.Proofs.TheoremPack

One-shot theorem packaging from a VM invariant space carrying distributed and
classical optional profiles.
-/

/-
The Problem. Users need a single entry point to obtain all applicable runtime
theorems for a given VM state, including optional distributed impossibility
results and classical analysis bounds.

Solution Structure. Defines `VMInvariantSpaceWithProfiles` combining distributed
and classical profiles. Provides projection functions to view the space as
distributed-only or classical-only. The packaging functions generate theorem
bundles from the combined invariant space in one shot.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Combined invariant space carrying distributed and classical profiles. -/
structure VMInvariantSpaceWithProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends Adapters.VMInvariantSpaceWithDistributed (ν := ν) store₀ State where
  classical : Adapters.ClassicalProfiles State := {}

/-- Forget classical profiles and view the space as distributed-only. -/
def VMInvariantSpaceWithProfiles.toDistributedSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithDistributed store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , distributed := space.distributed
  }

/-- Forget distributed profiles and view the space as classical-only. -/
def VMInvariantSpaceWithProfiles.toClassicalSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithClassical store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , classical := space.classical
  }

/-- Attach distributed profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (distributed : Adapters.DistributedProfiles) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := distributed }

/-- Attach classical profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (classical : Adapters.ClassicalProfiles State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := classical }

/-- Generic distributed-profile updater used by profile-specific setters. -/
def VMInvariantSpaceWithProfiles.updateDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.DistributedProfiles → Adapters.DistributedProfiles) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := update space.distributed }

/-- Generic classical-profile updater used by profile-specific setters. -/
def VMInvariantSpaceWithProfiles.updateClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (update : Adapters.ClassicalProfiles State → Adapters.ClassicalProfiles State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := update space.classical }

/-- Attach an FLP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FLPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with flp? := some p })

/-- Attach a CAP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CAPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with cap? := some p })

/-- Attach a quorum-geometry distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.QuorumGeometryProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with quorumGeometry? := some p })

/-- Attach a partial-synchrony distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.PartialSynchronyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with partialSynchrony? := some p })

/-- Attach a responsiveness distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ResponsivenessProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with responsiveness? := some p })

/-- Attach a Nakamoto distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.NakamotoProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with nakamoto? := some p })

/-- Attach a reconfiguration distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ReconfigurationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with reconfiguration? := some p })

/-- Attach an atomic-broadcast distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AtomicBroadcastProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with atomicBroadcast? := some p })

/-- Attach an accountable-safety distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AccountableSafetyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with accountableSafety? := some p })

/-- Attach a failure-detector distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureDetectorsProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureDetectors? := some p })

/-- Attach a data-availability distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.DataAvailabilityProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with dataAvailability? := some p })

/-- Attach a coordination distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CoordinationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with coordination? := some p })

/-- Attach a CRDT distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCRDT
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CRDTProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with crdt? := some p })

/-- Attach a consensus-envelope distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withConsensusEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ConsensusEnvelopeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with consensusEnvelope? := some p })

/-- Attach a failure-envelope distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFailureEnvelope
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureEnvelopeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with failureEnvelope? := some p })

/-- Attach a VM-envelope-adherence distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withVMEnvelopeAdherence
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.VMEnvelopeAdherenceProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with vmEnvelopeAdherence? := some p })

/-- Attach a VM-envelope-admission distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withVMEnvelopeAdmission
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.VMEnvelopeAdmissionProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with vmEnvelopeAdmission? := some p })

/-- Attach a protocol-envelope-bridge distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withProtocolEnvelopeBridge
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ProtocolEnvelopeBridgeProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateDistributedProfiles space
    (fun distributed => { distributed with protocolEnvelopeBridge? := some p })

/-- Attach a Foster profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFoster
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FosterProfile State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  VMInvariantSpaceWithProfiles.updateClassicalProfiles space
    (fun classical => { classical with foster? := some p })

/-- Packaged FLP lower-bound artifact. -/

end

end Proofs
end Runtime
