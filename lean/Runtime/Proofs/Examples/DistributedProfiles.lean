
import Runtime.Proofs.TheoremPack.Build

/- ## Structured Block 1 -/
set_option autoImplicit false

/-! # Runtime.Proofs.Examples.DistributedProfiles

End-to-end protocol machine examples for distributed theorem spaces:
profile attachment in `ProtocolMachineInvariantSpaceWithProfiles` automatically materializes
the corresponding theorem artifact in `ProtocolMachineTheoremPack`.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

/-- Minimal base invariant space used by theorem-pack examples. -/
def baseSpace (bundle : ProtocolMachineLivenessBundle store₀) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk (some bundle) none none none)
      {})
    {}

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpLowerBound?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpImpossibility?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CAPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCAP p)
    ).capImpossibility?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.QuorumGeometryProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDistributedProfiles
        { quorumGeometry? := some p })
    ).quorumGeometry?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.PartialSynchronyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withPartialSynchrony p)
    ).partialSynchrony?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ResponsivenessProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withResponsiveness p)
    ).responsiveness?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.NakamotoProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto p)
    ).nakamoto?.isSome = true := by
/- ## Structured Block 2 -/
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ReconfigurationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withReconfiguration p)
    ).reconfiguration?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.AtomicBroadcastProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAtomicBroadcast p)
    ).atomicBroadcast?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.AccountableSafetyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAccountableSafety p)
    ).accountableSafety?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FailureDetectorsProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFailureDetectors p)
    ).failureDetectors?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.DataAvailabilityProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDataAvailability p)
    ).dataAvailability?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CoordinationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCoordination p)
    ).coordination?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CoordinationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCoordination p)
    ).calm?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDT p)
    ).crdt?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDT p)
    ).crdtMonotonicity?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.TriangleOfForgettingProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withTriangleOfForgetting p)
    ).triangleOfForgetting?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ByzantineSafetyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withByzantineSafety p)
    ).byzantineSafety?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ConsensusEnvelopeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withConsensusEnvelope p)
    ).consensusEnvelope?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FailureEnvelopeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFailureEnvelope p)
    ).failureEnvelope?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolMachineEnvelopeAdherenceProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolMachineEnvelopeAdherence p)
    ).protocolMachineEnvelopeAdherence?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolMachineEnvelopeAdmissionProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolMachineEnvelopeAdmission p)
    ).protocolMachineEnvelopeAdmission?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolEnvelopeBridgeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolEnvelopeBridge p)
    ).protocolEnvelopeBridge?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
