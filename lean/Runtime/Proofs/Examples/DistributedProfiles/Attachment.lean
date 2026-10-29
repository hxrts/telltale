import Runtime.Proofs.Examples.DistributedProfiles.Models

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.DistributedProfiles.Attachment

End-to-end checks that profile attachment in
`ProtocolMachineInvariantSpaceWithProfiles` automatically materializes the
corresponding theorem artifact in `ProtocolMachineTheoremPack`.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

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

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withPartialSynchrony
          timedPartialSynchronyProfile)
    ).partialSynchrony?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withResponsiveness
          timedResponsivenessProfile)
    ).responsiveness?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.NakamotoProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto p)
    ).nakamoto?.isSome = true := by

  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto
          tinyNakamotoProfile)
    ).nakamoto?.isSome = true := by
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

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAccountableSafety
          tinyAccountableProfile)
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

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDataAvailability
          tinyDAProfile)
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

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTErasureProfile) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDTErasure p)
    ).crdtErasure?.isSome = true := by
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

/--
BFT path: a quorum-geometry profile induces a Byzantine-safety theorem-pack
artifact without the caller supplying a separate Byzantine safety theorem.
-/
example (bundle : ProtocolMachineLivenessBundle store₀) (q : Adapters.QuorumGeometryProfile) :
    let byz :=
      Distributed.ByzantineSafety.Profile.ofQuorumGeometry
        q bftQuorumSpec bft_quorum_spec_assumptions_passed
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withByzantineSafety byz)
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
