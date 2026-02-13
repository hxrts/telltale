
import Runtime.Proofs.TheoremPack

/- ## Structured Block 1 -/
set_option autoImplicit false

/-! # Runtime.Proofs.Examples.DistributedProfiles

End-to-end VM examples for distributed theorem spaces:
profile attachment in `VMInvariantSpaceWithProfiles` automatically materializes
the corresponding theorem artifact in `VMTheoremPack`.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

/-- Minimal base invariant space used by theorem-pack examples. -/
def baseSpace (bundle : VMLivenessBundle store₀) :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  VMInvariantSpaceWithProfiles.mk
    (Adapters.VMInvariantSpaceWithDistributed.mk
      (VMInvariantSpace.mk (some bundle) none none)
      {})
    {}

example (bundle : VMLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpLowerBound?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpImpossibility?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.CAPProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCAP p)
    ).capImpossibility?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.QuorumGeometryProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDistributedProfiles
        { quorumGeometry? := some p })
    ).quorumGeometry?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.PartialSynchronyProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withPartialSynchrony p)
    ).partialSynchrony?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.ResponsivenessProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withResponsiveness p)
    ).responsiveness?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.NakamotoProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto p)
    ).nakamoto?.isSome = true := by
/- ## Structured Block 2 -/
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.ReconfigurationProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withReconfiguration p)
    ).reconfiguration?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.AtomicBroadcastProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAtomicBroadcast p)
    ).atomicBroadcast?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.AccountableSafetyProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAccountableSafety p)
    ).accountableSafety?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.FailureDetectorsProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFailureDetectors p)
    ).failureDetectors?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.DataAvailabilityProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDataAvailability p)
    ).dataAvailability?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.CoordinationProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCoordination p)
    ).coordination?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀) (p : Adapters.CRDTProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDT p)
    ).crdt?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
