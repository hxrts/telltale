import Runtime.Proofs.TheoremPack

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.InvariantBundle

One-shot VM invariant-space examples showing automatic theorem derivation for:
- liveness/progress,
- FLP/CAP impossibility spaces,
- classical transport artifacts.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

def baseSpace (bundle : VMLivenessBundle store₀) :
    VMInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  VMInvariantSpaceWithProfiles.mk
    (Adapters.VMInvariantSpaceWithDistributed.mk
      (VMInvariantSpace.mk (some bundle) none none)
      {})
    {}

/-- Liveness bundle in invariant space auto-materializes a termination artifact. -/
example (bundle : VMLivenessBundle store₀) :
    (buildVMTheoremPack
      (space := baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle)
    ).termination?.isSome = true := by
  simp [baseSpace, buildVMTheoremPack]

/-- Optional progress hypothesis can be recovered from invariant-space evidence. -/
example (bundle : VMLivenessBundle store₀)
    (hNonTerminal : ¬ AllSessionsComplete store₀)
    (hHasProgress : bundle.progressHypothesis?.isSome = true) :
    ProgressEnabled store₀ := by
  let space : VMInvariantSpace (ν := ν) store₀ State :=
    VMInvariantSpace.mk (some bundle) none none
  exact Adapters.vm_progress_from_invariant_space
    (space := space)
    (bundle := bundle)
    (hLiveness := rfl)
    hNonTerminal
    hHasProgress

/-- FLP/CAP profiles attached to one bundle auto-materialize both impossibility artifacts. -/
example (bundle : VMLivenessBundle store₀)
    (flp : Adapters.FLPProfile)
    (cap : Adapters.CAPProfile) :
    let space := ((baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP flp).withCAP cap
    let pack := buildVMTheoremPack (space := space)
    pack.flpImpossibility?.isSome = true ∧ pack.capImpossibility?.isSome = true := by
  exact ⟨rfl, rfl⟩

/-- Classical Foster profile attached to one bundle auto-materializes a classical artifact. -/
example (bundle : VMLivenessBundle store₀)
    (foster : Adapters.FosterProfile State) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFoster foster)
    ).foster?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.MaxWeightProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { maxWeight? := some p })
    ).maxWeight?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.LDPProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { ldp? := some p })
    ).ldp?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.MeanFieldProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { meanField? := some p })
    ).meanField?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.HeavyTrafficProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { heavyTraffic? := some p })
    ).heavyTraffic?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.MixingProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { mixing? := some p })
    ).mixing?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.FluidProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { fluid? := some p })
    ).fluid?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.ConcentrationProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { concentration? := some p })
    ).concentration?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.LittlesLawProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { littlesLaw? := some p })
    ).littlesLaw?.isSome = true := by
  rfl

example (bundle : VMLivenessBundle store₀)
    (p : Adapters.FunctionalCLTProfile) :
    (buildVMTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { functionalCLT? := some p })
    ).functionalCLT?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
