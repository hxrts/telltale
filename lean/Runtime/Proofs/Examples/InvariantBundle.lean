import Runtime.Proofs.TheoremPack.Build

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.InvariantBundle

One-shot protocol machine invariant-space examples showing automatic theorem derivation for:
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

def baseSpace (bundle : ProtocolMachineLivenessBundle store₀) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk (some bundle) none none none)
      {})
    {}

/-- Liveness bundle in invariant space auto-materializes a termination artifact. -/
example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space := baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle)
    ).termination?.isSome = true := by
  simp [baseSpace, buildProtocolMachineTheoremPack]

/-- Optional progress hypothesis can be recovered from invariant-space evidence. -/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (hNonTerminal : ¬ AllSessionsComplete store₀)
    (hHasProgress : bundle.progressHypothesis?.isSome = true) :
    ProgressEnabled store₀ := by
  let space : ProtocolMachineInvariantSpace (ν := ν) store₀ State :=
    ProtocolMachineInvariantSpace.mk (some bundle) none none none
  exact Adapters.protocol_machine_progress_from_invariant_space
    (space := space)
    (bundle := bundle)
    (hLiveness := rfl)
    hNonTerminal
    hHasProgress

/-- FLP/CAP profiles attached to one bundle auto-materialize both impossibility artifacts. -/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (flp : Adapters.FLPProfile)
    (cap : Adapters.CAPProfile) :
    let space := ((baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP flp).withCAP cap
    let pack := buildProtocolMachineTheoremPack (space := space)
    pack.flpImpossibility?.isSome = true ∧ pack.capImpossibility?.isSome = true := by
  exact ⟨rfl, rfl⟩

/-- Classical Foster profile attached to one bundle auto-materializes a classical artifact. -/
example (bundle : ProtocolMachineLivenessBundle store₀)
    (foster : Adapters.FosterProfile State) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFoster foster)
    ).foster?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.MaxWeightProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { maxWeight? := some p })
    ).maxWeight?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.LDPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { ldp? := some p })
    ).ldp?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.MeanFieldProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { meanField? := some p })
    ).meanField?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.HeavyTrafficProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { heavyTraffic? := some p })
    ).heavyTraffic?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.MixingProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { mixing? := some p })
    ).mixing?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.FluidProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { fluid? := some p })
    ).fluid?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.ConcentrationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { concentration? := some p })
    ).concentration?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.LittlesLawProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { littlesLaw? := some p })
    ).littlesLaw?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀)
    (p : Adapters.FunctionalCLTProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withClassicalProfiles
        { functionalCLT? := some p })
    ).functionalCLT?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
