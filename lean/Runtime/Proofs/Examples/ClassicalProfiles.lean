import Runtime.Proofs.TheoremPack.Build

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.ClassicalProfiles

Concrete theorem-pack examples for classical profile constructors.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν}
variable [EntropyAPI.AnalysisLaws]

/-- Minimal base space used by classical theorem-pack examples. -/
def classicalBaseSpaceFor (State : Type) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk none none none none)
      {})
    {}

/-- Minimal unit-state base space used by most concrete examples. -/
abbrev classicalBaseSpace :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ Unit :=
  classicalBaseSpaceFor (ν := ν) (store₀ := store₀) Unit

/-! ## Concrete Profiles -/

def unitFosterCtx : Classical.Transport.TransportCtx Unit :=
  { step := id
  , coherent := fun _ => True
  , harmony := True
  , finiteState := True
  }

def unitFosterSystem : Classical.FosterLyapunovHarris.DriftSystem Unit :=
  { step := id
  , V := fun _ => 0
  , nonincrease := by intro s; cases s; simp
  , strict_on_pos := by intro s h; cases s; simp at h
  }

def unitFosterProfile : Adapters.FosterProfile Unit :=
  Adapters.mkFosterProfile unitFosterCtx
    (Classical.Transport.mkFosterInput unitFosterSystem rfl)

def unitMaxWeightProfile : Adapters.MaxWeightProfile :=
  Adapters.mkMaxWeightProfile
    (Classical.Transport.mkMaxWeightInput
      (ι := Unit)
      (fun _ => 0)
      (fun _ => 0)
      (by
        intro ν
        simp [Classical.MaxWeightBackpressure.weight]))

def unitLDPWitness :
    Classical.LargeDeviationPrinciple.LDPWitness (fun _ : Nat => (0 : Real)) :=
  { C := 1
  , ρ := 1
  , C_nonneg := by norm_num
  , rho_nonneg := by norm_num
  , rho_le_one := by norm_num
  , tail_upper := by
      intro n
      simp [Classical.LargeDeviationPrinciple.exponentialEnvelope]
  }

def unitLDPProfile : Adapters.LDPProfile :=
  Adapters.mkLDPProfile
    (Classical.Transport.mkLDPInput (fun _ : Nat => (0 : Real)) unitLDPWitness)

def unitMeanFieldProfile : Adapters.MeanFieldProfile :=
  Adapters.mkMeanFieldProfile
    (Classical.Transport.mkMeanFieldInput (n := 1) (fun _ => (0 : Real)))

def unitHeavyTrafficProfile : Adapters.HeavyTrafficProfile :=
  Adapters.mkHeavyTrafficProfile
    (Classical.Transport.mkHeavyTrafficInput 1 1)

def unitMixingWitness :
    Classical.MixingTimeBounds.MixingWitness (fun _ : Nat => (0 : Real)) :=
  { C := 1
  , ρ := 1
  , C_nonneg := by norm_num
  , rho_nonneg := by norm_num
  , rho_le_one := by norm_num
  , dist_upper := by
      intro n
      simp [Classical.MixingTimeBounds.geometricEnvelope]
  }

def unitMixingProfile : Adapters.MixingProfile :=
  Adapters.mkMixingProfile
    (Classical.Transport.mkMixingInput (fun _ : Nat => (0 : Real)) unitMixingWitness)

def unitFluidWitness :
    Classical.FluidLimitStability.FluidDescentWitness (fun _ : Nat => (0 : Real)) :=
  { κ := 0
  , kappa_nonneg := by norm_num
  , descent := by
      intro n
      simp [Classical.FluidLimitStability.energy]
  }

def unitFluidProfile : Adapters.FluidProfile :=
  Adapters.mkFluidProfile
    (Classical.Transport.mkFluidInput (fun _ : Nat => (0 : Real)) unitFluidWitness)

def unitConcentrationWitness :
    Classical.ConcentrationInequalities.ConcentrationWitness (fun _ : Real => (0 : Real)) :=
  { σ := 1
  , sigma_pos := by norm_num
  , tail_upper := by
      intro t ht
      exact Classical.ConcentrationInequalities.sub_gaussian_tail_nonneg 1 t
  }

def unitConcentrationProfile : Adapters.ConcentrationProfile :=
  Adapters.mkConcentrationProfile
    (Classical.Transport.mkConcentrationInput
      (fun _ : Real => (0 : Real)) unitConcentrationWitness)

def unitLittlesLawProfile : Adapters.LittlesLawProfile :=
  Adapters.mkLittlesLawProfile
    (Classical.Transport.mkLittlesLawInput 0 0 0 (by norm_num))

def unitFunctionalCLTProfile : Adapters.FunctionalCLTProfile :=
  Adapters.mkFunctionalCLTProfile
    (Classical.Transport.mkFunctionalCLTInput 0 1 0 (by norm_num))

/-! ## Pack Materialization Through Per-Family Setters -/

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFoster unitFosterProfile)
    ).foster?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMaxWeight unitMaxWeightProfile)
    ).maxWeight?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withLDP unitLDPProfile)
    ).ldp?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMeanField unitMeanFieldProfile)
    ).meanField?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withHeavyTraffic unitHeavyTrafficProfile)
    ).heavyTraffic?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMixing unitMixingProfile)
    ).mixing?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFluid unitFluidProfile)
    ).fluid?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withConcentration
          unitConcentrationProfile)
    ).concentration?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withLittlesLaw unitLittlesLawProfile)
    ).littlesLaw?.isSome = true := by
  rfl

example :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFunctionalCLT
          unitFunctionalCLTProfile)
    ).functionalCLT?.isSome = true := by
  rfl

example (p : Adapters.SpectralGapProfile Unit) :
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withSpectralGap p)
    ).spectralGapTermination?.isSome = true := by
  rfl

/-! ## Extraction Examples -/

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFoster unitFosterProfile)
      ).foster? = some artifact ∧
        Classical.Transport.FosterConclusion artifact.profile.input := by
  refine ⟨Adapters.fosterArtifactOfProfile unitFosterProfile, rfl, ?_⟩
  exact Adapters.fosterConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMaxWeight
            unitMaxWeightProfile)
      ).maxWeight? = some artifact ∧
        @Classical.Transport.MaxWeightConclusion artifact.profile.ι
          artifact.profile.instFintype artifact.profile.input := by
  refine ⟨Adapters.maxWeightArtifactOfProfile unitMaxWeightProfile, rfl, ?_⟩
  exact Adapters.maxWeightConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withLDP unitLDPProfile)
      ).ldp? = some artifact ∧
        Classical.Transport.LDPConclusion artifact.profile.input := by
  refine ⟨Adapters.ldpArtifactOfProfile unitLDPProfile, rfl, ?_⟩
  exact Adapters.ldpConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMeanField
            unitMeanFieldProfile)
      ).meanField? = some artifact ∧
        Classical.Transport.MeanFieldConclusion artifact.profile.input := by
  refine ⟨Adapters.meanFieldArtifactOfProfile unitMeanFieldProfile, rfl, ?_⟩
  exact Adapters.meanFieldConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withHeavyTraffic
            unitHeavyTrafficProfile)
      ).heavyTraffic? = some artifact ∧
        Classical.Transport.HeavyTrafficDiffusionScaleLaw artifact.profile.input := by
  refine ⟨Adapters.heavyTrafficArtifactOfProfile unitHeavyTrafficProfile, rfl, ?_⟩
  exact Adapters.heavyTrafficDiffusionScaleLawOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMixing unitMixingProfile)
      ).mixing? = some artifact ∧
        Classical.Transport.MixingConclusion artifact.profile.input := by
  refine ⟨Adapters.mixingArtifactOfProfile unitMixingProfile, rfl, ?_⟩
  exact Adapters.mixingConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFluid unitFluidProfile)
      ).fluid? = some artifact ∧
        Classical.Transport.FluidConclusion artifact.profile.input := by
  refine ⟨Adapters.fluidArtifactOfProfile unitFluidProfile, rfl, ?_⟩
  exact Adapters.fluidConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withConcentration
            unitConcentrationProfile)
      ).concentration? = some artifact ∧
        Classical.Transport.ConcentrationTailConclusion artifact.profile.input := by
  refine ⟨Adapters.concentrationArtifactOfProfile unitConcentrationProfile, rfl, ?_⟩
  exact Adapters.concentrationTailConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withLittlesLaw
            unitLittlesLawProfile)
      ).littlesLaw? = some artifact ∧
        Classical.Transport.LittlesLawThroughputConclusion artifact.profile.input := by
  refine ⟨Adapters.littlesLawArtifactOfProfile unitLittlesLawProfile, rfl, ?_⟩
  exact Adapters.littlesLawThroughputConclusionOfArtifact _

example :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space :=
          (classicalBaseSpace (ν := ν) (store₀ := store₀)).withFunctionalCLT
            unitFunctionalCLTProfile)
      ).functionalCLT? = some artifact ∧
        Classical.Transport.FunctionalCLTScaledProcessLaw artifact.profile.input := by
  refine ⟨Adapters.functionalCLTArtifactOfProfile unitFunctionalCLTProfile, rfl, ?_⟩
  exact Adapters.functionalCLTScaledProcessLawOfArtifact _

example (p : Adapters.SpectralGapProfile Unit) :
    ∃ artifact,
      (buildProtocolMachineTheoremPack
        (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withSpectralGap p)
      ).spectralGapTermination? = some artifact ∧
        @Classical.Transport.SpectralGapConclusion inferInstance Unit
          artifact.profile.instFintype artifact.profile.instDecidableEq
          artifact.profile.input := by
  refine ⟨Adapters.spectralGapArtifactOfProfile p, rfl, ?_⟩
  exact Adapters.spectralGapConclusionOfArtifact _

/-! ## Combined Distributed And Classical Shape -/

example (flp : Adapters.FLPProfile) :
    let space :=
      ((classicalBaseSpace (ν := ν) (store₀ := store₀)).withFLP flp).withLDP
        unitLDPProfile
    let pack := buildProtocolMachineTheoremPack (space := space)
    pack.flpImpossibility?.isSome = true ∧ pack.ldp?.isSome = true := by
  exact ⟨rfl, rfl⟩

/-! ## Protocol Constructor Shape -/

example (m : ProtocolClassical.ProtocolLDPModel) :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withLDP
          (Adapters.mkProtocolLDPProfileFromModel m))
    ).ldp?.isSome = true := by
  rfl

example
    (step : ProtocolClassical.FStep)
    (μ : ProtocolClassical.ProgressMeasureComponents)
    (h : ProtocolClassical.FosterLivenessAssumptions step μ)
    (hSide : ProtocolClassical.ProtocolFosterSideConditions) :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpaceFor (ν := ν) (store₀ := store₀)
          ProtocolClassical.WTConfigNState).withFoster
          (Adapters.mkProtocolFosterProfile step μ h hSide))
    ).foster?.isSome = true := by
  rfl

example
    {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat)
    (sched : ProtocolClassical.ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight
            (ProtocolClassical.queueWeightsFromBuffers bufferOccupancy) ν ≤
          Classical.MaxWeightBackpressure.weight
            (ProtocolClassical.queueWeightsFromBuffers bufferOccupancy) sched) :
    let p := Adapters.mkProtocolMaxWeightProfile bufferOccupancy sched hOptimal
    (buildProtocolMachineTheoremPack
      (space := (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMaxWeight p)
    ).maxWeight?.isSome = true := by
  rfl

example (m : ProtocolClassical.ProtocolMixingModel) :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMixing
          (Adapters.mkProtocolMixingProfileFromModel m))
    ).mixing?.isSome = true := by
  rfl

example (m : ProtocolClassical.ProtocolMeanFieldModel) :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpace (ν := ν) (store₀ := store₀)).withMeanField
          (Adapters.mkProtocolMeanFieldProfile m))
    ).meanField?.isSome = true := by
  rfl

example
    [DecidableEq ProtocolClassical.WTConfigN] [Fintype ProtocolClassical.WTConfigN]
    (step : ProtocolClassical.FStep)
    (gap_pos :
      Classical.SpectralGapTermination.SpectralGapPos
        (ProtocolClassical.wtConfigNMarkovChain step))
    (termination :
      Classical.SpectralGapTermination.TerminationWitness
        (ProtocolClassical.wtConfigNMarkovChain step)) :
    (buildProtocolMachineTheoremPack
      (space :=
        (classicalBaseSpaceFor (ν := ν) (store₀ := store₀)
          ProtocolClassical.WTConfigN).withSpectralGap
          (Adapters.mkProtocolSpectralGapProfile step gap_pos termination))
    ).spectralGapTermination?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
