import Runtime.Proofs.InvariantSpace
import Classical.Transport.API
import Protocol.Classical
import Runtime.Proofs.Adapters.ClassicalCore


set_option autoImplicit false
namespace Runtime
namespace Proofs
namespace Adapters
universe u v
section
variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-- Heavy-traffic artifact; elementary `(σ√n)² = σ²n` identity only. -/
structure HeavyTrafficArtifact where
  profile : HeavyTrafficProfile
  proof : Classical.Transport.HeavyTrafficConclusion profile.input
  diffusionScaleLaw : Classical.Transport.HeavyTrafficDiffusionScaleLaw profile.input

/-- Mixing artifact; derived from an assumed `MixingWitness`. -/
structure MixingArtifact where
  profile : MixingProfile
  proof : Classical.Transport.MixingConclusion profile.input

/-- Fluid artifact; derived from an assumed `FluidDescentWitness`. -/
structure FluidArtifact where
  profile : FluidProfile
  proof : Classical.Transport.FluidConclusion profile.input

/-- Concentration artifact; `tailBound` is the assumed classical input. -/
structure ConcentrationArtifact where
  profile : ConcentrationProfile
  proof : Classical.Transport.ConcentrationConclusion profile.input
  tailBound : Classical.Transport.ConcentrationTailConclusion profile.input

/-- Little's-law artifact; `proof` is the assumed classical input `law`. -/
structure LittlesLawArtifact where
  profile : LittlesLawProfile
  proof : Classical.Transport.LittlesLawConclusion profile.input
  waitTime : Classical.Transport.LittlesLawWaitTimeConclusion profile.input
  throughput : Classical.Transport.LittlesLawThroughputConclusion profile.input

/-- Functional-CLT artifact; degenerate constant-path identity, not a CLT. -/
structure FunctionalCLTArtifact where
  profile : FunctionalCLTProfile
  proof : Classical.Transport.FunctionalCLTConclusion profile.input
  scaledProcessLaw : Classical.Transport.FunctionalCLTScaledProcessLaw profile.input

/-- Spectral-gap artifact; `proof` is the assumed `termination.bounded_by_gap`. -/
structure SpectralGapArtifact (State : Type v) where
  profile : SpectralGapProfile State
  proof :
    @Classical.Transport.SpectralGapConclusion inferInstance State
      profile.instFintype profile.instDecidableEq profile.input

/-! ## Artifact Constructors -/

def fosterArtifactOfProfile
    {State : Type v}
    (p : FosterProfile State) : FosterArtifact State :=
  { profile := p
  , proof := Classical.Transport.foster_conclusion_of_input (input := p.input)
  }

def maxWeightArtifactOfProfile
    (p : MaxWeightProfile) : MaxWeightArtifact :=
  letI : Fintype p.ι := p.instFintype
  { profile := p
  , proof := p.input.choice.optimal
  }

def ldpArtifactOfProfile
    (p : LDPProfile) : LDPArtifact :=
  { profile := p
  , proof := Classical.Transport.ldp_conclusion_of_input p.input
  }

/-! ## Artifact Constructors: Extended Profiles -/

def meanFieldArtifactOfProfile
    (p : MeanFieldProfile) : MeanFieldArtifact :=
  { profile := p
  , proof := Classical.Transport.mean_field_permutation_invariant p.input
  }

def heavyTrafficArtifactOfProfile
    (p : HeavyTrafficProfile) : HeavyTrafficArtifact :=
  { profile := p
  , proof := Classical.Transport.heavy_traffic_scaled_variance_identity p.input
  , diffusionScaleLaw := Classical.Transport.heavy_traffic_scaled_variance_identity p.input
  }

def mixingArtifactOfProfile
    (p : MixingProfile) : MixingArtifact :=
  { profile := p
  , proof := Classical.Transport.mixing_conclusion_of_input p.input
  }

def fluidArtifactOfProfile
    (p : FluidProfile) : FluidArtifact :=
  { profile := p
  , proof := Classical.Transport.fluid_conclusion_of_input p.input
  }

def concentrationArtifactOfProfile
    (p : ConcentrationProfile) : ConcentrationArtifact :=
  { profile := p
  , proof := Classical.Transport.concentration_conclusion_of_input p.input
  , tailBound := p.input.witness.tail_upper
  }

def littlesLawArtifactOfProfile
    (p : LittlesLawProfile) : LittlesLawArtifact :=
  { profile := p
  , proof := p.input.law
  , waitTime := Classical.Transport.littles_law_wait_time_of_input p.input
  , throughput := Classical.Transport.littles_law_throughput_of_input p.input
  }

def functionalCLTArtifactOfProfile
    (p : FunctionalCLTProfile) : FunctionalCLTArtifact :=
  { profile := p
  , proof := Classical.Transport.constant_path_scaled_process_zero p.input
  , scaledProcessLaw := Classical.Transport.constant_path_scaled_process_zero p.input
  }

def spectralGapArtifactOfProfile
    {State : Type v}
    (p : SpectralGapProfile State) : SpectralGapArtifact State :=
  letI : Fintype State := p.instFintype
  letI : DecidableEq State := p.instDecidableEq
  { profile := p
  , proof := p.input.termination.bounded_by_gap
  }

/-! ## Artifact Extraction Theorems -/

/-- Extract the Foster conclusion carried by a packaged artifact. -/
theorem fosterConclusionOfArtifact
    {State : Type v}
    (artifact : FosterArtifact State) :
    Classical.Transport.FosterConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the MaxWeight conclusion carried by a packaged artifact. -/
theorem maxWeightConclusionOfArtifact
    (artifact : MaxWeightArtifact) :
    @Classical.Transport.MaxWeightConclusion artifact.profile.ι
      artifact.profile.instFintype artifact.profile.input :=
  artifact.proof

/-- Extract the large-deviation conclusion carried by a packaged artifact. -/
theorem ldpConclusionOfArtifact
    (artifact : LDPArtifact) :
    Classical.Transport.LDPConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the mean-field conclusion carried by a packaged artifact. -/
theorem meanFieldConclusionOfArtifact
    (artifact : MeanFieldArtifact) :
    Classical.Transport.MeanFieldConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the heavy-traffic conclusion carried by a packaged artifact. -/
theorem heavyTrafficConclusionOfArtifact
    (artifact : HeavyTrafficArtifact) :
    Classical.Transport.HeavyTrafficConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the heavy-traffic diffusion-scale law carried by a packaged artifact. -/
theorem heavyTrafficDiffusionScaleLawOfArtifact
    (artifact : HeavyTrafficArtifact) :
    Classical.Transport.HeavyTrafficDiffusionScaleLaw artifact.profile.input :=
  artifact.diffusionScaleLaw

/-- Extract the mixing conclusion carried by a packaged artifact. -/
theorem mixingConclusionOfArtifact
    (artifact : MixingArtifact) :
    Classical.Transport.MixingConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the fluid-limit conclusion carried by a packaged artifact. -/
theorem fluidConclusionOfArtifact
    (artifact : FluidArtifact) :
    Classical.Transport.FluidConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the concentration conclusion carried by a packaged artifact. -/
theorem concentrationConclusionOfArtifact
    (artifact : ConcentrationArtifact) :
    Classical.Transport.ConcentrationConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the concentration tail bound carried by a packaged artifact. -/
theorem concentrationTailConclusionOfArtifact
    (artifact : ConcentrationArtifact) :
    Classical.Transport.ConcentrationTailConclusion artifact.profile.input :=
  artifact.tailBound

/-- Extract the Little's-law conclusion carried by a packaged artifact. -/
theorem littlesLawConclusionOfArtifact
    (artifact : LittlesLawArtifact) :
    Classical.Transport.LittlesLawConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the Little's-law wait-time corollary carried by a packaged artifact. -/
theorem littlesLawWaitTimeConclusionOfArtifact
    (artifact : LittlesLawArtifact) :
    Classical.Transport.LittlesLawWaitTimeConclusion artifact.profile.input :=
  artifact.waitTime

/-- Extract the Little's-law throughput corollary carried by a packaged artifact. -/
theorem littlesLawThroughputConclusionOfArtifact
    (artifact : LittlesLawArtifact) :
    Classical.Transport.LittlesLawThroughputConclusion artifact.profile.input :=
  artifact.throughput

/-- Extract the functional-CLT conclusion carried by a packaged artifact. -/
theorem functionalCLTConclusionOfArtifact
    (artifact : FunctionalCLTArtifact) :
    Classical.Transport.FunctionalCLTConclusion artifact.profile.input :=
  artifact.proof

/-- Extract the functional-CLT scaled-process law carried by a packaged artifact. -/
theorem functionalCLTScaledProcessLawOfArtifact
    (artifact : FunctionalCLTArtifact) :
    Classical.Transport.FunctionalCLTScaledProcessLaw artifact.profile.input :=
  artifact.scaledProcessLaw

/-- Extract the spectral-gap termination conclusion carried by a packaged artifact. -/
theorem spectralGapConclusionOfArtifact
    {State : Type v}
    (artifact : SpectralGapArtifact State) :
    @Classical.Transport.SpectralGapConclusion inferInstance State
      artifact.profile.instFintype artifact.profile.instDecidableEq artifact.profile.input :=
  artifact.proof

/-! ## Classical Profile Bundles -/

/-- Optional classical profile bundle attached to a protocol machine invariant space. -/
structure ClassicalProfiles (State : Type v) where
  foster? : Option (FosterProfile State) := none
  maxWeight? : Option MaxWeightProfile := none
  ldp? : Option LDPProfile := none
  meanField? : Option MeanFieldProfile := none
  heavyTraffic? : Option HeavyTrafficProfile := none
  mixing? : Option MixingProfile := none
  fluid? : Option FluidProfile := none
  concentration? : Option ConcentrationProfile := none
  littlesLaw? : Option LittlesLawProfile := none
  functionalCLT? : Option FunctionalCLTProfile := none
  spectralGap? : Option (SpectralGapProfile State) := none

/-- protocol machine invariant space extended with optional classical profiles. -/
structure ProtocolMachineInvariantSpaceWithClassicalProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends ProtocolMachineInvariantSpace (ν := ν) store₀ State where
  classical : ClassicalProfiles State := {}

/-! ## Classical Theorem Pack Builder -/

/-- Classical theorem pack produced from classical profile evidence. -/
structure ProtocolMachineClassicalTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithClassicalProfiles (ν := ν) store₀ State) where
  foster? : Option (FosterArtifact State)
  maxWeight? : Option MaxWeightArtifact
  ldp? : Option LDPArtifact
  meanField? : Option MeanFieldArtifact
  heavyTraffic? : Option HeavyTrafficArtifact
  mixing? : Option MixingArtifact
  fluid? : Option FluidArtifact
  concentration? : Option ConcentrationArtifact
  littlesLaw? : Option LittlesLawArtifact
  functionalCLT? : Option FunctionalCLTArtifact
  spectralGap? : Option (SpectralGapArtifact State)

/-- Build all classical theorem artifacts from one classical profile bundle. -/
def buildProtocolMachineClassicalTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpaceWithClassicalProfiles (ν := ν) store₀ State) :
    ProtocolMachineClassicalTheoremPack (space := space) :=
  { foster? := space.classical.foster?.map fosterArtifactOfProfile
  , maxWeight? := space.classical.maxWeight?.map maxWeightArtifactOfProfile
  , ldp? := space.classical.ldp?.map ldpArtifactOfProfile
  , meanField? := space.classical.meanField?.map meanFieldArtifactOfProfile
  , heavyTraffic? := space.classical.heavyTraffic?.map heavyTrafficArtifactOfProfile
  , mixing? := space.classical.mixing?.map mixingArtifactOfProfile
  , fluid? := space.classical.fluid?.map fluidArtifactOfProfile
  , concentration? := space.classical.concentration?.map concentrationArtifactOfProfile
  , littlesLaw? := space.classical.littlesLaw?.map littlesLawArtifactOfProfile
  , functionalCLT? := space.classical.functionalCLT?.map functionalCLTArtifactOfProfile
  , spectralGap? := space.classical.spectralGap?.map spectralGapArtifactOfProfile
  }

end

end Adapters
end Proofs
end Runtime
