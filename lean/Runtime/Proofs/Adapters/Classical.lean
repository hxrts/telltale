import Runtime.Proofs.InvariantSpace
import Classical.Transport.API
import Protocol.Classical

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Classical

Adapters from invariant-space classical hypotheses to transported theorem
artifacts.
-/

/-
The Problem. Classical analysis theorems (Foster-Lyapunov stability, MaxWeight
scheduling, large deviations) exist in the Mathematical Physics library but need
to be instantiated with protocol machine-specific invariant spaces and step functions to yield
runtime guarantees.

Solution Structure. Provides profile wrappers (FosterProfile, MaxWeightProfile,
LDPProfile) that bundle transport contexts with inputs, then adapters that convert
classical witnesses from the invariant space into the required transport format.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable [EntropyAPI.AnalysisLaws]

/-- Build a transport context from a classical witness and a protocol machine step function. -/
def transportCtxOfWitness
    {State : Type v}
    (step : State → State)
    (w : ClassicalTransportWitness State) :
    Classical.Transport.TransportCtx State :=
  { step := step
  , coherent := w.coherent
  , harmony := w.harmony
  , finiteState := w.finiteState
  }

/-! ## Classical Profile Wrappers -/

/-- Profile wrapper for Foster-Lyapunov transport. -/
structure FosterProfile (State : Type v) where
  ctx : Classical.Transport.TransportCtx State
  input : Classical.Transport.FosterInput State ctx

/-- Profile wrapper for MaxWeight transport. -/
structure MaxWeightProfile where
  ι : Type
  instFintype : Fintype ι
  input : @Classical.Transport.MaxWeightInput ι instFintype

/-- Profile wrapper for LDP transport. -/
structure LDPProfile where
  input : Classical.Transport.LDPInput

/-- Profile wrapper for mean-field transport. -/
structure MeanFieldProfile where
  n : Nat
  input : Classical.Transport.MeanFieldInput n

/-- Profile wrapper for heavy-traffic transport. -/
structure HeavyTrafficProfile where
  input : Classical.Transport.HeavyTrafficInput

/-- Profile wrapper for mixing-time transport. -/
structure MixingProfile where
  input : Classical.Transport.MixingInput

/-- Profile wrapper for fluid-limit transport. -/
structure FluidProfile where
  input : Classical.Transport.FluidInput

/-- Profile wrapper for concentration transport. -/
structure ConcentrationProfile where
  input : Classical.Transport.ConcentrationInput

/-- Profile wrapper for Little's-law transport. -/
structure LittlesLawProfile where
  input : Classical.Transport.LittlesLawInput

/-- Profile wrapper for functional CLT transport. -/
structure FunctionalCLTProfile where
  input : Classical.Transport.FunctionalCLTInput

/-- Profile wrapper for spectral-gap termination transport. -/
structure SpectralGapProfile (State : Type v) where
  instFintype : Fintype State
  instDecidableEq : DecidableEq State
  input :
    @Classical.Transport.SpectralGapInput inferInstance State instFintype
      instDecidableEq

/-! ## Profile Constructors -/

/-- Build a runtime Foster profile from an explicit transport context and input. -/
def mkFosterProfile
    {State : Type v}
    (ctx : Classical.Transport.TransportCtx State)
    (input : Classical.Transport.FosterInput State ctx) :
    FosterProfile State :=
  { ctx := ctx
  , input := input
  }

/-- Build a runtime MaxWeight profile from a transport input. -/
def mkMaxWeightProfile
    {ι : Type} [Fintype ι]
    (input : Classical.Transport.MaxWeightInput ι) :
    MaxWeightProfile :=
  { ι := ι
  , instFintype := inferInstance
  , input := input
  }

/-- Build a runtime large-deviation profile from a transport input. -/
def mkLDPProfile
    (input : Classical.Transport.LDPInput) :
    LDPProfile :=
  { input := input }

/-- Build a runtime mean-field profile from a transport input. -/
def mkMeanFieldProfile
    {n : Nat}
    (input : Classical.Transport.MeanFieldInput n) :
    MeanFieldProfile :=
  { n := n
  , input := input
  }

/-- Build a runtime heavy-traffic profile from a transport input. -/
def mkHeavyTrafficProfile
    (input : Classical.Transport.HeavyTrafficInput) :
    HeavyTrafficProfile :=
  { input := input }

/-- Build a runtime mixing profile from a transport input. -/
def mkMixingProfile
    (input : Classical.Transport.MixingInput) :
    MixingProfile :=
  { input := input }

/-- Build a runtime fluid-limit profile from a transport input. -/
def mkFluidProfile
    (input : Classical.Transport.FluidInput) :
    FluidProfile :=
  { input := input }

/-- Build a runtime concentration profile from a transport input. -/
def mkConcentrationProfile
    (input : Classical.Transport.ConcentrationInput) :
    ConcentrationProfile :=
  { input := input }

/-- Build a runtime Little's-law profile from a transport input. -/
def mkLittlesLawProfile
    (input : Classical.Transport.LittlesLawInput) :
    LittlesLawProfile :=
  { input := input }

/-- Build a runtime functional-CLT profile from a transport input. -/
def mkFunctionalCLTProfile
    (input : Classical.Transport.FunctionalCLTInput) :
    FunctionalCLTProfile :=
  { input := input }

/-- Build a runtime spectral-gap termination profile from a transport input. -/
def mkSpectralGapProfile
    {State : Type v} [Fintype State] [DecidableEq State]
    (input : Classical.Transport.SpectralGapInput State) :
    SpectralGapProfile State :=
  { instFintype := inferInstance
  , instDecidableEq := inferInstance
  , input := input
  }

/-! ## Protocol-Facing Profile Constructors -/

/-- Lift protocol Foster side conditions into a runtime Foster profile. -/
def mkProtocolFosterProfile
    (step : ProtocolClassical.FStep)
    (μ : ProtocolClassical.ProgressMeasureComponents)
    (h : ProtocolClassical.FosterLivenessAssumptions step μ)
    (hSide : ProtocolClassical.ProtocolFosterSideConditions) :
    FosterProfile ProtocolClassical.WTConfigNState :=
  mkFosterProfile (ProtocolClassical.protocolFosterCtx step hSide)
    (ProtocolClassical.protocolFosterInput step μ h hSide)

/-- Lift protocol MaxWeight data into a runtime MaxWeight profile. -/
def mkProtocolMaxWeightProfile
    {ι : Type} [Fintype ι]
    (bufferOccupancy : ι → Nat)
    (sched : ProtocolClassical.ProtocolSchedule ι)
    (hOptimal :
      ∀ ν : ι → Real,
        Classical.MaxWeightBackpressure.weight
            (ProtocolClassical.queueWeightsFromBuffers bufferOccupancy) ν ≤
          Classical.MaxWeightBackpressure.weight
            (ProtocolClassical.queueWeightsFromBuffers bufferOccupancy) sched) :
    MaxWeightProfile :=
  mkMaxWeightProfile
    (ProtocolClassical.mkProtocolMaxWeightInput bufferOccupancy sched hOptimal)

/-- Lift a protocol rare-event model into a runtime large-deviation profile. -/
def mkProtocolLDPProfileFromModel
    (m : ProtocolClassical.ProtocolLDPModel) :
    LDPProfile :=
  mkLDPProfile (ProtocolClassical.mkProtocolLDPInputFromModel m)

/-- Lift protocol rate data into a runtime heavy-traffic profile. -/
def mkProtocolHeavyTrafficProfile
    (arrivalRate serviceRate : Real)
    (n : Nat) :
    HeavyTrafficProfile :=
  mkHeavyTrafficProfile
    (ProtocolClassical.mkProtocolHeavyTrafficInput arrivalRate serviceRate n)

/-- Lift a protocol mixing model into a runtime mixing profile. -/
def mkProtocolMixingProfileFromModel
    (m : ProtocolClassical.ProtocolMixingModel) :
    MixingProfile :=
  mkMixingProfile (ProtocolClassical.mkProtocolMixingInputFromModel m)

/-- Lift a protocol fluid model into a runtime fluid-limit profile. -/
def mkProtocolFluidProfileFromModel
    (m : ProtocolClassical.ProtocolFluidModel) :
    FluidProfile :=
  mkFluidProfile (ProtocolClassical.mkProtocolFluidInputFromModel m)

/-- Lift a protocol concentration model into a runtime concentration profile. -/
def mkProtocolConcentrationProfileFromModel
    (m : ProtocolClassical.ProtocolConcentrationModel) :
    ConcentrationProfile :=
  mkConcentrationProfile (ProtocolClassical.mkProtocolConcentrationInputFromModel m)

/-- Lift a protocol Little's-law model into a runtime Little's-law profile. -/
def mkProtocolLittlesLawProfile
    (m : ProtocolClassical.ProtocolLittleModel) :
    LittlesLawProfile :=
  mkLittlesLawProfile (ProtocolClassical.mkProtocolLittleInput m)

/-- Lift a protocol functional-CLT model into a runtime functional-CLT profile. -/
def mkProtocolFunctionalCLTProfile
    (m : ProtocolClassical.ProtocolFunctionalCLTModel) :
    FunctionalCLTProfile :=
  mkFunctionalCLTProfile (ProtocolClassical.mkProtocolFunctionalCLTInput m)

/-- Lift a protocol mean-field model into a runtime mean-field profile. -/
def mkProtocolMeanFieldProfile
    (m : ProtocolClassical.ProtocolMeanFieldModel) :
    MeanFieldProfile :=
  mkMeanFieldProfile (ProtocolClassical.mkProtocolMeanFieldInput m)

/-- Lift protocol spectral-gap termination witnesses into a runtime spectral-gap profile. -/
def mkProtocolSpectralGapProfile
    [DecidableEq ProtocolClassical.WTConfigN] [Fintype ProtocolClassical.WTConfigN]
    (step : ProtocolClassical.FStep)
    (gap_pos :
      Classical.SpectralGapTermination.SpectralGapPos
        (ProtocolClassical.wtConfigNMarkovChain step))
    (termination :
      Classical.SpectralGapTermination.TerminationWitness
        (ProtocolClassical.wtConfigNMarkovChain step)) :
    SpectralGapProfile ProtocolClassical.WTConfigN :=
  mkSpectralGapProfile
    (Classical.Transport.mkSpectralGapInput
      (ProtocolClassical.wtConfigNMarkovChain step) gap_pos termination)

/-! ## Packaged Classical Artifacts -/

/-- Packaged Foster transport artifact. -/
structure FosterArtifact (State : Type v) where
  profile : FosterProfile State
  proof : Classical.Transport.FosterConclusion profile.input

/-- Packaged MaxWeight transport artifact. -/
structure MaxWeightArtifact where
  profile : MaxWeightProfile
  proof : @Classical.Transport.MaxWeightConclusion
    profile.ι profile.instFintype profile.input

/-- Packaged LDP transport artifact. -/
structure LDPArtifact where
  profile : LDPProfile
  proof : Classical.Transport.LDPConclusion profile.input

/-- Packaged mean-field transport artifact. -/
structure MeanFieldArtifact where
  profile : MeanFieldProfile
  proof : Classical.Transport.MeanFieldConclusion profile.input

/-- Packaged heavy-traffic transport artifact. -/
structure HeavyTrafficArtifact where
  profile : HeavyTrafficProfile
  proof : Classical.Transport.HeavyTrafficConclusion profile.input
  diffusionScaleLaw : Classical.Transport.HeavyTrafficDiffusionScaleLaw profile.input

/-- Packaged mixing-time transport artifact. -/
structure MixingArtifact where
  profile : MixingProfile
  proof : Classical.Transport.MixingConclusion profile.input

/-- Packaged fluid-limit transport artifact. -/
structure FluidArtifact where
  profile : FluidProfile
  proof : Classical.Transport.FluidConclusion profile.input

/-- Packaged concentration transport artifact. -/
structure ConcentrationArtifact where
  profile : ConcentrationProfile
  proof : Classical.Transport.ConcentrationConclusion profile.input
  tailBound : Classical.Transport.ConcentrationTailConclusion profile.input

/-- Packaged Little's-law transport artifact. -/
structure LittlesLawArtifact where
  profile : LittlesLawProfile
  proof : Classical.Transport.LittlesLawConclusion profile.input
  waitTime : Classical.Transport.LittlesLawWaitTimeConclusion profile.input
  throughput : Classical.Transport.LittlesLawThroughputConclusion profile.input

/-- Packaged functional-CLT transport artifact. -/
structure FunctionalCLTArtifact where
  profile : FunctionalCLTProfile
  proof : Classical.Transport.FunctionalCLTConclusion profile.input
  scaledProcessLaw : Classical.Transport.FunctionalCLTScaledProcessLaw profile.input

/-- Packaged spectral-gap termination transport artifact. -/
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
  , proof := Classical.Transport.transported_foster_lyapunov (input := p.input)
  }

def maxWeightArtifactOfProfile
    (p : MaxWeightProfile) : MaxWeightArtifact :=
  letI : Fintype p.ι := p.instFintype
  { profile := p
  , proof := by
      simpa using
        (Classical.Transport.transported_max_weight (ι := p.ι) (input := p.input))
  }

def ldpArtifactOfProfile
    (p : LDPProfile) : LDPArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_ldp p.input
  }

/-! ## Artifact Constructors: Extended Profiles -/

def meanFieldArtifactOfProfile
    (p : MeanFieldProfile) : MeanFieldArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_mean_field p.input
  }

def heavyTrafficArtifactOfProfile
    (p : HeavyTrafficProfile) : HeavyTrafficArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_heavy_traffic p.input
  , diffusionScaleLaw :=
      Classical.Transport.transported_heavy_traffic_diffusion_scale_law p.input
  }

def mixingArtifactOfProfile
    (p : MixingProfile) : MixingArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_mixing p.input
  }

def fluidArtifactOfProfile
    (p : FluidProfile) : FluidArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_fluid_limit p.input
  }

def concentrationArtifactOfProfile
    (p : ConcentrationProfile) : ConcentrationArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_concentration p.input
  , tailBound := Classical.Transport.transported_concentration_tail p.input
  }

def littlesLawArtifactOfProfile
    (p : LittlesLawProfile) : LittlesLawArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_littles_law p.input
  , waitTime := Classical.Transport.transported_littles_law_wait_time p.input
  , throughput := Classical.Transport.transported_littles_law_throughput p.input
  }

def functionalCLTArtifactOfProfile
    (p : FunctionalCLTProfile) : FunctionalCLTArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_functional_clt p.input
  , scaledProcessLaw :=
      Classical.Transport.transported_functional_clt_scaled_process_law p.input
  }

def spectralGapArtifactOfProfile
    {State : Type v}
    (p : SpectralGapProfile State) : SpectralGapArtifact State :=
  letI : Fintype State := p.instFintype
  letI : DecidableEq State := p.instDecidableEq
  { profile := p
  , proof := Classical.Transport.transported_spectral_gap_termination p.input
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
