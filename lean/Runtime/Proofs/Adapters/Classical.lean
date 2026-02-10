import Runtime.Proofs.InvariantSpace
import Classical.Transport.API

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Classical

Adapters from invariant-space classical hypotheses to transported theorem
artifacts.
-/

/-! ## Core Development -/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Build a transport context from a classical witness and a VM step function. -/
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

/-- Foster theorem derived from a Foster profile. -/
theorem foster_of_profile
    {State : Type v}
    (p : FosterProfile State) :
    Classical.Transport.FosterConclusion p.input := by
  exact Classical.Transport.transported_fosterLyapunov (input := p.input)

/-- MaxWeight theorem derived from a MaxWeight profile. -/
theorem maxWeight_of_profile
    (p : MaxWeightProfile) :
    @Classical.Transport.MaxWeightConclusion p.ι p.instFintype p.input := by
  letI : Fintype p.ι := p.instFintype
  simpa using
    (Classical.Transport.transported_maxWeight (ι := p.ι) (input := p.input))

/-- LDP theorem derived from an LDP profile. -/
theorem ldp_of_profile
    (p : LDPProfile) :
    Classical.Transport.LDPConclusion p.input := by
  exact Classical.Transport.transported_ldp p.input

/-- Mean-field theorem derived from a mean-field profile. -/
theorem meanField_of_profile
    (p : MeanFieldProfile) :
    Classical.Transport.MeanFieldConclusion p.input := by
  exact Classical.Transport.transported_meanField p.input

/-- Heavy-traffic theorem derived from a heavy-traffic profile. -/
theorem heavyTraffic_of_profile
    (p : HeavyTrafficProfile) :
    Classical.Transport.HeavyTrafficConclusion p.input := by
  exact Classical.Transport.transported_heavyTraffic p.input

/-- Mixing-time theorem derived from a mixing profile. -/
theorem mixing_of_profile
    (p : MixingProfile) :
    Classical.Transport.MixingConclusion p.input := by
  exact Classical.Transport.transported_mixing p.input

/-- Fluid-limit theorem derived from a fluid profile. -/
theorem fluid_of_profile
    (p : FluidProfile) :
    Classical.Transport.FluidConclusion p.input := by
  exact Classical.Transport.transported_fluidLimit p.input

/-- Concentration theorem derived from a concentration profile. -/
theorem concentration_of_profile
    (p : ConcentrationProfile) :
    Classical.Transport.ConcentrationConclusion p.input := by
  exact Classical.Transport.transported_concentration p.input

/-- Little's-law theorem derived from a Little's-law profile. -/
theorem littlesLaw_of_profile
    (p : LittlesLawProfile) :
    Classical.Transport.LittlesLawConclusion p.input := by
  exact Classical.Transport.transported_littlesLaw p.input

/-- Functional CLT theorem derived from a functional-CLT profile. -/
theorem functionalCLT_of_profile
    (p : FunctionalCLTProfile) :
    Classical.Transport.FunctionalCLTConclusion p.input := by
  exact Classical.Transport.transported_functionalCLT p.input

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

/-- Packaged Little's-law transport artifact. -/
structure LittlesLawArtifact where
  profile : LittlesLawProfile
  proof : Classical.Transport.LittlesLawConclusion profile.input

/-- Packaged functional-CLT transport artifact. -/
structure FunctionalCLTArtifact where
  profile : FunctionalCLTProfile
  proof : Classical.Transport.FunctionalCLTConclusion profile.input

def fosterArtifactOfProfile
    {State : Type v}
    (p : FosterProfile State) : FosterArtifact State :=
  { profile := p
  , proof := foster_of_profile p
  }

def maxWeightArtifactOfProfile
    (p : MaxWeightProfile) : MaxWeightArtifact :=
  { profile := p
  , proof := maxWeight_of_profile p
  }

def ldpArtifactOfProfile
    (p : LDPProfile) : LDPArtifact :=
  { profile := p
  , proof := ldp_of_profile p
  }

def meanFieldArtifactOfProfile
    (p : MeanFieldProfile) : MeanFieldArtifact :=
  { profile := p
  , proof := meanField_of_profile p
  }

def heavyTrafficArtifactOfProfile
    (p : HeavyTrafficProfile) : HeavyTrafficArtifact :=
  { profile := p
  , proof := heavyTraffic_of_profile p
  }

def mixingArtifactOfProfile
    (p : MixingProfile) : MixingArtifact :=
  { profile := p
  , proof := mixing_of_profile p
  }

def fluidArtifactOfProfile
    (p : FluidProfile) : FluidArtifact :=
  { profile := p
  , proof := fluid_of_profile p
  }

def concentrationArtifactOfProfile
    (p : ConcentrationProfile) : ConcentrationArtifact :=
  { profile := p
  , proof := concentration_of_profile p
  }

def littlesLawArtifactOfProfile
    (p : LittlesLawProfile) : LittlesLawArtifact :=
  { profile := p
  , proof := littlesLaw_of_profile p
  }

def functionalCLTArtifactOfProfile
    (p : FunctionalCLTProfile) : FunctionalCLTArtifact :=
  { profile := p
  , proof := functionalCLT_of_profile p
  }

def fosterArtifactOfProfile?
    {State : Type v}
    (p? : Option (FosterProfile State)) : Option (FosterArtifact State) :=
  p?.map fosterArtifactOfProfile

def maxWeightArtifactOfProfile?
    (p? : Option MaxWeightProfile) : Option MaxWeightArtifact :=
  p?.map maxWeightArtifactOfProfile

def ldpArtifactOfProfile?
    (p? : Option LDPProfile) : Option LDPArtifact :=
  p?.map ldpArtifactOfProfile

def meanFieldArtifactOfProfile?
    (p? : Option MeanFieldProfile) : Option MeanFieldArtifact :=
  p?.map meanFieldArtifactOfProfile

def heavyTrafficArtifactOfProfile?
    (p? : Option HeavyTrafficProfile) : Option HeavyTrafficArtifact :=
  p?.map heavyTrafficArtifactOfProfile

def mixingArtifactOfProfile?
    (p? : Option MixingProfile) : Option MixingArtifact :=
  p?.map mixingArtifactOfProfile

def fluidArtifactOfProfile?
    (p? : Option FluidProfile) : Option FluidArtifact :=
  p?.map fluidArtifactOfProfile

def concentrationArtifactOfProfile?
    (p? : Option ConcentrationProfile) : Option ConcentrationArtifact :=
  p?.map concentrationArtifactOfProfile

def littlesLawArtifactOfProfile?
    (p? : Option LittlesLawProfile) : Option LittlesLawArtifact :=
  p?.map littlesLawArtifactOfProfile

def functionalCLTArtifactOfProfile?
    (p? : Option FunctionalCLTProfile) : Option FunctionalCLTArtifact :=
  p?.map functionalCLTArtifactOfProfile

/-- Optional classical profile bundle attached to a VM invariant space. -/
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

/-- VM invariant space extended with optional classical profiles. -/
structure VMInvariantSpaceWithClassical
    (store₀ : SessionStore ν) (State : Type v)
    extends VMInvariantSpace (ν := ν) store₀ State where
  classical : ClassicalProfiles State := {}

def VMInvariantSpaceWithClassical.withProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (profiles : ClassicalProfiles State) :
    VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := profiles }

def VMInvariantSpaceWithClassical.withFoster
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : FosterProfile State) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with foster? := some p } }

def VMInvariantSpaceWithClassical.withMaxWeight
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : MaxWeightProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with maxWeight? := some p } }

def VMInvariantSpaceWithClassical.withLDP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : LDPProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with ldp? := some p } }

def VMInvariantSpaceWithClassical.withMeanField
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : MeanFieldProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with meanField? := some p } }

def VMInvariantSpaceWithClassical.withHeavyTraffic
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : HeavyTrafficProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with heavyTraffic? := some p } }

def VMInvariantSpaceWithClassical.withMixing
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : MixingProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with mixing? := some p } }

def VMInvariantSpaceWithClassical.withFluid
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : FluidProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with fluid? := some p } }

def VMInvariantSpaceWithClassical.withConcentration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : ConcentrationProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with concentration? := some p } }

def VMInvariantSpaceWithClassical.withLittlesLaw
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : LittlesLawProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with littlesLaw? := some p } }

def VMInvariantSpaceWithClassical.withFunctionalCLT
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State)
    (p : FunctionalCLTProfile) : VMInvariantSpaceWithClassical store₀ State :=
  { space with classical := { space.classical with functionalCLT? := some p } }

/-- Classical theorem pack produced from classical profile evidence. -/
structure VMClassicalTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State) where
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

/-- Build all classical theorem artifacts from one classical profile bundle. -/
def buildVMClassicalTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithClassical (ν := ν) store₀ State) :
    VMClassicalTheoremPack (space := space) :=
  { foster? := fosterArtifactOfProfile? space.classical.foster?
  , maxWeight? := maxWeightArtifactOfProfile? space.classical.maxWeight?
  , ldp? := ldpArtifactOfProfile? space.classical.ldp?
  , meanField? := meanFieldArtifactOfProfile? space.classical.meanField?
  , heavyTraffic? := heavyTrafficArtifactOfProfile? space.classical.heavyTraffic?
  , mixing? := mixingArtifactOfProfile? space.classical.mixing?
  , fluid? := fluidArtifactOfProfile? space.classical.fluid?
  , concentration? := concentrationArtifactOfProfile? space.classical.concentration?
  , littlesLaw? := littlesLawArtifactOfProfile? space.classical.littlesLaw?
  , functionalCLT? := functionalCLTArtifactOfProfile? space.classical.functionalCLT?
  }

end

end Adapters
end Proofs
end Runtime
