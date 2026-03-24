import Runtime.Proofs.InvariantSpace
import Classical.Transport.API

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Classical

Adapters from invariant-space classical hypotheses to transported theorem
artifacts.
-/

/-
The Problem. Classical analysis theorems (Foster-Lyapunov stability, MaxWeight
scheduling, large deviations) exist in the Mathematical Physics library but need
to be instantiated with VM-specific invariant spaces and step functions to yield
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
  }

def littlesLawArtifactOfProfile
    (p : LittlesLawProfile) : LittlesLawArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_littles_law p.input
  }

def functionalCLTArtifactOfProfile
    (p : FunctionalCLTProfile) : FunctionalCLTArtifact :=
  { profile := p
  , proof := Classical.Transport.transported_functional_clt p.input
  }

/-! ## Classical Profile Bundles -/

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
  }

end

end Adapters
end Proofs
end Runtime
