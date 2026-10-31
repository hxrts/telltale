import Runtime.Proofs.InvariantSpace
import Classical.Transport.API
import Protocol.Classical

/-! # Runtime.Proofs.Adapters.ClassicalCorennClassical profile wrappers, profile constructors, and packaged classical artifact records. Artifact constructors, extraction theorems, and bundles live in `Runtime.Proofs.Adapters.Classical`. -/

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

/- `mkProtocolSpectralGapProfile` was removed: it instantiated the spectral
interface on the deterministic 0/1 protocol kernel, whose spectral gap is
degenerate (see `Protocol.Classical.SpectralGap`). -/

/-! ## Packaged Classical Artifacts -/

/-- Foster artifact; deterministic potential bound derived from the drift input. -/
structure FosterArtifact (State : Type v) where
  profile : FosterProfile State
  proof : Classical.Transport.FosterConclusion profile.input

/-- MaxWeight artifact; `proof` is the assumed classical input `choice.optimal`. -/
structure MaxWeightArtifact where
  profile : MaxWeightProfile
  proof : @Classical.Transport.MaxWeightConclusion
    profile.ι profile.instFintype profile.input

/-- LDP artifact; derived from an assumed `LDPWitness`. -/
structure LDPArtifact where
  profile : LDPProfile
  proof : Classical.Transport.LDPConclusion profile.input

/-- Mean-field artifact; elementary reindexing identity only. -/
structure MeanFieldArtifact where
  profile : MeanFieldProfile
  proof : Classical.Transport.MeanFieldConclusion profile.input

end
end Adapters
end Proofs
end Runtime
