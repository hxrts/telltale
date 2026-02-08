import Classical
import Protocol.Classical.Regime

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

namespace ProtocolClassical

/-- Function-style protocol evolution packaged with transport prerequisites. -/
structure TransportFramework where
  step : CoherenceState → CoherenceState
  coherenceClosed :
    ∀ C, Coherent C.G C.D → Coherent (step C).G (step C).D
  harmony :
    ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → ConfigEquiv (step C₁) (step C₂)
  finiteCoherentStateSpace :
    Set.Finite { C : CoherenceState | Coherent C.G C.D }

/-- Relational view of a function-style step. -/
def stepRel (fw : TransportFramework) : CoherenceState → CoherenceState → Prop :=
  fun C C' => C' = fw.step C

theorem stepRel_total (fw : TransportFramework) : Total (stepRel fw) := by
  intro C
  exact ⟨fw.step C, rfl⟩

theorem stepRel_deterministic (fw : TransportFramework) : Deterministic (stepRel fw) := by
  intro C C₁ C₂ h₁ h₂
  rw [h₁, h₂]

/-- Function-style framework induces the Phase 6 classical-regime relation. -/
theorem inducedClassicalRegime (fw : TransportFramework)
    (hLocalInteraction :
      ∀ {C C'}, stepRel fw C C' →
        ∀ e, ¬ ActiveEdge C.G e → lookupD C'.D e = lookupD C.D e) :
    ClassicalRegime (stepRel fw) := by
  refine
    { exchangeability := ?_
      localInteraction := hLocalInteraction
      wellPosedDynamics := ⟨stepRel_total fw, stepRel_deterministic fw⟩
      classicalCorrelations := ?_
      classicalStateSpace := fw.finiteCoherentStateSpace }
  · intro C₁ C₂ C₁' hEq hStep
    refine ⟨fw.step C₂, rfl, ?_⟩
    cases hStep
    simpa using fw.harmony hEq
  · intro C₁ C₂ hEq
    exact classicalCorrelations_default hEq

/-- Build the generic classical transport context from protocol data. -/
def toTransportCtx (fw : TransportFramework) :
    Classical.Transport.TransportCtx CoherenceState :=
  { step := fw.step
    coherent := fun C => Coherent C.G C.D
    harmony := ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → ConfigEquiv (fw.step C₁) (fw.step C₂)
    finiteState := Set.Finite { C : CoherenceState | Coherent C.G C.D } }

/-- Package protocol data for the transported Foster-Lyapunov theorem. -/
def mkFosterInput (fw : TransportFramework)
    (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
    (hStep : system.step = fw.step) :
    Classical.Transport.FosterInput CoherenceState (toTransportCtx fw) :=
  { system := system
    step_agrees := hStep }

theorem transport_fosterLyapunov (fw : TransportFramework)
    (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
    (hStep : system.step = fw.step) :
    Classical.Transport.FosterConclusion (mkFosterInput fw system hStep) := by
  exact Classical.Transport.transported_fosterLyapunov
    (input := mkFosterInput fw system hStep)

abbrev MaxWeightInput := Classical.Transport.MaxWeightInput
abbrev LDPInput := Classical.Transport.LDPInput
abbrev MeanFieldInput := Classical.Transport.MeanFieldInput
abbrev HeavyTrafficInput := Classical.Transport.HeavyTrafficInput
abbrev MixingInput := Classical.Transport.MixingInput
abbrev FluidInput := Classical.Transport.FluidInput
abbrev ConcentrationInput := Classical.Transport.ConcentrationInput
abbrev LittlesLawInput := Classical.Transport.LittlesLawInput
abbrev FunctionalCLTInput := Classical.Transport.FunctionalCLTInput

/-- Transport API wrappers re-exported from the protocol-facing framework. -/
theorem transport_maxWeight {ι : Type} [Fintype ι] (input : MaxWeightInput ι) :
    Classical.Transport.MaxWeightConclusion input :=
  Classical.Transport.transported_maxWeight input

theorem transport_ldp (input : LDPInput) :
    Classical.Transport.LDPConclusion input :=
  Classical.Transport.transported_ldp input

theorem transport_meanField {n : Nat} (input : MeanFieldInput n) :
    Classical.Transport.MeanFieldConclusion input :=
  Classical.Transport.transported_meanField input

theorem transport_heavyTraffic (input : HeavyTrafficInput) :
    Classical.Transport.HeavyTrafficConclusion input :=
  Classical.Transport.transported_heavyTraffic input

theorem transport_mixing (input : MixingInput) :
    Classical.Transport.MixingConclusion input :=
  Classical.Transport.transported_mixing input

theorem transport_fluidLimit (input : FluidInput) :
    Classical.Transport.FluidConclusion input :=
  Classical.Transport.transported_fluidLimit input

theorem transport_concentration (input : ConcentrationInput) :
    Classical.Transport.ConcentrationConclusion input :=
  Classical.Transport.transported_concentration input

theorem transport_littlesLaw (input : LittlesLawInput) :
    Classical.Transport.LittlesLawConclusion input :=
  Classical.Transport.transported_littlesLaw input

theorem transport_functionalCLT (input : FunctionalCLTInput) :
    Classical.Transport.FunctionalCLTConclusion input :=
  Classical.Transport.transported_functionalCLT input

end ProtocolClassical
