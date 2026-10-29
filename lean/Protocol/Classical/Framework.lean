import Classical
import Protocol.Classical.Regime

/- 
The Problem. The protocol layer needs a reusable bridge from coherence-step
evolution to the generic classical transport theorems.

Solution Structure. Package protocol evolution as a transport framework and
prove adapters that instantiate the shared classical-regime interfaces.
-/

/-! # Protocol.Classical.Framework

Protocol-facing transport framework wrappers for classical-regime results.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Core Development -/

namespace ProtocolClassical

variable [EntropyAPI.AnalysisLaws]

/-- Function-style protocol evolution packaged with transport prerequisites. -/
structure TransportFramework where
  step : CoherenceState → CoherenceState
  coherenceClosed :
    ∀ C, Coherent C.G C.D → Coherent (step C).G (step C).D
  harmony :
    ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → ConfigEquiv (step C₁) (step C₂)
  finiteCoherentStateSpace :
    Set.Finite { C : CoherenceState | Coherent C.G C.D }

/-! ## Step Relation and Basic Properties -/

/-- Relational view of a function-style step. -/
def stepRel (fw : TransportFramework) : CoherenceState → CoherenceState → Prop :=
  fun C C' => C' = fw.step C

theorem step_rel_total (fw : TransportFramework) : Total (stepRel fw) := by
  intro C
  exact ⟨fw.step C, rfl⟩

theorem step_rel_deterministic (fw : TransportFramework) : Deterministic (stepRel fw) := by
  intro C C₁ C₂ h₁ h₂
  rw [h₁, h₂]

/-! ## Classical-Regime Induction -/

/-- Function-style framework induces the Phase 6 classical-regime relation. -/
theorem induced_classical_regime (fw : TransportFramework)
    (hLocalInteraction :
      ∀ {C C'}, stepRel fw C C' →
        ∀ e, ¬ ActiveEdge C.G e → lookupD C'.D e = lookupD C.D e) :
    ClassicalRegime (stepRel fw) := by
  refine
    { exchangeability := ?_
      localInteraction := hLocalInteraction
      wellPosedDynamics := ⟨step_rel_total fw, step_rel_deterministic fw⟩
      classicalCorrelations := ?_
      classicalStateSpace := fw.finiteCoherentStateSpace }
  · intro C₁ C₂ C₁' hEq hStep
    refine ⟨fw.step C₂, rfl, ?_⟩
    cases hStep
    simpa using fw.harmony hEq
  · intro C₁ C₂ hEq
    exact classical_correlations_default hEq

/-! ## Transport Context Construction -/

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

/-! ## Foster-Lyapunov Transport -/

/-- Conditional on the drift-system input, the potential is non-increasing along
iterates of the framework step (deterministic; not stochastic Foster-Lyapunov). -/
theorem foster_conclusion_of_framework (fw : TransportFramework)
    (system : Classical.FosterLyapunovHarris.DriftSystem CoherenceState)
    (hStep : system.step = fw.step) :
    Classical.Transport.FosterConclusion (mkFosterInput fw system hStep) :=
  Classical.Transport.foster_conclusion_of_input (input := mkFosterInput fw system hStep)

/-! ## Transport Input Aliases -/

abbrev MaxWeightInput := Classical.Transport.MaxWeightInput
abbrev LDPInput := Classical.Transport.LDPInput
abbrev MeanFieldInput := Classical.Transport.MeanFieldInput
abbrev HeavyTrafficInput := Classical.Transport.HeavyTrafficInput
abbrev MixingInput := Classical.Transport.MixingInput
abbrev FluidInput := Classical.Transport.FluidInput
abbrev LittlesLawInput := Classical.Transport.LittlesLawInput
abbrev FunctionalCLTInput := Classical.Transport.FunctionalCLTInput

/-
The former `transport_*` re-exports were pure aliases (several of them merely
returned an assumed premise field). They are removed; use the conditional
lemmas in `Classical.Transport.Theorems` or the witness fields directly.
-/

end ProtocolClassical
