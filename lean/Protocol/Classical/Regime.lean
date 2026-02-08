import Mathlib
import Protocol.Coherence.ConfigEquiv

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

namespace ProtocolClassical

/-- Coherence-only state used for erasure/harmony analysis. -/
abbrev CoherenceState := CoherenceConfig

/-- Totality of a step relation on coherence states. -/
def Total (step : CoherenceState → CoherenceState → Prop) : Prop :=
  ∀ C, ∃ C', step C C'

/-- Determinism of a step relation on coherence states. -/
def Deterministic (step : CoherenceState → CoherenceState → Prop) : Prop :=
  ∀ C C₁ C₂, step C C₁ → step C C₂ → C₁ = C₂

/-- Characterization of the classical regime used for theorem transport. -/
structure ClassicalRegime (step : CoherenceState → CoherenceState → Prop) : Prop where
  /-- Session renaming (ConfigEquiv) commutes with one-step evolution. -/
  exchangeability :
    ∀ {C₁ C₂ C₁'}, ConfigEquiv C₁ C₂ → step C₁ C₁' →
      ∃ C₂', step C₂ C₂' ∧ ConfigEquiv C₁' C₂'
  /-- Steps only affect active edges; inactive traces are unchanged. -/
  localInteraction :
    ∀ {C C'}, step C C' →
      ∀ e, ¬ ActiveEdge C.G e → lookupD C'.D e = lookupD C.D e
  /-- Dynamics are total and deterministic. -/
  wellPosedDynamics : Total step ∧ Deterministic step
  /-- Coherence is invariant under ConfigEquiv (classical correlations). -/
  classicalCorrelations :
    ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ →
      (Coherent C₁.G C₁.D ↔ Coherent C₂.G C₂.D)
  /-- Coherent states form a finite state space. -/
  classicalStateSpace :
    Set.Finite { C : CoherenceState | Coherent C.G C.D }

/-- Default correlation law from the established Coherence/ConfigEquiv theorem. -/
theorem classicalCorrelations_default {C₁ C₂ : CoherenceState}
    (hEq : ConfigEquiv C₁ C₂) :
    (Coherent C₁.G C₁.D ↔ Coherent C₂.G C₂.D) :=
  Coherent_respects_equiv hEq

/-- Unfolded characterization form for `ClassicalRegime`. -/
theorem classicalRegime_iff (step : CoherenceState → CoherenceState → Prop) :
    ClassicalRegime step ↔
      (∀ {C₁ C₂ C₁'}, ConfigEquiv C₁ C₂ → step C₁ C₁' →
        ∃ C₂', step C₂ C₂' ∧ ConfigEquiv C₁' C₂') ∧
      (∀ {C C'}, step C C' → ∀ e, ¬ ActiveEdge C.G e → lookupD C'.D e = lookupD C.D e) ∧
      (Total step ∧ Deterministic step) ∧
      (∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → (Coherent C₁.G C₁.D ↔ Coherent C₂.G C₂.D)) ∧
      Set.Finite { C : CoherenceState | Coherent C.G C.D } := by
  constructor
  · intro h
    exact ⟨h.exchangeability, h.localInteraction, h.wellPosedDynamics,
      h.classicalCorrelations, h.classicalStateSpace⟩
  · intro h
    rcases h with ⟨hEx, hLocal, hWP, hCorr, hFinite⟩
    exact
      { exchangeability := hEx
        localInteraction := hLocal
        wellPosedDynamics := hWP
        classicalCorrelations := hCorr
        classicalStateSpace := hFinite }

end ProtocolClassical
