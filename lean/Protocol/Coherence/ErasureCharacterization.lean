import Protocol.Coherence.Delegation
import Protocol.Coherence.ConfigEquiv

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! # Erasure Characterization and Delegation Envelope

This module packages the Phase 7 core statements around erasure and delegation:

1. A side-condition envelope for delegation (`DelegationEnvelope`)
2. Erasure characterization of coherence via `ConfigEquiv`
3. Delegation sufficiency and local necessity wrappers
-/

/-- Side-condition envelope used by delegation/harmony theorems. -/
structure DelegationEnvelope
    (G : GEnv) (D : DEnv) (s : SessionId) (A B : Role) : Prop where
  coherent : Coherent G D
  wf : DelegationWF G s A B

/-- Any concrete delegation step provides the well-formed delegation side conditions. -/
theorem DelegationStep.wf_envelope
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    DelegationEnvelope G D s A B :=
  { coherent := hCoh
    wf := hDeleg.wf }

/-- The delegation envelope is sufficient to preserve coherence across a delegation step. -/
theorem delegation_envelope_preserves_coherent
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hEnv : DelegationEnvelope G D s A B)
    (hDeleg : DelegationStep G G' D D' s A B) :
    Coherent G' D' :=
  delegation_preserves_coherent G G' D D' s A B hEnv.coherent hDeleg

/-- Erasure-stability predicate for invariants over coherence configurations. -/
def ErasureStableInvariant (I : CoherenceConfig → Prop) : Prop :=
  ∀ {C₁ C₂}, ConfigEquiv C₁ C₂ → (I C₁ ↔ I C₂)

/-- Coherence is erasure-stable under the `ConfigEquiv` relation. -/
theorem coherent_erasure_stable :
    ErasureStableInvariant (fun C => Coherent C.G C.D) := by
  intro C₁ C₂ hEq
  exact Coherent_respects_equiv hEq

/-- Erasure characterization: coherence at `C` iff all erasure-equivalent views are coherent. -/
theorem coherence_erasure_characterization (C : CoherenceConfig) :
    Coherent C.G C.D ↔
      ∀ C', ConfigEquiv C C' → Coherent C'.G C'.D := by
  constructor
  · intro hCoh C' hEq
    exact (Coherent_respects_equiv hEq).1 hCoh
  · intro hAll
    exact hAll C (ConfigEquiv_refl C)

/-- Safety contract for delegation from `G,D` to `G',D'`. -/
def SafeDelegation
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Prop :=
  Coherent G D ∧ Nonempty (DelegationStep G G' D D' s A B) ∧ Coherent G' D'

/-- Delegation sufficiency: coherence + delegation step imply safe delegation. -/
theorem delegation_sufficiency
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hCoh : Coherent G D)
    (hDeleg : DelegationStep G G' D D' s A B) :
    SafeDelegation G G' D D' s A B := by
  refine ⟨hCoh, ⟨hDeleg⟩, ?_⟩
  exact delegation_preserves_coherent G G' D D' s A B hCoh hDeleg

/-- Local necessity: any safe delegation carries the original coherence and WF side conditions. -/
theorem safeDelegation_local_necessity
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hSafe : SafeDelegation G G' D D' s A B) :
    Coherent G D ∧ DelegationWF G s A B := by
  rcases hSafe with ⟨hCoh, hStep, _⟩
  rcases hStep with ⟨hDeleg⟩
  exact ⟨hCoh, hDeleg.wf⟩

/-- Invariant families over coherence configurations. -/
abbrev CoherenceInvariant := CoherenceConfig → Prop

/-- `I` is conservative if it never admits a state outside coherence. -/
def ConservativeToCoherence (I : CoherenceInvariant) : Prop :=
  ∀ C, I C → Coherent C.G C.D

/-- `I` is complete for coherence if it contains all coherent states. -/
def CompleteForCoherence (I : CoherenceInvariant) : Prop :=
  ∀ C, Coherent C.G C.D → I C

/-- Safety contract induced by a custom pre-invariant `I`. -/
def SafeDelegationFrom
    (I : CoherenceInvariant)
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Prop :=
  I ⟨G, D⟩ ∧ Nonempty (DelegationStep G G' D D' s A B) ∧ Coherent G' D'

/-- Relative minimality: any invariant both conservative and complete is equivalent to coherence. -/
theorem relative_minimality
    (I : CoherenceInvariant)
    (hConservative : ConservativeToCoherence I)
    (hComplete : CompleteForCoherence I) :
    ∀ C, I C ↔ Coherent C.G C.D := by
  intro C
  constructor
  · exact hConservative C
  · exact hComplete C

/-- Conservativity: a conservative invariant cannot justify extra safe delegations. -/
theorem conservative_no_extra_safe_delegations
    (I : CoherenceInvariant)
    (hConservative : ConservativeToCoherence I)
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hSafeI : SafeDelegationFrom I G G' D D' s A B) :
    SafeDelegation G G' D D' s A B := by
  rcases hSafeI with ⟨hI, hStep, hPost⟩
  exact ⟨hConservative ⟨G, D⟩ hI, hStep, hPost⟩

/-- Packaged theorem statements for downstream papers/modules. -/
structure Phase7TheoremPackage : Prop where
  erasure_characterization :
    ∀ C, Coherent C.G C.D ↔
      ∀ C', ConfigEquiv C C' → Coherent C'.G C'.D
  delegation_sufficiency :
    ∀ {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role},
      Coherent G D → DelegationStep G G' D D' s A B →
      SafeDelegation G G' D D' s A B
  local_necessity :
    ∀ {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role},
      SafeDelegation G G' D D' s A B →
      Coherent G D ∧ DelegationWF G s A B
  relative_minimality :
    ∀ (I : CoherenceInvariant),
      ConservativeToCoherence I →
      CompleteForCoherence I →
      ∀ C, I C ↔ Coherent C.G C.D
  conservativity :
    ∀ (I : CoherenceInvariant)
      {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role},
      ConservativeToCoherence I →
      SafeDelegationFrom I G G' D D' s A B →
      SafeDelegation G G' D D' s A B

/-- Canonical packaged theorem bundle. -/
def phase7_theorem_package : Phase7TheoremPackage :=
  { erasure_characterization := coherence_erasure_characterization
    delegation_sufficiency := by
      intro G G' D D' s A B hCoh hDeleg
      exact delegation_sufficiency hCoh hDeleg
    local_necessity := by
      intro G G' D D' s A B hSafe
      exact safeDelegation_local_necessity hSafe
    relative_minimality := by
      intro I hCons hComp C
      exact relative_minimality I hCons hComp C
    conservativity := by
      intro I G G' D D' s A B hCons hSafeI
      exact conservative_no_extra_safe_delegations I hCons hSafeI }
