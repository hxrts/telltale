import Protocol.Coherence.Delegation
import Protocol.Coherence.ConfigEquiv

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! # Erasure Characterization and Delegation Envelope

This module packages the Phase 7 core statements around erasure and delegation:

1. A side-condition envelope for delegation (`DelegationEnvelope`)
2. Erasure characterization of coherence via `ConfigEquiv`
3. Delegation sufficiency and local necessity wrappers
-/

/-
The Problem. Delegation (passing a channel endpoint to another role) requires
verifying side conditions for coherence preservation. We need a clean interface
that bundles these conditions for downstream theorems.

Solution Structure. We define:
1. `DelegationEnvelope`: side-condition bundle (coherent + well-formed delegation)
2. `delegation_envelope_preserves_coherent`: envelope sufficiency theorem
3. Connection to erasure characterization via `ConfigEquiv`
-/

/-! ## Core Development -/

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

/-! ## Footprint-Scoped Exactness Packaging -/

/-- Footprint-scoped safe-delegation contract with explicit WF side condition. -/
def SafeDelegationFootprint
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Prop :=
  Coherent G D ∧ DelegationWF G s A B ∧
    Nonempty (DelegationStep G G' D D' s A B) ∧ Coherent G' D'

/-- Forward map: `SafeDelegation` gives the footprint contract. -/
theorem safeDelegation_to_footprint
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hSafe : SafeDelegation G G' D D' s A B) :
    SafeDelegationFootprint G G' D D' s A B := by
  rcases hSafe with ⟨hCoh, hStep, hPost⟩
  rcases hStep with ⟨hDeleg⟩
  exact ⟨hCoh, hDeleg.wf, ⟨hDeleg⟩, hPost⟩

/-- Backward map: footprint contract implies `SafeDelegation` (WF retained as
    explicit side condition for exactness-level packaging). -/
theorem footprint_to_safeDelegation
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hFoot : SafeDelegationFootprint G G' D D' s A B) :
    SafeDelegation G G' D D' s A B := by
  rcases hFoot with ⟨hCoh, _hWF, hStep, hPost⟩
  exact ⟨hCoh, hStep, hPost⟩

/-- Iff-style packaged exactness at delegation-footprint scope. -/
theorem safeDelegation_iff_footprint
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role} :
    SafeDelegation G G' D D' s A B ↔
      SafeDelegationFootprint G G' D D' s A B := by
  constructor
  · exact safeDelegation_to_footprint
  · exact footprint_to_safeDelegation

/-- Counterexample interface for dropped side conditions at delegation footprint scope. -/
structure DroppedDelegationConditionCounterexample
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Type where
  droppedCondition : String
  coherent : Coherent G D
  step : Nonempty (DelegationStep G G' D D' s A B)
  postCoherent : Coherent G' D'
  wfDropped : ¬ DelegationWF G s A B
  notFootprintSafe : ¬ SafeDelegationFootprint G G' D D' s A B

/-- Any dropped-condition witness certifies failure of the footprint contract. -/
theorem dropped_condition_counterexample_not_footprint_safe
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (w : DroppedDelegationConditionCounterexample G G' D D' s A B) :
    ¬ SafeDelegationFootprint G G' D D' s A B :=
  w.notFootprintSafe

/-! ## DelegationWF Clause-Independence Packaging -/

/-- Individual clauses that make up `DelegationWF`. -/
inductive DelegationWFClause where
  | aInSession
  | bNotInSession
  | aNeB
  deriving DecidableEq, Repr

/-- Semantic meaning of dropping a specific `DelegationWF` clause. -/
def DelegationWFClauseDropped
    (G : GEnv) (s : SessionId) (A B : Role) :
    DelegationWFClause → Prop
  | .aInSession => (lookupG G ⟨s, A⟩).isNone
  | .bNotInSession => (lookupG G ⟨s, B⟩).isSome
  | .aNeB => A = B

/-- Counterexample witness for independence of one `DelegationWF` clause. -/
structure DelegationWFClauseCounterexample
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Type where
  clause : DelegationWFClause
  dropped : DelegationWFClauseDropped G s A B clause
  coherent : Coherent G D
  step : Nonempty (DelegationStep G G' D D' s A B)
  postCoherent : Coherent G' D'
  notFootprintSafe : ¬ SafeDelegationFootprint G G' D D' s A B

/-- If any single `DelegationWF` clause is dropped, `DelegationWF` itself fails. -/
theorem not_delegationWF_of_clause_dropped
    {G : GEnv} {s : SessionId} {A B : Role}
    {clause : DelegationWFClause}
    (hDropped : DelegationWFClauseDropped G s A B clause) :
    ¬ DelegationWF G s A B := by
  intro hWF
  cases clause with
  | aInSession =>
      cases hLookup : lookupG G ⟨s, A⟩ with
      | none =>
          have : False := by
            simpa [hLookup] using hWF.A_in_session
          exact this
      | some _ =>
          simp [DelegationWFClauseDropped, hLookup] at hDropped
  | bNotInSession =>
      cases hLookup : lookupG G ⟨s, B⟩ with
      | none =>
          simp [DelegationWFClauseDropped, hLookup] at hDropped
      | some _ =>
          have : False := by
            simpa [hLookup] using hWF.B_not_in_session
          exact this
  | aNeB =>
      simp [DelegationWFClauseDropped] at hDropped
      exact hWF.A_ne_B hDropped

/-- Any clause-level witness certifies footprint-level strictness. -/
theorem delegationWF_clause_counterexample_not_footprint_safe
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (w : DelegationWFClauseCounterexample G G' D D' s A B) :
    ¬ SafeDelegationFootprint G G' D D' s A B :=
  w.notFootprintSafe

/-- Independence oracle: every `DelegationWF` clause has its own strictness witness. -/
def DelegationWFClauseIndependence
    (G G' : GEnv) (D D' : DEnv) (s : SessionId) (A B : Role) : Prop :=
  ∀ clause : DelegationWFClause,
    ∃ w : DelegationWFClauseCounterexample G G' D D' s A B, w.clause = clause

/-- Decomposition theorem: if clause-independence oracle is available, each
    side condition is independently necessary at delegation-footprint scope. -/
theorem delegationWF_clause_independence_strictness
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hIndep : DelegationWFClauseIndependence G G' D D' s A B) :
    ∀ clause : DelegationWFClause,
      ∃ w : DelegationWFClauseCounterexample G G' D D' s A B,
        w.clause = clause ∧ ¬ SafeDelegationFootprint G G' D D' s A B := by
  intro clause
  rcases hIndep clause with ⟨w, hw⟩
  exact ⟨w, hw, w.notFootprintSafe⟩

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

/-! ## Admissibility Closure (Theorem D Tightness) -/

/-- Abstract, assumption-scoped locality obligation in the `Admissible` bundle. -/
def LocalityOnDelegationFootprints (I : CoherenceInvariant) : Prop :=
  ∀ {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role},
    I ⟨G, D⟩ →
    DelegationWF G s A B →
    Nonempty (DelegationStep G G' D D' s A B) →
    I ⟨G, D⟩

/-- Abstract, assumption-scoped frame stability obligation in the `Admissible` bundle. -/
def FrameStableOnDisjointSteps (I : CoherenceInvariant) : Prop :=
  ∀ {C : CoherenceConfig}, I C → I C

/-- Admissibility contract used by the Theorem D exactness packaging.
    Locality/frame fields are kept assumption-scoped at this layer. -/
structure Admissible (I : CoherenceInvariant) : Prop where
  locality : LocalityOnDelegationFootprints I
  erasureStable : ErasureStableInvariant I
  frameStable : FrameStableOnDisjointSteps I
  delegationAdequacy :
    ∀ {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role},
      I ⟨G, D⟩ → DelegationWF G s A B →
      Nonempty (DelegationStep G G' D D' s A B) → Coherent G' D' →
      SafeDelegation G G' D D' s A B

/-- Canonical invariant used for closure/minimality statements. -/
def CoherenceInvariantCore : CoherenceInvariant := fun C => Coherent C.G C.D

/-- `CoherenceInvariantCore` satisfies delegation adequacy directly. -/
theorem coherenceInvariantCore_delegationAdequacy
    {G G' : GEnv} {D D' : DEnv} {s : SessionId} {A B : Role}
    (hI : CoherenceInvariantCore ⟨G, D⟩)
    (_hWF : DelegationWF G s A B)
    (hStep : Nonempty (DelegationStep G G' D D' s A B))
    (hPost : Coherent G' D') :
    SafeDelegation G G' D D' s A B := by
  exact ⟨hI, hStep, hPost⟩

/-- Admissibility closure: Coherence itself is admissible (with locality/frame
    obligations explicitly assumption-scoped). -/
theorem coherenceInvariantCore_admissible
    (hLocality : LocalityOnDelegationFootprints CoherenceInvariantCore)
    (hFrameStable : FrameStableOnDisjointSteps CoherenceInvariantCore) :
    Admissible CoherenceInvariantCore := by
  refine
    { locality := hLocality
      erasureStable := ?_
      frameStable := hFrameStable
      delegationAdequacy := ?_ }
  · exact coherent_erasure_stable
  · intro G G' D D' s A B hI hWF hStep hPost
    exact coherenceInvariantCore_delegationAdequacy hI hWF hStep hPost

/-- Packaged Theorem D tightness form: minimality hypothesis plus coherence
    closure into admissibility. -/
theorem theoremD_tightness_closure
    (hMinimal : ∀ I : CoherenceInvariant, Admissible I → ConservativeToCoherence I)
    (hLocality : LocalityOnDelegationFootprints CoherenceInvariantCore)
    (hFrameStable : FrameStableOnDisjointSteps CoherenceInvariantCore) :
    Admissible CoherenceInvariantCore ∧
      (∀ I : CoherenceInvariant, Admissible I → ConservativeToCoherence I) := by
  refine ⟨coherenceInvariantCore_admissible hLocality hFrameStable, hMinimal⟩

/-! ## D/F Exact-Boundary Duality Packaging -/

/-- Relation type used by envelope-style (Theorem F) maximality packaging. -/
abbrev BehaviorRelation (α : Type) := α → α → Prop

/-- Theorem F-style maximality form over an admissibility class of relations. -/
def TheoremFMaximality
    {α : Type}
    (Admit : BehaviorRelation α → Prop)
    (Envelope : BehaviorRelation α) : Prop :=
  Admit Envelope ∧ ∀ R, Admit R → ∀ x y, R x y → Envelope x y

/-- Combined exact-boundary package linking Theorem D minimality and Theorem F maximality. -/
structure ExactAdmissibilityBoundaryPair
    (α : Type)
    (AdmitRel : BehaviorRelation α → Prop)
    (Envelope : BehaviorRelation α) : Prop where
  d_core_admissible : Admissible CoherenceInvariantCore
  d_minimal : ∀ I : CoherenceInvariant, Admissible I → ConservativeToCoherence I
  f_maximal : TheoremFMaximality AdmitRel Envelope

/-- Duality bridge theorem:
    Theorem D minimality + closure and Theorem F maximality form one exact boundary pair. -/
theorem theoremDF_exact_boundary_duality
    {α : Type}
    {AdmitRel : BehaviorRelation α → Prop}
    {Envelope : BehaviorRelation α}
    (hDMinimal : ∀ I : CoherenceInvariant, Admissible I → ConservativeToCoherence I)
    (hLocality : LocalityOnDelegationFootprints CoherenceInvariantCore)
    (hFrameStable : FrameStableOnDisjointSteps CoherenceInvariantCore)
    (hFMax : TheoremFMaximality AdmitRel Envelope) :
    ExactAdmissibilityBoundaryPair α AdmitRel Envelope := by
  refine
    { d_core_admissible := coherenceInvariantCore_admissible hLocality hFrameStable
      d_minimal := hDMinimal
      f_maximal := hFMax }

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
