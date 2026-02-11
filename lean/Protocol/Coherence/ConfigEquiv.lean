import Protocol.Coherence.ConfigEquivRenaming

/-! # Protocol.Coherence.ConfigEquiv

Lookup-based equivalence on coherence configurations and invariance of coherence.
-/

/-
The Problem. We need a quotient-style equivalence on coherence configurations
that identifies states differing only by session-id renaming, and we must show
coherence is invariant under this quotient.

Solution Structure.
1. Define `CoherenceConfig` and lookup-based renaming equivalence `ConfigEquiv`.
2. Prove equivalence laws (reflexive/symmetric/transitive).
3. Show coherence is preserved under equivalent configurations.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section
/-! ## Coherence Configurations and Equivalence -/

/-- A coherence configuration consists of environments (G, D). -/
structure CoherenceConfig where
  -- Session environment.
  G : GEnv
  -- Trace environment.
  D : DEnv

/-- Lookup-based renaming equivalence of coherence configurations. -/
def ConfigEquiv (C₁ C₂ : CoherenceConfig) : Prop :=
  -- Witnessed by a session-ID isomorphism and lookup preservation.
  ∃ σ : SessionIso,
    (∀ e,
      lookupG C₂.G (renameEndpoint (SessionIso.toRenaming σ) e) =
        (lookupG C₁.G e).map (renameLocalType (SessionIso.toRenaming σ))) ∧
    (∀ e,
      lookupD C₂.D (renameEdge (SessionIso.toRenaming σ) e) =
        (lookupD C₁.D e).map (renameValType (SessionIso.toRenaming σ)))

/-- ConfigEquiv is reflexive. -/
theorem ConfigEquiv_refl (C : CoherenceConfig) : ConfigEquiv C C := by
  -- Identity renaming witnesses reflexivity.
  refine ⟨SessionIso.id, ?_, ?_⟩
  · intro e
    -- Case split on the lookup to avoid rewriting mismatches.
    cases h : lookupG C.G e <;>
      simp [SessionIso.toRenaming_id, renameEndpoint_id, renameLocalType_id, h]
  · intro e
    -- Case split on the lookup to avoid rewriting mismatches.
    cases h : lookupD C.D e <;>
      simp [SessionIso.toRenaming_id, renameEdge_id, renameValType_id_fun, h]

private theorem ConfigEquiv_symm_G (σ : SessionIso) (C₁ C₂ : CoherenceConfig)
    (hG : ∀ e,
      lookupG C₂.G (renameEndpoint (SessionIso.toRenaming σ) e) =
        (lookupG C₁.G e).map (renameLocalType (SessionIso.toRenaming σ))) :
    ∀ e,
      lookupG C₁.G (renameEndpoint (SessionIso.invRenaming σ) e) =
        (lookupG C₂.G e).map (renameLocalType (SessionIso.invRenaming σ)) := by
  -- Use a preimage endpoint and cancel the renaming.
  intro e
  let e' : Endpoint := { sid := σ.bwd e.sid, role := e.role }
  have hEq : renameEndpoint (SessionIso.toRenaming σ) e' = e := by
    simp [renameEndpoint, SessionIso.toRenaming, e', σ.right_inv]
  have hFwd : lookupG C₂.G e =
      (lookupG C₁.G e').map (renameLocalType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using hG e'
  have hMap : (lookupG C₂.G e).map (renameLocalType (SessionIso.invRenaming σ)) =
      lookupG C₁.G e' := by
    -- Case split on the preimage lookup.
    cases h : lookupG C₁.G e' <;>
      simp [hFwd, h, renameLocalType_left_inv]
  have hLhs : lookupG C₁.G (renameEndpoint (SessionIso.invRenaming σ) e) =
      lookupG C₁.G e' := by
    simp [renameEndpoint, SessionIso.invRenaming, e']
  simpa [hLhs] using hMap.symm

private theorem ConfigEquiv_symm_D (σ : SessionIso) (C₁ C₂ : CoherenceConfig)
    (hD : ∀ e,
      lookupD C₂.D (renameEdge (SessionIso.toRenaming σ) e) =
        (lookupD C₁.D e).map (renameValType (SessionIso.toRenaming σ))) :
    ∀ e,
      lookupD C₁.D (renameEdge (SessionIso.invRenaming σ) e) =
        (lookupD C₂.D e).map (renameValType (SessionIso.invRenaming σ)) := by
  -- Use a preimage edge and cancel the renaming.
  intro e
  let e' : Edge := { sid := σ.bwd e.sid, sender := e.sender, receiver := e.receiver }
  have hEq : renameEdge (SessionIso.toRenaming σ) e' = e := by
    simp [renameEdge, SessionIso.toRenaming, e', σ.right_inv]
  have hFwd : lookupD C₂.D e =
      (lookupD C₁.D e').map (renameValType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using hD e'
  have hMap : (lookupD C₂.D e).map (renameValType (SessionIso.invRenaming σ)) =
      lookupD C₁.D e' := by
    -- Case split on the preimage lookup.
    cases h : lookupD C₁.D e' <;>
      simp [hFwd, h, List.map_map, map_renameValType_left_inv, renameValType_left_inv]
  have hLhs : lookupD C₁.D (renameEdge (SessionIso.invRenaming σ) e) =
      lookupD C₁.D e' := by
    simp [renameEdge, SessionIso.invRenaming, e']
  simpa [hLhs] using hMap.symm

/-- ConfigEquiv is symmetric. -/
theorem ConfigEquiv_symm {C₁ C₂ : CoherenceConfig} :
    ConfigEquiv C₁ C₂ → ConfigEquiv C₂ C₁ := by
  -- Use the inverse isomorphism to flip the equivalence.
  intro h
  rcases h with ⟨σ, hG, hD⟩
  refine ⟨SessionIso.symm σ, ?_, ?_⟩
  · simpa [SessionIso.symm, SessionIso.toRenaming] using
      (ConfigEquiv_symm_G (σ:=σ) (C₁:=C₁) (C₂:=C₂) hG)
  · simpa [SessionIso.symm, SessionIso.toRenaming] using
      (ConfigEquiv_symm_D (σ:=σ) (C₁:=C₁) (C₂:=C₂) hD)

private theorem ConfigEquiv_trans_G
    (σ₂ σ₁ : SessionIso) (C₁ C₂ C₃ : CoherenceConfig)
    (hG₁ : ∀ e,
      lookupG C₂.G (renameEndpoint (SessionIso.toRenaming σ₁) e) =
        (lookupG C₁.G e).map (renameLocalType (SessionIso.toRenaming σ₁)))
    (hG₂ : ∀ e,
      lookupG C₃.G (renameEndpoint (SessionIso.toRenaming σ₂) e) =
        (lookupG C₂.G e).map (renameLocalType (SessionIso.toRenaming σ₂))) :
    ∀ e,
      lookupG C₃.G (renameEndpoint (SessionIso.toRenaming (SessionIso.comp σ₂ σ₁)) e) =
        (lookupG C₁.G e).map
          (renameLocalType (SessionIso.toRenaming (SessionIso.comp σ₂ σ₁))) := by
  -- Compose the two renaming equalities on lookups.
  intro e
  have hStep := hG₂ (renameEndpoint (SessionIso.toRenaming σ₁) e)
  have hBase := hG₁ e
  have hComp : lookupG C₃.G (renameEndpoint (SessionIso.toRenaming σ₂)
      (renameEndpoint (SessionIso.toRenaming σ₁) e)) =
      ((lookupG C₁.G e).map (renameLocalType (SessionIso.toRenaming σ₁))).map
        (renameLocalType (SessionIso.toRenaming σ₂)) := by
    simpa [hBase] using hStep
  have hMap : lookupG C₃.G (renameEndpoint (SessionIso.toRenaming σ₂)
      (renameEndpoint (SessionIso.toRenaming σ₁) e)) =
      (lookupG C₁.G e).map
        (renameLocalType (SessionRenaming.comp
          (SessionIso.toRenaming σ₂) (SessionIso.toRenaming σ₁))) := by
    -- Collapse the two-step map on options.
    simpa [map_renameLocalType_comp] using hComp
  simpa [renameEndpoint_comp, SessionIso.comp, SessionIso.toRenaming] using hMap

private theorem ConfigEquiv_trans_D
    (σ₂ σ₁ : SessionIso) (C₁ C₂ C₃ : CoherenceConfig)
    (hD₁ : ∀ e,
      lookupD C₂.D (renameEdge (SessionIso.toRenaming σ₁) e) =
        (lookupD C₁.D e).map (renameValType (SessionIso.toRenaming σ₁)))
    (hD₂ : ∀ e,
      lookupD C₃.D (renameEdge (SessionIso.toRenaming σ₂) e) =
        (lookupD C₂.D e).map (renameValType (SessionIso.toRenaming σ₂))) :
    ∀ e,
      lookupD C₃.D (renameEdge (SessionIso.toRenaming (SessionIso.comp σ₂ σ₁)) e) =
        (lookupD C₁.D e).map
          (renameValType (SessionIso.toRenaming (SessionIso.comp σ₂ σ₁))) := by
  -- Compose the two renaming equalities on traces.
  intro e
  have hStep := hD₂ (renameEdge (SessionIso.toRenaming σ₁) e)
  have hBase := hD₁ e
  have hComp : lookupD C₃.D (renameEdge (SessionIso.toRenaming σ₂)
      (renameEdge (SessionIso.toRenaming σ₁) e)) =
      ((lookupD C₁.D e).map (renameValType (SessionIso.toRenaming σ₁))).map
        (renameValType (SessionIso.toRenaming σ₂)) := by
    simpa [hBase] using hStep
  have hMap : lookupD C₃.D (renameEdge (SessionIso.toRenaming σ₂)
      (renameEdge (SessionIso.toRenaming σ₁) e)) =
      (lookupD C₁.D e).map
        (renameValType (SessionRenaming.comp
          (SessionIso.toRenaming σ₂) (SessionIso.toRenaming σ₁))) := by
    -- Collapse the two-step map on traces.
    simpa [map_renameValType_comp] using hComp
  simpa [renameEdge_comp, SessionIso.comp, SessionIso.toRenaming] using hMap

/-- ConfigEquiv is transitive. -/
theorem ConfigEquiv_trans {C₁ C₂ C₃ : CoherenceConfig} :
    ConfigEquiv C₁ C₂ → ConfigEquiv C₂ C₃ → ConfigEquiv C₁ C₃ := by
  -- Compose the witnessing isomorphisms.
  intro h12 h23
  rcases h12 with ⟨σ₁, hG₁, hD₁⟩
  rcases h23 with ⟨σ₂, hG₂, hD₂⟩
  refine ⟨SessionIso.comp σ₂ σ₁, ?_, ?_⟩
  · exact ConfigEquiv_trans_G (σ₂:=σ₂) (σ₁:=σ₁) (C₁:=C₁) (C₂:=C₂) (C₃:=C₃) hG₁ hG₂
  · exact ConfigEquiv_trans_D (σ₂:=σ₂) (σ₁:=σ₁) (C₁:=C₁) (C₂:=C₂) (C₃:=C₃) hD₁ hD₂

/-- ConfigEquiv is an equivalence relation. -/
theorem ConfigEquiv_equivalence : Equivalence ConfigEquiv := by
  -- Pack reflexivity, symmetry, and transitivity.
  refine ⟨ConfigEquiv_refl, ?_, ?_⟩
  · intro C₁ C₂ h; exact ConfigEquiv_symm h
  · intro C₁ C₂ C₃ h12 h23; exact ConfigEquiv_trans h12 h23

/-! ## Coherence Respects Equivalence -/

/-- EdgeCoherent depends only on lookups. -/
theorem EdgeCoherent_congr {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} (e : Edge)
    (hG : ∀ e, lookupG G₁ e = lookupG G₂ e)
    (hD : ∀ e, lookupD D₁ e = lookupD D₂ e) :
    EdgeCoherent G₁ D₁ e ↔ EdgeCoherent G₂ D₂ e := by
  -- Rewrite lookups in the definition of EdgeCoherent.
  simp [EdgeCoherent, hG, hD]

/-- Coherent depends only on lookups. -/
theorem Coherent_congr {G₁ G₂ : GEnv} {D₁ D₂ : DEnv}
    (hG : ∀ e, lookupG G₁ e = lookupG G₂ e)
    (hD : ∀ e, lookupD D₁ e = lookupD D₂ e) :
    Coherent G₁ D₁ ↔ Coherent G₂ D₂ := by
  -- Rewrite all lookups under Coherent.
  simp [Coherent, ActiveEdge, EdgeCoherent, hG, hD]

private theorem ConfigEquiv_lookupG_eq (σ : SessionIso) (C₁ C₂ : CoherenceConfig)
    (hG : ∀ e,
      lookupG C₂.G (renameEndpoint (SessionIso.toRenaming σ) e) =
        (lookupG C₁.G e).map (renameLocalType (SessionIso.toRenaming σ))) :
    ∀ e, lookupG (renameGEnv (SessionIso.toRenaming σ) C₁.G) e = lookupG C₂.G e := by
  -- Any endpoint has a preimage because σ is bijective.
  intro e
  let e' : Endpoint := { sid := σ.bwd e.sid, role := e.role }
  have hEq : renameEndpoint (SessionIso.toRenaming σ) e' = e := by
    simp [renameEndpoint, SessionIso.toRenaming, e', σ.right_inv]
  have hRen : lookupG (renameGEnv (SessionIso.toRenaming σ) C₁.G) e =
      (lookupG C₁.G e').map (renameLocalType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using (lookupG_rename (ρ:=SessionIso.toRenaming σ) (G:=C₁.G) (e:=e'))
  have hCfg : lookupG C₂.G e =
      (lookupG C₁.G e').map (renameLocalType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using hG e'
  exact hRen.trans hCfg.symm

private theorem ConfigEquiv_lookupD_eq (σ : SessionIso) (C₁ C₂ : CoherenceConfig)
    (hD : ∀ e,
      lookupD C₂.D (renameEdge (SessionIso.toRenaming σ) e) =
        (lookupD C₁.D e).map (renameValType (SessionIso.toRenaming σ))) :
    ∀ e, lookupD (renameDEnv (SessionIso.toRenaming σ) C₁.D) e = lookupD C₂.D e := by
  -- Any edge has a preimage because σ is bijective.
  intro e
  let e' : Edge := { sid := σ.bwd e.sid, sender := e.sender, receiver := e.receiver }
  have hEq : renameEdge (SessionIso.toRenaming σ) e' = e := by
    simp [renameEdge, SessionIso.toRenaming, e', σ.right_inv]
  have hRen : lookupD (renameDEnv (SessionIso.toRenaming σ) C₁.D) e =
      (lookupD C₁.D e').map (renameValType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using (lookupD_rename (ρ:=SessionIso.toRenaming σ) (D:=C₁.D) (e:=e'))
  have hCfg : lookupD C₂.D e =
      (lookupD C₁.D e').map (renameValType (SessionIso.toRenaming σ)) := by
    simpa [hEq] using hD e'
  exact hRen.trans hCfg.symm

/-- Coherence is preserved under ConfigEquiv. -/
private theorem Coherent_of_ConfigEquiv {C₁ C₂ : CoherenceConfig} :
    ConfigEquiv C₁ C₂ → Coherent C₁.G C₁.D → Coherent C₂.G C₂.D := by
  -- Reduce to renaming preservation plus lookup congruence.
  intro h hCoh
  rcases h with ⟨σ, hG, hD⟩
  have hG' := ConfigEquiv_lookupG_eq (σ:=σ) (C₁:=C₁) (C₂:=C₂) hG
  have hD' := ConfigEquiv_lookupD_eq (σ:=σ) (C₁:=C₁) (C₂:=C₂) hD
  have hRen := CoherentRenaming (ρ:=SessionIso.toRenaming σ) (G:=C₁.G) (D:=C₁.D) hCoh
  exact (Coherent_congr (G₁:=renameGEnv (SessionIso.toRenaming σ) C₁.G)
    (D₁:=renameDEnv (SessionIso.toRenaming σ) C₁.D) (G₂:=C₂.G) (D₂:=C₂.D) hG' hD').mp hRen

/-- Coherence is preserved under ConfigEquiv. -/
theorem Coherent_respects_equiv {C₁ C₂ : CoherenceConfig} :
    ConfigEquiv C₁ C₂ → (Coherent C₁.G C₁.D ↔ Coherent C₂.G C₂.D) := by
  -- Combine the forward direction with symmetry.
  intro h
  constructor
  · exact Coherent_of_ConfigEquiv h
  · intro hCoh
    have hSymm := ConfigEquiv_symm (C₁:=C₁) (C₂:=C₂) h
    exact Coherent_of_ConfigEquiv hSymm hCoh

end
