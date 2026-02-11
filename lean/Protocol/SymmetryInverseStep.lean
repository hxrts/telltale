import Protocol.SymmetryCore

/-! # Protocol.SymmetryInverseStep

Inverse-step reconstruction lemmas under protocol renaming.
-/

/-
The Problem. Recover preimage send/select/branch steps from renamed-step observations.

Solution Structure. Use renamed lookup inversion and branch-membership inversion lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
/-! ## Inverse Step Theorems -/

/-- Helper: branch membership under renaming.
    If (l', L') is in the renamed branches, there exists an original (l, L). -/
theorem mem_renameBranchesPR_inv (σ : ProtocolRenaming)
    (bs : List (Label × LocalType)) (l' : Label) (L' : LocalType) :
    (l', L') ∈ renameBranchesPR σ bs →
    ∃ l L, (l, L) ∈ bs ∧ l' = σ.labelMap l ∧ L' = renameLocalTypePR σ L := by
  induction bs with
  | nil =>
      intro h
      unfold renameBranchesPR at h
      simp at h
  | cons hd tl ih =>
      intro h
      unfold renameBranchesPR at h
      simp only [List.mem_cons] at h
      cases h with
      | inl heq =>
          obtain ⟨hl, hL⟩ := Prod.mk.inj heq
          refine ⟨hd.1, hd.2, ?_, hl, hL⟩
          exact List.mem_cons.mpr (Or.inl rfl)
      | inr hmem =>
          obtain ⟨l, L, hmem', hl, hL⟩ := ih hmem
          exact ⟨l, L, List.mem_cons.mpr (Or.inr hmem'), hl, hL⟩

/-- Inverse step for send: if σ(C) has a send type, C has a corresponding send type.
    The renamed sender/receiver are preimages under σ.roleMap.
    From Aristotle 06b. -/
theorem inverse_step_send_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (T' : ValType) (L' : LocalType) (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, s'⟩ = some (.send r' T' L')) :
    ∃ s r T L, σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      T' = renameValTypePR σ T ∧
      lookupG G ⟨sid, s⟩ = some (.send r T L) ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv to get preimage, then case split on local type
  obtain ⟨ep, L, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = s' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : L with
  | send r T Lcont =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.send.injEq] at hLfull
      obtain ⟨hr', hT', hLcont'⟩ := hLfull
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.send r T Lcont) := by
        simpa [hEqEp, hL] using hep
      refine ⟨ep.role, r, T, Lcont, hrole, hr'.symm, hT', hLookup, hLcont'⟩
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | select _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | branch _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim

/-- Inverse step for select: if σ(C) has a select type, C has a corresponding select type.
    From Aristotle 06b. -/
theorem inverse_step_select_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (bs' : List (Label × LocalType)) (l' : Label) (L' : LocalType)
    (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, s'⟩ = some (.select r' bs'))
    (hIn' : (l', L') ∈ bs') :
    ∃ s r bs l L,
      σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      σ.labelMap l = l' ∧
      lookupG G ⟨sid, s⟩ = some (.select r bs) ∧
      (l, L) ∈ bs ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv + mem_renameBranchesPR_inv
  obtain ⟨ep, Lep, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = s' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : Lep with
  | select r bs =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.select.injEq] at hLfull
      obtain ⟨hr', hbs'⟩ := hLfull
      rw [hbs'] at hIn'
      obtain ⟨l, L, hl, hlmap, hLmap⟩ := mem_renameBranchesPR_inv σ bs l' L' hIn'
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.select r bs) := by
        simpa [hEqEp, hL] using hep
      refine ⟨ep.role, r, bs, l, L, hrole, hr'.symm, hlmap.symm, hLookup, hl, hLmap⟩
  | send _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | branch _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim

/-- Inverse step for branch: if σ(C) has a branch type, C has a corresponding branch type.
    From Aristotle 06b. -/
theorem inverse_step_branch_exists (σ : ProtocolRenaming)
    (G : GEnv) (s' r' : Role) (bs' : List (Label × LocalType)) (l' : Label) (L' : LocalType)
    (sid : SessionId)
    (hG' : lookupG (renameGEnvPR σ G) ⟨sid, r'⟩ = some (.branch s' bs'))
    (hIn' : (l', L') ∈ bs') :
    ∃ s r bs l L,
      σ.roleMap s = s' ∧ σ.roleMap r = r' ∧
      σ.labelMap l = l' ∧
      lookupG G ⟨sid, r⟩ = some (.branch s bs) ∧
      (l, L) ∈ bs ∧
      L' = renameLocalTypePR σ L := by
  -- Use lookupG_renamePR_inv + mem_renameBranchesPR_inv
  obtain ⟨ep, Lep, hep, hep', hLfull⟩ := lookupG_renamePR_inv σ G _ _ hG'
  have hsid : ep.sid = sid := by
    have := congrArg Endpoint.sid hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hrole : σ.roleMap ep.role = r' := by
    have := congrArg Endpoint.role hep'
    simp [renameEndpointPR] at this
    exact this.symm
  have hEqEp : ({ sid := sid, role := ep.role } : Endpoint) = ep := by
    cases ep with
    | mk sid0 role0 =>
        cases hsid
        rfl
  cases hL : Lep with
  | branch s bs =>
      rw [hL] at hLfull
      simp only [renameLocalTypePR, LocalType.branch.injEq] at hLfull
      obtain ⟨hs', hbs'⟩ := hLfull
      rw [hbs'] at hIn'
      obtain ⟨l, L, hl, hlmap, hLmap⟩ := mem_renameBranchesPR_inv σ bs l' L' hIn'
      have hLookup : lookupG G { sid := sid, role := ep.role } = some (.branch s bs) := by
        simpa [hEqEp, hL] using hep
      refine ⟨s, ep.role, bs, l, L, hs'.symm, hrole, hlmap.symm, hLookup, hl, hLmap⟩
  | send _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | recv _ _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | select _ _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | end_ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | var _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim
  | mu _ =>
      rw [hL] at hLfull
      have hFalse : False := by
        simp [renameLocalTypePR] at hLfull
      exact hFalse.elim


end
