import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas

/-!
# MPST Process Typing

This module defines the typing rules for MPST processes.

## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ### Framing Lemmas -/

/-- HasTypeVal is stable under framing on the left of G. -/
theorem HasTypeVal_frame_left {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    DisjointG G₁ G₂ →
    HasTypeVal G₂ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  intro hDisj hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
      exact HasTypeVal.prod (HasTypeVal_frame_left hDisj h₁) (HasTypeVal_frame_left hDisj h₂)
  | chan h =>
      rename_i e L
      have hDisjSym := DisjointG_symm hDisj
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym h
      have hLookup : lookupG (G₁ ++ G₂) e = some L := by
        simpa [lookupG_append_right hNone] using h
      exact HasTypeVal.chan hLookup

/-- Pre-update typing is stable under framing on the left of G (no S changes). -/
private theorem HasTypeProcPre_frame_G_branch
    {Ssh Sown : SEnv} {G₁ G : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} :
    DisjointG G₁ G →
    lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e.sid e.role) →
    lookupG G e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length) {G₁' : GEnv},
        DisjointG G₁' (updateG G e (bs.get ⟨i, hi⟩).2) →
          HasTypeProcPre Ssh Sown
            (G₁' ++ updateG G e (bs.get ⟨i, hi⟩).2)
            (procs.get ⟨i, hip⟩).2) →
    HasTypeProcPre Ssh Sown (G₁ ++ G) (.branch k procs) := by
  intro hDisj hk hG hLen hLbl hProcs ih
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch p bs, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := by
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G = (∅ : Set SessionId) := by
      simpa [DisjointG, GEnvDisjoint] using hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact this.elim
  have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
  have hG' : lookupG (G₁ ++ G) e = some (.branch p bs) := by
    simpa [lookupG_append_right hNone] using hG
  have hProcs' :
      ∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2 := by
    intro i hi hip
    have hSub : SessionsOf (updateG G e (bs.get ⟨i, hi⟩).2) ⊆ SessionsOf G := by
      intro s hs
      rcases hs with ⟨e', L', hLookup, hSid'⟩
      by_cases hEq : e' = e
      · subst hEq
        simpa [hSid'] using hSid
      · have hLookup' : lookupG G e' = some L' := by
          have h :=
            lookupG_update_neq (env:=G) (e:=e) (e':=e') (L:= (bs.get ⟨i, hi⟩).2) (Ne.symm hEq)
          rw [h] at hLookup
          exact hLookup
        exact ⟨e', L', hLookup', hSid'⟩
    have hDisj' : DisjointG G₁ (updateG G e (bs.get ⟨i, hi⟩).2) := by
      have hDisjSym := DisjointG_symm hDisj
      have hDisj'' :=
        DisjointG_of_subset_left (G₁:=G) (G₁':=updateG G e (bs.get ⟨i, hi⟩).2)
          (G₂:=G₁) hSub hDisjSym
      exact DisjointG_symm hDisj''
    have hPre' := ih i hi hip (G₁':=G₁) hDisj'
    have hUpd :
        updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2 =
          G₁ ++ updateG G e (bs.get ⟨i, hi⟩).2 :=
      updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:= (bs.get ⟨i, hi⟩).2) hNone
    rw [hUpd.symm] at hPre'
    exact hPre'
  exact HasTypeProcPre.branch hk hG' hLen hLbl hProcs'

theorem HasTypeProcPre_frame_G {Ssh Sown : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh Sown (G₁ ++ G₂) P := by
  intro hDisj hPre
  induction hPre generalizing G₁
  case skip =>
    exact HasTypeProcPre.skip
  case send hk hG hx =>
    rename_i G' k x e q T L
    have hSid : e.sid ∈ SessionsOf G' := ⟨e, .send q T L, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G' := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G' = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G') e = some (.send q T L) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.send hk hG' hx
  case recv hk hG hSsh =>
    rename_i G' k x e p T L
    have hSid : e.sid ∈ SessionsOf G' := ⟨e, .recv p T L, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G' := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G' = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G') e = some (.recv p T L) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.recv hk hG' hSsh
  case select hk hG hFind =>
    rename_i G' k l e q bs L
    have hSid : e.sid ∈ SessionsOf G' := ⟨e, .select q bs, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G' := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G' = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G') e = some (.select q bs) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.select hk hG' hFind
  case branch hk hG hLen hLbl hProcs ih =>
    rename_i G' k procs e p bs
    exact HasTypeProcPre_frame_G_branch
      (G₁:=G₁) (G:=G') (k:=k) (procs:=procs) (e:=e) (p:=p) (bs:=bs)
      hDisj hk hG hLen hLbl hProcs
      (by
        intro i hi hip G₁' hDisj'
        exact ih i hi hip hDisj')
  case seq hP hQ ihP ihQ =>
    exact HasTypeProcPre.seq (ihP hDisj) (ihQ hDisj)
  case par hDisjS hP hQ ihP ihQ =>
    exact HasTypeProcPre.par hDisjS (ihP hDisj) (ihQ hDisj)
  case assign hSsh hv =>
    exact HasTypeProcPre.assign hSsh (HasTypeVal_frame_left hDisj hv)

/-- Disjointness with an appended SEnv implies disjointness with the left side. -/
private theorem DisjointS_of_append_left {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₂ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₂ (S₂ ++ S₃) := SEnvDomSubset_append_left (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- Disjointness with an appended SEnv implies disjointness with the right side. -/
private theorem DisjointS_of_append_right {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₃ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₃ (S₂ ++ S₃) := SEnvDomSubset_append_right (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- DisjointG with an appended GEnv implies disjointness with the left side. -/
private theorem DisjointG_of_append_left {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₂ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₂ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_left (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- DisjointG with an appended GEnv implies disjointness with the right side. -/
private theorem DisjointG_of_append_right {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₃ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₃ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_right (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- Pre-update typing is stable under framing on the left of S/G. -/
theorem HasTypeProcPre_frame_left {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh S₂ G₂ P →
    HasTypeProcPre Ssh (S₁ ++ S₂) (G₁ ++ G₂) P := by
  intro hDisjS hDisjG hPre
  induction hPre generalizing G₁ S₁
  case skip =>
    exact HasTypeProcPre.skip
  case send hk hG hx =>
    rename_i S₂ G₂ k x e q T L
    have hk' : lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) k = some (.chan e.sid e.role) := by
      have hk0 : lookupSEnv (Ssh ++ S₂) k = some (.chan e.sid e.role) := by
        simpa [SEnvAll] using hk
      have hk1 := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisjS hk0
      simpa [SEnvAll] using hk1
    have hx' : lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) x = some T := by
      have hx0 : lookupSEnv (Ssh ++ S₂) x = some T := by
        simpa [SEnvAll] using hx
      have hx1 := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisjS hx0
      simpa [SEnvAll] using hx1
    have hSid : e.sid ∈ SessionsOf G₂ := ⟨e, .send q T L, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisjG
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G₂) e = some (.send q T L) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.send hk' hG' hx'
  case recv hk hG hSsh =>
    rename_i S₂ G₂ k x e p T L
    have hk' : lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) k = some (.chan e.sid e.role) := by
      have hk0 : lookupSEnv (Ssh ++ S₂) k = some (.chan e.sid e.role) := by
        simpa [SEnvAll] using hk
      have hk1 := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisjS hk0
      simpa [SEnvAll] using hk1
    have hSid : e.sid ∈ SessionsOf G₂ := ⟨e, .recv p T L, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisjG
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G₂) e = some (.recv p T L) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.recv hk' hG' hSsh
  case select hk hG hFind =>
    rename_i S₂ G₂ k l e q bs L
    have hk' : lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) k = some (.chan e.sid e.role) := by
      have hk0 : lookupSEnv (Ssh ++ S₂) k = some (.chan e.sid e.role) := by
        simpa [SEnvAll] using hk
      have hk1 := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisjS hk0
      simpa [SEnvAll] using hk1
    have hSid : e.sid ∈ SessionsOf G₂ := ⟨e, .select q bs, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisjG
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G₂) e = some (.select q bs) := by
      simpa [lookupG_append_right hNone] using hG
    exact HasTypeProcPre.select hk' hG' hFind
  case branch hk hG hLen hLbl hProcs ih =>
    rename_i S₂ G₂ k procs e p bs
    have hk' : lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) k = some (.chan e.sid e.role) := by
      have hk0 : lookupSEnv (Ssh ++ S₂) k = some (.chan e.sid e.role) := by
        simpa [SEnvAll] using hk
      have hk1 := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisjS hk0
      simpa [SEnvAll] using hk1
    have hSid : e.sid ∈ SessionsOf G₂ := ⟨e, .branch p bs, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisjG
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G₂) e = some (.branch p bs) := by
      simpa [lookupG_append_right hNone] using hG
    have hProcs' :
        ∀ i (hi : i < bs.length) (hip : i < procs.length),
          HasTypeProcPre Ssh (S₁ ++ S₂)
            (updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2)
            (procs.get ⟨i, hip⟩).2 := by
      intro i hi hip
      have hSub : SessionsOf (updateG G₂ e (bs.get ⟨i, hi⟩).2) ⊆ SessionsOf G₂ := by
        intro s hs
        rcases hs with ⟨e', L', hLookup, hSid'⟩
        by_cases hEq : e' = e
        · subst hEq
          simpa [hSid'] using hSid
        · have hLookup' : lookupG G₂ e' = some L' := by
            have h := lookupG_update_neq (env:=G₂) (e:=e) (e':=e') (L:= (bs.get ⟨i, hi⟩).2) (Ne.symm hEq)
            rw [h] at hLookup
            exact hLookup
          exact ⟨e', L', hLookup', hSid'⟩
      have hDisj' : DisjointG G₁ (updateG G₂ e (bs.get ⟨i, hi⟩).2) := by
        have hDisjSym := DisjointG_symm hDisjG
        have hDisj'' :=
          DisjointG_of_subset_left (G₁:=G₂) (G₁':=updateG G₂ e (bs.get ⟨i, hi⟩).2)
            (G₂:=G₁) hSub hDisjSym
        exact DisjointG_symm hDisj''
      have hPre' := ih i hi hip (S₁:=S₁) (G₁:=G₁) hDisjS hDisj'
      have hUpd :
          updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2 =
            G₁ ++ updateG G₂ e (bs.get ⟨i, hi⟩).2 :=
        updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:= (bs.get ⟨i, hi⟩).2) hNone
      rw [hUpd.symm] at hPre'
      exact hPre'
    exact HasTypeProcPre.branch hk' hG' hLen hLbl hProcs'
  case seq hP hQ ihP ihQ =>
    exact HasTypeProcPre.seq (ihP hDisjS hDisjG) (ihQ hDisjS hDisjG)
  case par hDisjS' hP hQ ihP ihQ =>
    rename_i S₁' S₂' G P Q
    -- derive disjointness with the new left frame
    have hDisjS1 : DisjointS S₁ S₁' :=
      DisjointS_of_append_left (S₁:=S₁) (S₂:=S₁') (S₃:=S₂') hDisjS
    have hDisjS2 : DisjointS S₁ S₂' :=
      DisjointS_of_append_right (S₁:=S₁) (S₂:=S₁') (S₃:=S₂') hDisjS
    have hP' := ihP (S₁:=S₁) (G₁:=G₁) hDisjS1 hDisjG
    have hQ' := HasTypeProcPre_frame_G (Ssh:=Ssh) (Sown:=S₂') (G₁:=G₁) (G₂:=G) hDisjG hQ
    have hDisjS' : DisjointS (S₁ ++ S₁') S₂' :=
      DisjointS_append_left (S₁:=S₁) (S₁':=S₁') (S₂:=S₂') hDisjS2 hDisjS'
    -- Rebuild par with framed components; coerce by lookup-extensionality.
    have hAssoc : (S₁ ++ S₁') ++ S₂' = S₁ ++ (S₁' ++ S₂') := by
      simpa [List.append_assoc]
    simpa [hAssoc] using HasTypeProcPre.par hDisjS' hP' hQ'
  case assign hSsh hv =>
    exact HasTypeProcPre.assign hSsh (HasTypeVal_frame_left hDisjG hv)

/-- Sessions only shrink under pre-out typing (no new sessions introduced).

    NOTE: This is assumed for now; branch typing with empty branches does not
    constrain G'. -/
axiom SessionsOf_subset_of_HasTypeProcPreOut
    {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SessionsOf G' ⊆ SessionsOf G

/-- Lift SEnvAll lookups across a right frame (left-biased). -/
private theorem lookupSEnv_all_frame_right
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh S₁) x = some T →
    lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) x = some T := by
  -- Appending on the right preserves existing left-biased lookups.
  intro hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ S₁) (S₂:=S₂) (x:=x) (T:=T) hLookup
  have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=S₁) (S₃:=S₂) (x:=x)
  simpa [SEnvAll, hEq] using hLeft

/-- Lift a GEnv lookup across a left frame using disjointness. -/
private theorem lookupG_frame_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  -- Disjointness forces the lookup to come from the right.
  intro hDisj hLookup
  have hDisjSym := DisjointG_symm hDisj
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hLookup
  simpa [lookupG_append_right hNone] using hLookup

/-- GEnv disjointness is preserved when updating an existing endpoint on the right. -/
private theorem DisjointG_updateG_left
    {G₁ G₂ : GEnv} {e : Endpoint} {L L' : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    DisjointG G₁ (updateG G₂ e L') := by
  -- Updating an existing endpoint does not add new session ids.
  intro hDisj hLookup
  have hSub : SessionsOf (updateG G₂ e L') ⊆ SessionsOf G₂ := by
    intro s hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases hEq : e' = e
    · have hLookup'' : lookupG G₂ e' = some L := by
        simpa [hEq] using hLookup
      exact ⟨e', L, hLookup'', hSid⟩
    · have hLookup'' : lookupG G₂ e' = some L'' := by
        have h := lookupG_update_neq (env:=G₂) (e:=e) (e':=e') (L:=L') (Ne.symm hEq)
        simpa [h] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩
  have hDisjSym := DisjointG_symm hDisj
  have hDisj' :=
    DisjointG_of_subset_left (G₁:=G₂) (G₁':=updateG G₂ e L') (G₂:=G₁) hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- Right framing preserves HasTypeVal without extra disjointness. -/
private theorem HasTypeVal_frame_right {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    HasTypeVal G₁ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  -- The left environment dominates lookups.
  intro hv
  induction hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ ih₁ ih₂ => exact HasTypeVal.prod ih₁ ih₂
  | chan h =>
      exact HasTypeVal.chan (lookupG_append_left h)

/-- If the right frame is disjoint from a lookup on the left, the right lookup is none. -/
private theorem lookupSEnv_none_of_disjoint_right {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₂ S₁ →
    lookupSEnv S₁ x = some T →
    lookupSEnv S₂ x = none := by
  -- Disjointness forbids any binding for x on the right.
  intro hDisj hLeft
  by_cases hNone : lookupSEnv S₂ x = none
  · exact hNone
  · cases hRight : lookupSEnv S₂ x with
    | none => exact (hNone hRight).elim
    | some T₂ => exact (hDisj x T₂ T hRight hLeft).elim

/-- Empty SEnv is disjoint from any environment. -/
private theorem DisjointS_left_empty (S : SEnv) : DisjointS (∅ : SEnv) S := by
  -- Empty lookup is never `some`, so disjointness is trivial.
  intro x T₁ T₂ hLeft hRight
  cases hLeft

/-- Disjointness distributes over right appends. -/
private theorem DisjointS_append_right
    {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh S₁ →
    DisjointS Ssh S₂ →
    DisjointS Ssh (S₁ ++ S₂) := by
  -- Route the append lookup to the appropriate side.
  intro hDisj1 hDisj2 x T₁ T₂ hLsh hL12
  cases hL1 : lookupSEnv S₁ x with
  | some T₁' =>
      have hEq : T₁' = T₂ := by
        have hLeft := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁') hL1
        exact Option.some.inj (by simpa [hLeft] using hL12)
      exact hDisj1 x T₁ T₁' hLsh (by simpa [hEq] using hL1)
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hL1
      have hL2 : lookupSEnv S₂ x = some T₂ := by
        simpa [hRight] using hL12
      exact hDisj2 x T₁ T₂ hLsh hL2

/-- Appending the empty SEnv on the right is a no-op. -/
private theorem SEnv_append_empty_right (S : SEnv) : S ++ (∅ : SEnv) = S := by
  simpa using (List.append_nil S)

private axiom updateSEnv_append_left_any {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂

/-- Shorthand for left-framing on pre-out typing. -/
private abbrev FrameLeft (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the left framing goal as a reusable predicate.
  ∀ {S₂' G₂' W Δ}, DisjointS S₁ S₂ → DisjointS S₁ S₂' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁ ++ S₂') (G₁ ++ G₂') W Δ

/-- Shorthand for right-framing on pre-out typing. -/
private abbrev FrameRight (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the right framing goal as a reusable predicate.
  ∀ {S₁' G₁' W Δ}, DisjointS S₂ S₁ → DisjointS S₂ S₁' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ

/-- Right framing for branch pre-typing. -/
private theorem frame_right_pre_branch
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} :
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
      (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
      HasTypeProcPre Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2)
        (procs.get ⟨i, hip⟩).2) →
    HasTypeProcPre Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.branch k procs) := by
  -- Rebuild the branch rule with framed lookups.
  intro hk hG hLen hLbl hProcs'
  exact HasTypeProcPre.branch (lookupSEnv_all_frame_right hk) (lookupG_append_left hG)
    hLen hLbl hProcs'

/-- Right framing for branch pre-typing using an IH. -/
private theorem frame_right_pre_branch_of
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} :
    DisjointS S₂ S₁ →
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
      (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length) {S₂' : SEnv} {G₂' : GEnv},
      DisjointS S₂' S₁ →
      HasTypeProcPre Ssh (S₁ ++ S₂') (updateG G₁ e (bs.get ⟨i, hi⟩).2 ++ G₂')
        (procs.get ⟨i, hip⟩).2) →
    HasTypeProcPre Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.branch k procs) := by
  -- Build each branch via IH and rewrite the G update.
  intro hDisj hk hG hLen hLbl ih
  have hProcs' :
      ∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2 := by
    intro i hi hip
    have hPre' := ih i hi hip (S₂':=S₂) (G₂':=G₂) hDisj
    have hUpd := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
      (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
    rw [hUpd.symm] at hPre'
    exact hPre'
  exact frame_right_pre_branch hk hG hLen hLbl hProcs'

/-- Right framing for parallel pre-typing. -/
private theorem frame_right_pre_par
    {Ssh S₁ S₂ Sfr : SEnv} {G₁ Gfr : GEnv} {P Q : Process} :
    DisjointS Sfr (S₁ ++ S₂) →
    DisjointS S₁ S₂ →
    HasTypeProcPre Ssh S₁ (G₁ ++ Gfr) P →
    HasTypeProcPre Ssh (S₂ ++ Sfr) (G₁ ++ Gfr) Q →
    HasTypeProcPre Ssh ((S₁ ++ S₂) ++ Sfr) (G₁ ++ Gfr) (.par P Q) := by
  -- Push the frame to the right component and re-associate.
  intro hDisj hDisjPQ hP hQ
  have hDisjS1 : DisjointS S₁ Sfr := by
    have hDisj' : DisjointS Sfr S₁ := DisjointS_of_append_left hDisj
    exact DisjointS_symm hDisj'
  have hDisjOut : DisjointS S₁ (S₂ ++ Sfr) :=
    DisjointS_append_right hDisjPQ hDisjS1
  have hPar := HasTypeProcPre.par hDisjOut hP hQ
  simpa [SEnv_append_assoc] using hPar

/-- Right framing for parallel pre-typing using IHs. -/
private theorem frame_right_pre_par_of
    {Ssh S₁ S₂ Sfr : SEnv} {G₁ Gfr : GEnv} {P Q : Process} :
    DisjointS Sfr (S₁ ++ S₂) →
    DisjointS S₁ S₂ →
    (∀ {S₂' G₂'}, DisjointS S₂' S₁ →
      HasTypeProcPre Ssh (S₁ ++ S₂') (G₁ ++ G₂') P) →
    (∀ {S₂' G₂'}, DisjointS S₂' S₂ →
      HasTypeProcPre Ssh (S₂ ++ S₂') (G₁ ++ G₂') Q) →
    HasTypeProcPre Ssh ((S₁ ++ S₂) ++ Sfr) (G₁ ++ Gfr) (.par P Q) := by
  -- Frame P with empty S, Q with the right frame, then reassemble.
  intro hDisj hDisjPQ ihP ihQ
  have hDisjR : DisjointS Sfr S₂ := DisjointS_of_append_right hDisj
  have hP' : HasTypeProcPre Ssh S₁ (G₁ ++ Gfr) P := by
    have hP0 := ihP (S₂':=∅) (G₂':=Gfr) (DisjointS_left_empty S₁)
    simpa [SEnv_append_empty_right] using hP0
  have hQ' : HasTypeProcPre Ssh (S₂ ++ Sfr) (G₁ ++ Gfr) Q := ihQ hDisjR
  exact frame_right_pre_par hDisj hDisjPQ hP' hQ'

/-- Right framing for pre-update typing. -/
private theorem HasTypeProcPre_frame_right
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS S₂ S₁ →
    HasTypeProcPre Ssh S₁ G₁ P →
    HasTypeProcPre Ssh (S₁ ++ S₂) (G₁ ++ G₂) P := by
  -- Induct on pre-typing; right frames preserve left-biased lookups.
  intro hDisj hPre
  induction hPre generalizing S₂ G₂ with
  | skip =>
      exact HasTypeProcPre.skip
  | send hk hG hx =>
      exact HasTypeProcPre.send (lookupSEnv_all_frame_right hk) (lookupG_append_left hG)
        (lookupSEnv_all_frame_right hx)
  | recv hk hG hSsh =>
      exact HasTypeProcPre.recv (lookupSEnv_all_frame_right hk) (lookupG_append_left hG) hSsh
  | select hk hG hFind =>
      exact HasTypeProcPre.select (lookupSEnv_all_frame_right hk) (lookupG_append_left hG) hFind
  | branch hk hG hLen hLbl hProcs ih =>
      exact frame_right_pre_branch_of hDisj hk hG hLen hLbl ih
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisj) (ihQ hDisj)
  | par hDisjPQ hP hQ ihP ihQ =>
      exact frame_right_pre_par_of hDisj hDisjPQ ihP ihQ
  | assign hSsh hv =>
      exact HasTypeProcPre.assign hSsh (HasTypeVal_frame_right hv)

/-- Left framing for skip. -/
private theorem frame_left_skip {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} :
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) .skip (S₁ ++ S₂) (G₁ ++ G₂) [] ∅ := by
  -- Skip leaves environments unchanged.
  simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂))

/-- Left framing for send. -/
private theorem frame_left_send
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {q : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.send q T L) →
    lookupSEnv (SEnvAll Ssh S₂) x = some T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.send k x)
      (S₁ ++ S₂) (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hx
  have hk' := lookupSEnv_all_frame_left hDisjS hk
  have hx' := lookupSEnv_all_frame_left hDisjS hx
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hx')

/-- Left framing for recv_new. -/
private theorem frame_left_recv_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.recv k x)
      (S₁ ++ updateSEnv S₂ x T) (G₁ ++ updateG G₂ e L) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to show x is not in the left frame.
  intro hDisjS hDisjS' hDisjG hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_left hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hSown' : lookupSEnv (S₁ ++ S₂) x = none := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hx1
    simpa [hEq, hSown] using hSown
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hUpdS := updateSEnv_append_left (Ssh:=S₁) (Sown:=S₂) (x:=x) (T:=T) hx1
  simpa [hUpdG, hUpdS] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hSsh hSown')

/-- Left framing for recv_old. -/
private theorem frame_left_recv_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} {T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.recv k x)
      (S₁ ++ updateSEnv S₂ x T) (G₁ ++ updateG G₂ e L) [x] ∅ := by
  -- Old recv: x already in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_left hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hSown' : lookupSEnv (S₁ ++ S₂) x = some T' := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hx1
    simpa [hEq] using hSown
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hUpdS := updateSEnv_append_left (Ssh:=S₁) (Sown:=S₂) (x:=x) (T:=T) hx1
  simpa [hUpdG, hUpdS] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hSsh hSown')

/-- Left framing for select. -/
private theorem frame_left_select
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {l : Label} {e : Endpoint}
    {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.select q bs) →
    bs.find? (fun b => b.1 == l) = some (l, L) →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.select k l)
      (S₁ ++ S₂) (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hFind
  have hk' := lookupSEnv_all_frame_left hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hFind)

/-- Frame-left helper for branch pre-typing. -/
private theorem frame_left_pre_updateG
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L0 →
    HasTypeProcPre Ssh S₂ (updateG G₂ e L) P →
    HasTypeProcPre Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e L) P := by
  -- Frame pre-typing and rewrite the update on G.
  intro hDisjS hDisjG hG hPre
  have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
    DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hDisjG hG
  have hPre' := HasTypeProcPre_frame_left (S₁:=S₁) (S₂:=S₂) (G₁:=G₁)
    (G₂:=updateG G₂ e L) hDisjS hDisjG' hPre
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using hPre'

/-- Left framing for branch. -/
private theorem frame_left_branch
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh S₂ (updateG G₂ e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh S₂ (updateG G₂ e L) P S₂' G₂' W Δ) →
    SEnvDomSubset S₂ S₂' →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      DisjointS S₁ S₂ →
      DisjointS S₁ S₂' →
      DisjointG G₁ (updateG G₂ e L) →
      HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ updateG G₂ e L) P
        (S₁ ++ S₂') (G₁ ++ G₂') W Δ) →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.branch k procs)
      (S₁ ++ S₂') (G₁ ++ G₂') W Δ := by
  -- Frame each branch using the provided IH and rebuild the constructor.
  intro hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hDom ih
  have hk' := lookupSEnv_all_frame_left hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hProcs' :
      ∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e (bs.get ⟨j, hj⟩).2)
          (procs.get ⟨j, hjp⟩).2 := by
    intro j hj hjp
    exact frame_left_pre_updateG hDisjS hDisjG hG (hProcs j hj hjp)
  have hOut' :
      ∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e L)
          P (S₁ ++ S₂') (G₁ ++ G₂') W Δ := by
    intro lbl P L hP hB
    have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
      DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=.branch p bs) (L':=L) hDisjG hG
    have hPre' := ih lbl P L hP hB hDisjS hDisjS' hDisjG'
    have hDisjSym := DisjointG_symm hDisjG
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
    have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
    simpa [hUpd] using hPre'
  have hDom' := SEnvDomSubset_append_right_of_domsubset (S₁:=S₁) (S₂':=S₂) (S₂:=S₂') hDom
  exact HasTypeProcPreOut.branch hk' hG' hLen hLbl hProcs' hOut' hDom'

/-- Left framing for assign_new. -/
private theorem frame_left_assign_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T : ValType} :
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.assign x v)
      (S₁ ++ updateSEnv S₂ x T) (G₁ ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to keep x absent from the left frame.
  intro hDisjS' hDisjG hSsh hSown hv
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hSown' : lookupSEnv (S₁ ++ S₂) x = none := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hx1
    simpa [hEq, hSown] using hSown
  have hUpdS := updateSEnv_append_left (Ssh:=S₁) (Sown:=S₂) (x:=x) (T:=T) hx1
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  simpa [hUpdS] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hSsh hSown' hv')

/-- Left framing for assign_old. -/
private theorem frame_left_assign_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.assign x v)
      (S₁ ++ updateSEnv S₂ x T) (G₁ ++ G₂) [x] ∅ := by
  -- Old assignment: x is in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hSsh hSown hv
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hSown' : lookupSEnv (S₁ ++ S₂) x = some T' := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hx1
    simpa [hEq] using hSown
  have hUpdS := updateSEnv_append_left (Ssh:=S₁) (Sown:=S₂) (x:=x) (T:=T) hx1
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  simpa [hUpdS] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hSsh hSown' hv')

/-- Left framing for par: frame only the left component. -/
private theorem frame_left_par
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P Q : Process}
    {Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit S₂ G₂)
    (hSfin : Sfin = S₁' ++ S₂')
    (hGfin : Gfin = G₁' ++ G₂')
    (hW : Wfin = W₁ ++ W₂)
    (hΔ : Δfin = Δ₁ ++ Δ₂)
    (hDisjG : DisjointG split.G1 split.G2)
    (hDisjS : DisjointS split.S1 split.S2)
    (hDisjS_left : DisjointS S₁' split.S2)
    (hDisjS_right : DisjointS split.S1 S₂')
    (hDisjS' : DisjointS S₁' S₂')
    (hDisjW : DisjointW W₁ W₂)
    (hDisjΔ : DisjointS Δ₁ Δ₂)
    (hQ : HasTypeProcPreOut Ssh split.S2 split.G2 Q S₂' G₂' W₂ Δ₂)
    (hDisjS_frame : DisjointS S₁ S₂)
    (hDisjS_frame' : DisjointS S₁ Sfin)
    (hDisjG_frame : DisjointG G₁ G₂)
    (ihP : DisjointS S₁ split.S1 → DisjointS S₁ S₁' → DisjointG G₁ split.G1 →
      HasTypeProcPreOut Ssh (S₁ ++ split.S1) (G₁ ++ split.G1) P (S₁ ++ S₁') (G₁ ++ G₁') W₁ Δ₁) :
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.par P Q)
      (S₁ ++ Sfin) (G₁ ++ Gfin) Wfin Δfin := by
  -- Frame the left branch and rebuild the split.
  have hDisjS1 : DisjointS S₁ split.S1 :=
    DisjointS_of_append_left (by simpa [split.hS] using hDisjS_frame)
  have hDisjS2 : DisjointS S₁ split.S2 :=
    DisjointS_of_append_right (by simpa [split.hS] using hDisjS_frame)
  have hDisjS1' : DisjointS S₁ S₁' :=
    DisjointS_of_append_left (by simpa [hSfin] using hDisjS_frame')
  have hDisjG1 : DisjointG G₁ split.G1 :=
    DisjointG_of_append_left (by simpa [split.hG] using hDisjG_frame)
  have hP' := ihP hDisjS1 hDisjS1' hDisjG1
  let splitOut : ParSplit (S₁ ++ S₂) (G₁ ++ G₂) :=
    { S1 := S₁ ++ split.S1, S2 := split.S2,
      G1 := G₁ ++ split.G1, G2 := split.G2,
      hS := by simpa [split.hS] using (SEnv_append_assoc S₁ split.S1 split.S2),
      hG := by simp [split.hG, List.append_assoc] }
  have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
    have hDisjG2 : DisjointG G₁ split.G2 :=
      DisjointG_of_append_right (by simpa [split.hG] using hDisjG_frame)
    simpa [splitOut] using DisjointG_append_left hDisjG2 hDisjG
  have hDisjSOut : DisjointS splitOut.S1 splitOut.S2 :=
    by simpa [splitOut] using DisjointS_append_left hDisjS2 hDisjS
  have hDisjS_left_out : DisjointS (S₁ ++ S₁') split.S2 :=
    DisjointS_append_left hDisjS2 hDisjS_left
  have hDisjS2' : DisjointS S₁ S₂' :=
    DisjointS_of_append_right (by simpa [hSfin] using hDisjS_frame')
  have hDisjS_right_out : DisjointS (S₁ ++ split.S1) S₂' :=
    DisjointS_append_left hDisjS2' hDisjS_right
  have hDisjS_out : DisjointS (S₁ ++ S₁') S₂' :=
    DisjointS_append_left hDisjS2' hDisjS'
  simpa [hSfin, hGfin, hW, hΔ, SEnv_append_assoc, List.append_assoc] using
    (HasTypeProcPreOut.par splitOut rfl rfl rfl rfl
      hDisjGOut hDisjSOut hDisjS_left_out hDisjS_right_out hDisjS_out hDisjW hDisjΔ hP' hQ)


/-- Pre-out typing is stable under framing on the left of S/G. -/
theorem HasTypeProcPreOut_frame_left
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁ ++ S₂') (G₁ ++ G₂') W Δ := by
  -- Induct on the pre-out derivation and apply the local frame lemmas.
  intro hDisjS hDisjS' hDisjG hPre
  induction hPre with
  | skip => exact frame_left_skip
  | send hk hG hx => exact frame_left_send hDisjS hDisjG hk hG hx
  | recv_new hk hG hSsh hSown =>
      exact frame_left_recv_new hDisjS hDisjS' hDisjG hk hG hSsh hSown
  | recv_old hk hG hSsh hSown => exact frame_left_recv_old hDisjS hDisjG hk hG hSsh hSown
  | select hk hG hFind => exact frame_left_select hDisjS hDisjG hk hG hFind
  | branch hk hG hLen hLbl hProcs hOut hDom ih =>
      exact frame_left_branch hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hDom ih
  | seq hP hQ ihP ihQ =>
      -- Intermediate environment is disjoint by dom-subset from Q.
      have hDomQ := HasTypeProcPreOut_domsubset hQ
      have hDisjS_mid := DisjointS_of_domsubset_right hDomQ hDisjS'
      have hSubG := SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG_mid := by
        have hSym := DisjointG_symm hDisjG
        have hTmp := DisjointG_of_subset_left hSubG hSym
        exact DisjointG_symm hTmp
      have hP' := ihP hDisjS hDisjS_mid hDisjG
      have hQ' := ihQ hDisjS_mid hDisjS' hDisjG_mid
      exact HasTypeProcPreOut.seq hP' hQ'
  | par split hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right hDisjS_fin
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      exact frame_left_par split hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right
        hDisjS_fin hDisjW hDisjΔ hQ hDisjS hDisjS' hDisjG ihP
  | assign_new hSsh hSown hv => exact frame_left_assign_new hDisjS' hDisjG hSsh hSown hv
  | assign_old hSsh hSown hv => exact frame_left_assign_old hDisjS hDisjG hSsh hSown hv

/-- Right framing for skip. -/
private theorem frame_right_skip {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} :
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) .skip (S₁ ++ S₂) (G₁ ++ G₂) [] ∅ := by
  -- Skip leaves environments unchanged.
  simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂))

/-- Right framing for send. -/
private theorem frame_right_send
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {q : Role}
    {T : ValType} {L : LocalType} :
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.send q T L) →
    lookupSEnv (SEnvAll Ssh S₁) x = some T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.send k x)
      (S₁ ++ S₂) (updateG G₁ e L ++ G₂) [] ∅ := by
  -- Lift lookups across the right frame and rewrite the update.
  intro hk hG hx
  have hk' := lookupSEnv_all_frame_right (S₂:=S₂) hk
  have hx' := lookupSEnv_all_frame_right (S₂:=S₂) hx
  have hG' := lookupG_append_left (G₂:=G₂) hG
  have hUpd := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.send q T L) (L':=L) hG
  simpa [hUpd] using
    (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hx')

/-- Right framing for recv_new. -/
private theorem frame_right_recv_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₂ (updateSEnv S₁ x T) →
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₁ x = none →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.recv k x)
      (updateSEnv S₁ x T ++ S₂) (updateG G₁ e L ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to keep x absent from the right frame.
  intro hDisjS' hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_right (S₂:=S₂) hk
  have hG' := lookupG_append_left (G₂:=G₂) hG
  have hx2 : lookupSEnv (updateSEnv S₁ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hNone2 : lookupSEnv S₂ x = none := lookupSEnv_none_of_disjoint_right hDisjS' hx2
  have hSown' : lookupSEnv (S₁ ++ S₂) x = none := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hSown
    simpa [hEq] using hNone2
  have hUpdS := updateSEnv_append_left_any (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T)
  have hUpdG := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.recv p T L) (L':=L) hG
  simpa [hUpdS, hUpdG] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hSsh hSown')

/-- Right framing for recv_old. -/
private theorem frame_right_recv_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} {T' : ValType} :
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₁ x = some T' →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.recv k x)
      (updateSEnv S₁ x T ++ S₂) (updateG G₁ e L ++ G₂) [x] ∅ := by
  -- The left binding of x is preserved by right framing.
  intro hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_right (S₂:=S₂) hk
  have hG' := lookupG_append_left (G₂:=G₂) hG
  have hSown' : lookupSEnv (S₁ ++ S₂) x = some T' := lookupSEnv_append_left hSown
  have hUpdS := updateSEnv_append_left_any (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T)
  have hUpdG := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.recv p T L) (L':=L) hG
  simpa [hUpdS, hUpdG] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hSsh hSown')

/-- Right framing for select. -/
private theorem frame_right_select
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {l : Label} {e : Endpoint}
    {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.select q bs) →
    bs.find? (fun b => b.1 == l) = some (l, L) →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.select k l)
      (S₁ ++ S₂) (updateG G₁ e L ++ G₂) [] ∅ := by
  -- Right framing preserves the select lookup and update.
  intro hk hG hFind
  have hk' := lookupSEnv_all_frame_right (S₂:=S₂) hk
  have hG' := lookupG_append_left (G₂:=G₂) hG
  have hUpd := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.select q bs) (L':=L) hG
  simpa [hUpd] using
    (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hk' hG' hFind)

/-! Right-framing helpers for branch typing. -/

/-- Frame right for branch pre-typing. -/
private theorem frame_right_branch_pre
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
    DisjointS S₂ S₁ →
    lookupG G₁ e = some (.branch p bs) →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh S₁ (updateG G₁ e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
    ∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e (bs.get ⟨j, hj⟩).2)
        (procs.get ⟨j, hjp⟩).2 := by
  -- Frame each branch and rewrite the G update.
  intro hDisjS hG hProcs j hj hjp
  have hPre := HasTypeProcPre_frame_right (G₂:=G₂) hDisjS (hProcs j hj hjp)
  have hUpd := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨j, hj⟩).2) hG
  rw [hUpd]
  exact hPre

/-- Frame right for branch outputs. -/
private theorem frame_right_branch_out
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)}
    {S₁' : SEnv} {G₁' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₂ S₁ → DisjointS S₂ S₁' → DisjointG G₁ G₂ →
    lookupG G₁ e = some (.branch p bs) →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh S₁ (updateG G₁ e L) P S₁' G₁' W Δ) →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      DisjointS S₂ S₁ →
      DisjointS S₂ S₁' →
      DisjointG (updateG G₁ e L) G₂ →
      HasTypeProcPreOut Ssh (S₁ ++ S₂) (updateG G₁ e L ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ) →
    ∀ lbl P L, procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh (S₁ ++ S₂) (updateG (G₁ ++ G₂) e L)
        P (S₁' ++ S₂) (G₁' ++ G₂) W Δ := by
  -- Apply the branch IH and rewrite the G update.
  intro hDisjS hDisjS' hDisjG hG hOut ih lbl P L hP hB
  have hDisjG' : DisjointG (updateG G₁ e L) G₂ := by
    have hSym := DisjointG_symm hDisjG
    have hTmp := DisjointG_updateG_left (G₁:=G₂) (G₂:=G₁) (e:=e)
      (L:=.branch p bs) (L':=L) hSym hG
    exact DisjointG_symm hTmp
  have hPre' := ih lbl P L hP hB hDisjS hDisjS' hDisjG'
  have hUpd := updateG_append_left_hit (G₁:=G₁) (G₂:=G₂) (e:=e)
    (L:=.branch p bs) (L':=L) hG
  simpa [hUpd] using hPre'

/-- Right framing for branch. -/
private theorem frame_right_branch
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)}
    {S₁' : SEnv} {G₁' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₂ S₁ → DisjointS S₂ S₁' → DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₁) k = some (.chan e.sid e.role) →
    lookupG G₁ e = some (.branch p bs) → bs.length = procs.length →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh S₁ (updateG G₁ e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
    (∀ lbl P L, procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh S₁ (updateG G₁ e L) P S₁' G₁' W Δ) →
    SEnvDomSubset S₁ S₁' →
    (∀ lbl P L, procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      DisjointS S₂ S₁ →
      DisjointS S₂ S₁' →
      DisjointG (updateG G₁ e L) G₂ →
      HasTypeProcPreOut Ssh (S₁ ++ S₂) (updateG G₁ e L ++ G₂) P
        (S₁' ++ S₂) (G₁' ++ G₂) W Δ) →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.branch k procs)
      (S₁' ++ S₂) (G₁' ++ G₂) W Δ := by
  -- Assemble the framed branch rule.
  intro hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hDom ih
  have hk' := lookupSEnv_all_frame_right (S₂:=S₂) hk
  have hG' := lookupG_append_left (G₂:=G₂) hG
  have hProcs' := frame_right_branch_pre (S₁:=S₁) (S₂:=S₂) (G₁:=G₁) (G₂:=G₂)
    hDisjS hG hProcs
  have hOut' := frame_right_branch_out (S₁:=S₁) (S₂:=S₂) (G₁:=G₁) (G₂:=G₂)
    hDisjS hDisjS' hDisjG hG hOut ih
  have hDom' := SEnvDomSubset_append_left_of_domsubset (S₁:=S₁') (S₁':=S₁) (S₂:=S₂) hDom
  exact HasTypeProcPreOut.branch hk' hG' hLen hLbl hProcs' hOut' hDom'

/-- Right framing for assign_new. -/
private theorem frame_right_assign_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T : ValType} :
    DisjointS S₂ (updateSEnv S₁ x T) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₁ x = none →
    HasTypeVal G₁ v T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.assign x v)
      (updateSEnv S₁ x T ++ S₂) (G₁ ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Right framing preserves the new assignment.
  intro hDisjS' hSsh hSown hv
  have hv' := HasTypeVal_frame_right (G₁:=G₁) (G₂:=G₂) hv
  have hx2 : lookupSEnv (updateSEnv S₁ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hNone2 : lookupSEnv S₂ x = none := lookupSEnv_none_of_disjoint_right hDisjS' hx2
  have hSown' : lookupSEnv (S₁ ++ S₂) x = none := by
    have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hSown
    simpa [hEq] using hNone2
  have hUpdS := updateSEnv_append_left_any (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T)
  simpa [hUpdS] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hSsh hSown' hv')

/-- Right framing for assign_old. -/
private theorem frame_right_assign_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T T' : ValType} :
    lookupSEnv Ssh x = none →
    lookupSEnv S₁ x = some T' →
    HasTypeVal G₁ v T →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.assign x v)
      (updateSEnv S₁ x T ++ S₂) (G₁ ++ G₂) [x] ∅ := by
  -- Right framing keeps the existing binding for x.
  intro hSsh hSown hv
  have hv' := HasTypeVal_frame_right (G₁:=G₁) (G₂:=G₂) hv
  have hSown' : lookupSEnv (S₁ ++ S₂) x = some T' := lookupSEnv_append_left hSown
  have hUpdS := updateSEnv_append_left_any (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T)
  simpa [hUpdS] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂) hSsh hSown' hv')

/-- Right framing for par: frame only the right component. -/
private theorem frame_right_par
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P Q : Process} {Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit S₁ G₁) :
    Sfin = S₁' ++ S₂' → Gfin = G₁' ++ G₂' → Wfin = W₁ ++ W₂ → Δfin = Δ₁ ++ Δ₂ →
    DisjointG split.G1 split.G2 → DisjointS split.S1 split.S2 → DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' → DisjointS S₁' S₂' → DisjointW W₁ W₂ → DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh split.S1 split.G1 P S₁' G₁' W₁ Δ₁ →
    HasTypeProcPreOut Ssh split.S2 split.G2 Q S₂' G₂' W₂ Δ₂ →
    DisjointS S₂ S₁ → DisjointS S₂ Sfin → DisjointG G₁ G₂ →
    (DisjointS S₂ split.S2 → DisjointS S₂ S₂' → DisjointG split.G2 G₂ →
      HasTypeProcPreOut Ssh (split.S2 ++ S₂) (split.G2 ++ G₂) Q (S₂' ++ S₂) (G₂' ++ G₂) W₂ Δ₂) →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.par P Q) (Sfin ++ S₂) (Gfin ++ G₂) Wfin Δfin := by
  -- Frame the right branch and rebuild the split.
  intro hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ hDisjS_frame hDisjS_frame' hDisjG_frame ihQ
  have hDisjG2 : DisjointG split.G2 G₂ := by
    have hSym := DisjointG_symm hDisjG_frame
    have hTmp : DisjointG G₂ split.G2 :=
      DisjointG_of_append_right (by simpa [split.hG] using hSym)
    exact DisjointG_symm hTmp
  have hQ' := ihQ (DisjointS_of_append_right (by simpa [split.hS] using hDisjS_frame))
    (DisjointS_of_append_right (by simpa [hSfin] using hDisjS_frame'))
    hDisjG2
  let splitOut : ParSplit (S₁ ++ S₂) (G₁ ++ G₂) :=
    { S1 := split.S1, S2 := split.S2 ++ S₂, G1 := split.G1, G2 := split.G2 ++ G₂,
      hS := by simpa [split.hS, SEnv_append_assoc], hG := by simp [split.hG, List.append_assoc] }
  have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
    have hDisjG1 : DisjointG G₂ split.G1 := by
      have hSym := DisjointG_symm hDisjG_frame
      have hTmp : DisjointG G₂ split.G1 :=
        DisjointG_of_append_left (by simpa [split.hG] using hSym)
      exact hTmp
    have hDisjG2 : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
    have hTmp := DisjointG_append_left hDisjG2 hDisjG1
    simpa [splitOut] using DisjointG_symm hTmp
  have hDisjSOut : DisjointS splitOut.S1 splitOut.S2 := by
    have hDisjS1 := DisjointS_of_append_left (by simpa [split.hS] using hDisjS_frame)
    have hDisjS1' := DisjointS_symm hDisjS1
    simpa [splitOut] using DisjointS_append_right hDisjS hDisjS1'
  have hDisjS_left_out : DisjointS S₁' splitOut.S2 := by
    have hDisjS1' := DisjointS_symm (DisjointS_of_append_left (by simpa [hSfin] using hDisjS_frame')); simpa [splitOut] using DisjointS_append_right hDisjS_left hDisjS1'
  have hDisjS_right_out : DisjointS splitOut.S1 (S₂' ++ S₂) := by
    have hDisjS1 := DisjointS_of_append_left (by simpa [split.hS] using hDisjS_frame)
    have hDisjS1' := DisjointS_symm hDisjS1
    simpa [splitOut] using DisjointS_append_right hDisjS_right hDisjS1'
  have hDisjS_out : DisjointS S₁' (S₂' ++ S₂) := by
    have hDisjS1' := DisjointS_symm (DisjointS_of_append_left (by simpa [hSfin] using hDisjS_frame')); simpa using DisjointS_append_right hDisjS' hDisjS1'
  simpa [hSfin, hGfin, hW, hΔ, SEnv_append_assoc, List.append_assoc] using
    (HasTypeProcPreOut.par splitOut rfl rfl rfl rfl hDisjGOut hDisjSOut hDisjS_left_out hDisjS_right_out hDisjS_out hDisjW hDisjΔ hP hQ')

/-- Pre-out typing is stable under framing on the right of S/G. -/
theorem HasTypeProcPreOut_frame_right
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₁' : SEnv} {G₁' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₂ S₁ →
    DisjointS S₂ S₁' →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ := by
  -- Induct on the pre-out derivation and apply right-frame lemmas.
  intro hDisjS hDisjS' hDisjG hPre
  induction hPre with
  | skip => exact frame_right_skip
  | send hk hG hx => exact frame_right_send hk hG hx
  | recv_new hk hG hSsh hSown => exact frame_right_recv_new hDisjS' hk hG hSsh hSown
  | recv_old hk hG hSsh hSown => exact frame_right_recv_old hk hG hSsh hSown
  | select hk hG hFind => exact frame_right_select hk hG hFind
  | branch hk hG hLen hLbl hProcs hOut hDom ih =>
      exact frame_right_branch hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hDom ih
  | seq hP hQ ihP ihQ =>
      have hDomQ := HasTypeProcPreOut_domsubset hQ
      have hDisjS_mid := DisjointS_of_domsubset_right hDomQ hDisjS'
      have hSubG := SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG_mid := DisjointG_of_subset_left hSubG hDisjG
      exact HasTypeProcPreOut.seq (ihP hDisjS hDisjS_mid hDisjG) (ihQ hDisjS_mid hDisjS' hDisjG_mid)
  | par split hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ ihP ihQ =>
      exact frame_right_par split hSfin hGfin hW hΔ hDisjG0 hDisjS0 hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ
        hP hQ hDisjS hDisjS' hDisjG ihQ
  | assign_new hSsh hSown hv => exact frame_right_assign_new hDisjS' hSsh hSown hv
  | assign_old hSsh hSown hv => exact frame_right_assign_old hSsh hSown hv

/-! ### Pre-Update Typing Preservation -/

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
private theorem HasTypeProcPreOut_preserved_sub
    {Gstore G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hTS hPre
  induction hTS generalizing Sfin Gfin W Δ with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      cases hPre with
      | send hk' hG' hx' =>
          rename_i e' q' T' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.send q' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.send q' T' L') := by
            simpa [hEq] using hGPre
          have hEqSend : (LocalType.send target T L) = (LocalType.send q' T' L') := by
            have : some (LocalType.send target T L) = some (LocalType.send q' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hL : L' = L := by
            cases hEqSend
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout
            simpa [hEq, hL] using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      cases hPre with
      | recv_new hk' hG' hSsh hSown =>
          rename_i e' p' T' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.recv p' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.recv p' T' L') := by
            simpa [hEq] using hGPre
          have hEqRecv : (LocalType.recv source T L) = (LocalType.recv p' T' L') := by
            have : some (LocalType.recv source T L) = some (LocalType.recv p' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hT : T' = T := by
            cases hEqRecv
            rfl
          have hL : L' = L := by
            cases hEqRecv
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout; subst hSout
            simpa [hEq, hT, hL] using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | recv_old hk' hG' hSsh hSown =>
          rename_i e' p' T' L' Told
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.recv p' T' L') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.recv p' T' L') := by
            simpa [hEq] using hGPre
          have hEqRecv : (LocalType.recv source T L) = (LocalType.recv p' T' L') := by
            have : some (LocalType.recv source T L) = some (LocalType.recv p' T' L') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hT : T' = T := by
            cases hEqRecv
            rfl
          have hL : L' = L := by
            cases hEqRecv
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout; subst hSout
            simpa [hEq, hT, hL] using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      cases hPre with
      | select hk' hG' hFind' =>
          rename_i e' q' bs' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.select q' bs') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.select q' bs') := by
            simpa [hEq] using hGPre
          have hEqSel : (LocalType.select target bs) = (LocalType.select q' bs') := by
            have : some (LocalType.select target bs) = some (LocalType.select q' bs') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hBs : bs' = bs := by
            cases hEqSel
            rfl
          have hFind'' : bs.find? (fun b => b.1 == ℓ) = some (ℓ, L') := by
            simpa [hBs] using hFind'
          have hEqFind : some (ℓ, L) = some (ℓ, L') := by
            simpa [hFind] using hFind''
          have hL : L' = L := by
            cases hEqFind
            rfl
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hGout
            simpa [hEq, hL] using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      cases hPre with
      | branch hk' hG' hLen hLabels hPreAll hPost hDom =>
          rename_i e' p' bs'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) := by
            simpa using hk'
          have hGPre : lookupG G e' = some (.branch p' bs') := by
            simpa using hG'
          -- Align endpoints via store typing.
          have hkTyped : HasTypeVal Gstore (.chan e) (.chan e'.sid e'.role) :=
            hStore k (.chan e) (.chan e'.sid e'.role) hk hkPre
          have hEq : e = e' := by
            have hValEq : (Value.chan e) = Value.chan ⟨e'.sid, e'.role⟩ := by
              simpa using (HasTypeVal_chan_inv hkTyped)
            cases e
            cases e'
            cases hValEq
            rfl
          have hG'' : lookupG G e = some (.branch p' bs') := by
            simpa [hEq] using hGPre
          have hEqBr : (LocalType.branch source bs) = (LocalType.branch p' bs') := by
            have : some (LocalType.branch source bs) = some (LocalType.branch p' bs') := by
              simpa [hG] using hG''
            exact Option.some.inj this
          have hBs : bs' = bs := by
            cases hEqBr
            rfl
          have hFindT' : bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) := by
            simpa [hBs] using hFindT
          have hPre' := hPost _ _ _ hFindP hFindT'
          subst hGout
          refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
          simpa [hEq] using hPre'
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v T Sown' store'
      cases hPre with
      | assign_new hSsh hSown hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=G))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | assign_old hSsh hSown hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=updateSEnv Sown x T) (G:=G))
          · intro x hx; cases hx
          · intro x T hx; cases hx
  | seq_step hTS ih =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStore hP
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.seq hP' hQ
          · exact FootprintSubset_append_left hSubW
          · exact SEnvDomSubset_append_left_of_domsubset hSubΔ
  | seq_skip =>
      cases hPre with
      | seq hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          · exact hQ
          · simpa using (FootprintSubset_refl (W:=W₂))
          · simpa using (SEnvDomSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  | par_left split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁'
      have hStore' : StoreTyped Gstore (SEnvAll Ssh (split.S1 ++ split.S2)) store := by
        simpa [split.hS] using hStore
      have hStoreL : StoreTyped Gstore (SEnvAll Ssh split.S1) store := by
        have hStore'' : StoreTyped Gstore ((Ssh ++ split.S1) ++ split.S2) store := by
          intro x v T hStoreX hLookup
          have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=split.S1) (S₃:=split.S2) (x:=x)
          have hLookup' : lookupSEnv (Ssh ++ (split.S1 ++ split.S2)) x = some T := by
            simpa [hEq] using hLookup
          exact hStore' x v T hStoreX (by simpa [SEnvAll] using hLookup')
        exact StoreTyped_split_left (S₁:=Ssh ++ split.S1) (S₂:=split.S2) hStore''
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStoreL hP
          let splitOut : ParSplit (S₁' ++ split.S2) (G₁' ++ split.G2) :=
            { S1 := S₁', S2 := split.S2, G1 := G₁', G2 := split.G2, hS := rfl, hG := rfl }
          have hSubG : SessionsOf G₁' ⊆ SessionsOf split.G1 := SessionsOf_subset_of_TypedStep hTS
          have hDisjGOut : DisjointG G₁' split.G2 := DisjointG_of_subset_left hSubG hDisjG
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomP := HasTypeProcPreOut_domsubset hP'
          have hDisjS_left0 : DisjointS S₁' split.S2 :=
            DisjointS_of_domsubset_left hDomP hDisjS_left
          have hDisjS_left' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_left0
          have hDisjS_in_out := DisjointS_of_domsubset_left hDomP hDisjS''
          have hDisjW' : DisjointW W₁' W₂ :=
            DisjointW_of_subset_left hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁' Δ₂ :=
            DisjointS_of_domsubset_left hSubΔ hDisjΔ
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_left' hDisjS_left hDisjS_in_out hDisjS'' hDisjW' hDisjΔ' hP' hQ
          · simpa [hW] using (FootprintSubset_append_left hSubW)
          · simpa [hΔ] using (SEnvDomSubset_append_left_of_domsubset hSubΔ)
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂'
      have hStoreR : StoreTyped Gstore (SEnvAll Ssh split.S2) store := by
        intro x v T hStoreX hLookup
        have hLookupS : lookupSEnv (Ssh ++ split.S2) x = some T := by
          simpa [SEnvAll] using hLookup
        have hLookup' : lookupSEnv (Ssh ++ split.S1 ++ split.S2) x = some T := by
          by_cases hSh : lookupSEnv Ssh x = none
          · have hRight : lookupSEnv split.S2 x = some T := by
              simpa [lookupSEnv_append_right (S₁:=Ssh) (S₂:=split.S2) hSh] using hLookupS
            have hS1 : lookupSEnv split.S1 x = none := by
              by_contra hSome
              cases hSome' : lookupSEnv split.S1 x with
              | none => exact (hSome hSome').elim
              | some T₁ =>
                  exact (hDisjS x T₁ T (by simpa using hSome') hRight).elim
            have hNone : lookupSEnv (Ssh ++ split.S1) x = none := by
              simpa [lookupSEnv_append_right (S₁:=Ssh) (S₂:=split.S1) hSh] using hS1
            have hAppend : lookupSEnv ((Ssh ++ split.S1) ++ split.S2) x = lookupSEnv split.S2 x :=
              lookupSEnv_append_right (S₁:=Ssh ++ split.S1) (S₂:=split.S2) hNone
            have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=split.S1) (S₃:=split.S2) (x:=x)
            have hAppend' : lookupSEnv (Ssh ++ (split.S1 ++ split.S2)) x = lookupSEnv split.S2 x := by
              simpa [hEq] using hAppend
            simpa [hRight] using hAppend'
          · cases hSh' : lookupSEnv Ssh x with
            | none => exact (hSh hSh').elim
            | some Tsh =>
                have hLeft0 : lookupSEnv (Ssh ++ split.S2) x = some Tsh := by
                  simpa [SEnvAll] using
                    (lookupSEnv_append_left (S₁:=Ssh) (S₂:=split.S2) hSh')
                have hLeft1 : lookupSEnv (Ssh ++ (split.S1 ++ split.S2)) x = some Tsh := by
                  simpa [SEnvAll] using
                    (lookupSEnv_append_left (S₁:=Ssh) (S₂:=split.S1 ++ split.S2) hSh')
                have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=split.S1) (S₃:=split.S2) (x:=x)
                have hLeft : lookupSEnv (Ssh ++ split.S1 ++ split.S2) x = some Tsh := by
                  simpa [hEq.symm] using hLeft1
                have hEq : T = Tsh := by
                  have : some T = some Tsh := by
                    simpa [hLookupS] using hLeft0
                  exact Option.some.inj this
                simpa [hEq] using hLeft
        exact hStore x v T hStoreX (by
          have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=split.S1) (S₃:=split.S2) (x:=x)
          have hLookup'' : lookupSEnv (Ssh ++ (split.S1 ++ split.S2)) x = some T := by
            simpa [hEq] using hLookup'
          simpa [SEnvAll, split.hS] using hLookup'')
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i W₁ W₂ Δ₁ Δ₂
          obtain ⟨W₂', Δ₂', hQ', hSubW, hSubΔ⟩ := ih hStoreR hQ
          let splitOut : ParSplit (split.S1 ++ S₂') (split.G1 ++ G₂') :=
            { S1 := split.S1, S2 := S₂', G1 := split.G1, G2 := G₂', hS := rfl, hG := rfl }
          have hSubG : SessionsOf G₂' ⊆ SessionsOf split.G2 := SessionsOf_subset_of_TypedStep hTS
          have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
          have hDisjG' : DisjointG G₂' split.G1 := DisjointG_of_subset_left hSubG hDisjGsym
          have hDisjGOut : DisjointG split.G1 G₂' := DisjointG_symm hDisjG'
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomQ := HasTypeProcPreOut_domsubset hQ'
          have hDisjS_right0 : DisjointS split.S1 S₂' :=
            DisjointS_of_domsubset_right hDomQ hDisjS_right
          have hDisjS_right' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_right0
          have hDisjS_left_in := DisjointS_of_domsubset_right hDomQ hDisjS''
          have hDisjW' : DisjointW W₁ W₂' :=
            DisjointW_of_subset_right hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁ Δ₂' :=
            DisjointS_of_domsubset_right hSubΔ hDisjΔ
          refine ⟨W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_right' hDisjS_left_in hDisjS_right hDisjS'' hDisjW' hDisjΔ' hP hQ'
          · simpa [hW] using (FootprintSubset_append_right_of_subset hSubW)
          · simpa [hΔ] using (SEnvDomSubset_append_right_of_domsubset hSubΔ)
  | par_skip_left =>
      cases hPre with
      | par split hSfin hGfin hW hΔ hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hP
          have hQframe :=
            HasTypeProcPreOut_frame_left hDisjS' hDisjS_right hDisjG' hQ
          refine ⟨W₂, Δ₂, ?_, ?_, ?_⟩
          · simpa [split.hS, split.hG, hSfin, hGfin] using hQframe
          · simpa [hW] using (FootprintSubset_refl)
          · simpa [hΔ] using (SEnvDomSubset_append_right (S₁:=∅) (S₂:=Δ₂))
  | par_skip_right =>
      cases hPre with
      | par split hSfin hGfin hW hΔ hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hP hQ =>
          rename_i W₁ W₂ Δ₁ Δ₂
          cases hQ
          have hDisjS_left_symm : DisjointS split.S2 split.S1 := DisjointS_symm hDisjS'
          have hDisjS_out_symm := DisjointS_symm hDisjS_left
          have hPframe :=
            HasTypeProcPreOut_frame_right hDisjS_left_symm hDisjS_out_symm hDisjG' hP
          refine ⟨W₁, Δ₁, ?_, ?_, ?_⟩
          · simpa [split.hS, split.hG, hSfin, hGfin] using hPframe
          · simpa [hW] using (FootprintSubset_refl)
          · simpa [hΔ] using (SEnvDomSubset_append_left (S₁:=Δ₁) (S₂:=∅))

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
theorem HasTypeProcPreOut_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped G (SEnvAll Ssh Sown) store →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' := by
  intro hStore hTS hPre
  obtain ⟨W', Δ', hPre', _, _⟩ := HasTypeProcPreOut_preserved_sub hStore hTS hPre
  exact ⟨W', Δ', hPre'⟩


end
