import Protocol.Environments.Core
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

private theorem lookupSEnv_all_frame_prefix_ofLeft
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (SEnvAll Ssh (S₂ : OwnedEnv)) x = some T →
    lookupSEnv (SEnvAll Ssh { right := S₁, left := S₂ }) x = some T := by
  intro hDisj hLookup
  have hLookup' : lookupSEnv (Ssh ++ S₂) x = some T := by
    simpa [SEnvAll_ofLeft] using hLookup
  have hFrame := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) hDisj hLookup'
  simpa [SEnvAll, List.append_assoc] using hFrame

private theorem lookupSEnv_all_frame_left_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    DisjointS Sframe Sown.left →
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sown.right, left := Sframe ++ Sown.left }) x = some T := by
  intro hDisj hLookup
  have hLookup' : lookupSEnv ((Ssh ++ Sown.right) ++ Sown.left) x = some T := by
    have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=Sown.right) (S₃:=Sown.left) (x:=x)
    simpa [SEnvAll, hEq] using hLookup
  have hFrame :=
    lookupSEnv_all_frame_left (Ssh:=Ssh ++ Sown.right) (S₁:=Sframe) (S₂:=Sown.left) hDisj hLookup'
  have hEq' := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=Sown.right) (S₃:=Sframe ++ Sown.left) (x:=x)
  simpa [SEnvAll, hEq', List.append_assoc] using hFrame

private theorem lookupSEnv_all_frame_right_owned
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sown.right, left := Sown.left ++ Sframe }) x = some T := by
  intro hLookup
  have hLookup' : lookupSEnv (Ssh ++ (Sown.right ++ Sown.left)) x = some T := by
    simpa [SEnvAll] using hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ (Sown.right ++ Sown.left)) (S₂:=Sframe) (x:=x) (T:=T) hLookup'
  simpa [SEnvAll, List.append_assoc] using hLeft

private theorem lookupSEnv_all_frame_right_prefix
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {x : Var} {T : ValType} :
    DisjointS Sframe Sown.right →
    DisjointS Sframe Sown.left →
    lookupSEnv (SEnvAll Ssh Sown) x = some T →
    lookupSEnv (SEnvAll Ssh { right := Sframe ++ Sown.right, left := Sown.left }) x = some T := by
  intro hDisjR hDisjL hLookup
  have hDisj : DisjointS Sframe (Sown.right ++ Sown.left) := by
    intro x T₁ T₂ hL1 hL12
    cases hLr : lookupSEnv Sown.right x with
    | some T₁' =>
        have hEq : T₁' = T₂ := by
          have hLeft := lookupSEnv_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T₁') hLr
          exact Option.some.inj (by simpa [hLeft] using hL12)
        exact hDisjR x T₁ T₁' hL1 (by simpa [hEq] using hLr)
    | none =>
        have hRight := lookupSEnv_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hLr
        have hL2 : lookupSEnv Sown.left x = some T₂ := by
          simpa [hRight] using hL12
        exact hDisjL x T₁ T₂ hL1 hL2
  have hLookup' : lookupSEnv (Ssh ++ (Sown.right ++ Sown.left)) x = some T := by
    simpa [SEnvAll] using hLookup
  have hFrame := lookupSEnv_all_frame_left (Ssh:=Ssh) (S₁:=Sframe) (S₂:=Sown.right ++ Sown.left) hDisj hLookup'
  simpa [SEnvAll, List.append_assoc] using hFrame

private lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (S₁ ++ S₂) x = lookupSEnv (S₂ ++ S₁) x := by
  intro x
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      have hRight : lookupSEnv S₂ x = none :=
        lookupSEnv_none_of_disjoint_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T₁) (DisjointS_symm hDisj) hLeft
      have hA := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁) hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hRight
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      cases hRight : lookupSEnv S₂ x with
      | some T₂ =>
          have hB := lookupSEnv_append_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T₂) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hRight
          simpa [hA, hB, hRight, hLeft]

private lemma lookupSEnv_swap_left {S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv ((S₂ ++ S₁) ++ S₃) x := by
  intro x
  cases hLeft : lookupSEnv (S₁ ++ S₂) x with
  | some T =>
      have hA := lookupSEnv_append_left (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) (T:=T) hLeft
      have hSwap := lookupSEnv_comm_of_disjoint hDisj x
      have hLeft' : lookupSEnv (S₂ ++ S₁) x = some T := by
        simpa [hSwap] using hLeft
      have hB := lookupSEnv_append_left (S₁:=S₂ ++ S₁) (S₂:=S₃) (x:=x) (T:=T) hLeft'
      have hA' : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = some T := by
        simpa [List.append_assoc] using hA
      have hB' : lookupSEnv (S₂ ++ (S₁ ++ S₃)) x = some T := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁ ++ S₂) (S₂:=S₃) (x:=x) hLeft
      have hSwap := lookupSEnv_comm_of_disjoint hDisj x
      have hNone : lookupSEnv (S₂ ++ S₁) x = none := by
        simpa [hSwap] using hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂ ++ S₁) (S₂:=S₃) (x:=x) hNone
      have hA' : lookupSEnv (S₁ ++ (S₂ ++ S₃)) x = lookupSEnv S₃ x := by
        simpa [List.append_assoc] using hA
      have hB' : lookupSEnv (S₂ ++ (S₁ ++ S₃)) x = lookupSEnv S₃ x := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']

private lemma lookupSEnv_swap_left_prefix {Ssh S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) x =
      lookupSEnv (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) x := by
  intro x
  cases hS : lookupSEnv Ssh x with
  | some Ty =>
      have hLeft :=
        lookupSEnv_append_left (S₁:=Ssh) (S₂:=((S₁ ++ S₂) ++ S₃)) (x:=x) (T:=Ty) hS
      have hRight :=
        lookupSEnv_append_left (S₁:=Ssh) (S₂:=(S₂ ++ (S₁ ++ S₃))) (x:=x) (T:=Ty) hS
      have hLeft' : lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x = some Ty := by
        simpa [List.append_assoc] using hLeft
      simpa [SEnvAll, hLeft', hRight]
  | none =>
      have hLeft := lookupSEnv_append_right (S₁:=Ssh) (S₂:=((S₁ ++ S₂) ++ S₃)) (x:=x) hS
      have hRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=(S₂ ++ (S₁ ++ S₃))) (x:=x) hS
      have hLeft' : lookupSEnv ((S₁ ++ S₂) ++ S₃) x = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        simpa using (lookupSEnv_swap_left (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x)
      have hLeft'' : lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x =
          lookupSEnv ((S₁ ++ S₂) ++ S₃) x := by
        simpa [List.append_assoc] using hLeft
      have hRight'' : lookupSEnv (Ssh ++ (S₂ ++ (S₁ ++ S₃))) x =
          lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := by
        simpa [List.append_assoc] using hRight
      calc
        lookupSEnv (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) x
            = lookupSEnv (Ssh ++ (S₁ ++ (S₂ ++ S₃))) x := by
                simp [SEnvAll, List.append_assoc]
        _ = lookupSEnv ((S₁ ++ S₂) ++ S₃) x := hLeft''
        _ = lookupSEnv (S₂ ++ (S₁ ++ S₃)) x := hLeft'
        _ = lookupSEnv (Ssh ++ (S₂ ++ (S₁ ++ S₃))) x := by
                symm; exact hRight''
        _ = lookupSEnv (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) x := by
                simp [SEnvAll]

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
    {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G : GEnv} {k : Var} {procs : List (Label × Process)}
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

theorem HasTypeProcPre_frame_G {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G₂ : GEnv} {P : Process} :
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
    rename_i G k x e p T L
    have hSid : e.sid ∈ SessionsOf G := ⟨e, .recv p T L, hG, rfl⟩
    have hNot : e.sid ∉ SessionsOf G₁ := by
      intro hIn
      have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G := ⟨hIn, hSid⟩
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G = (∅ : Set SessionId) := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have : e.sid ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
    have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
    have hG' : lookupG (G₁ ++ G) e = some (.recv p T L) := by
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
  case par hDisjS hSplit hP hQ ihP ihQ =>
    exact HasTypeProcPre.par hDisjS hSplit (ihP hDisj) (ihQ hDisj)
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

/-- Lift a GEnv lookup across a left frame using disjointness. -/
private theorem lookupG_frame_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
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

/-- Pre-update typing is stable under framing on the left of S/G. -/
theorem HasTypeProcPre_frame_left
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS Sframe Sown.right →
    DisjointS Sframe Sown.left →
  DisjointG G₁ G₂ →
  HasTypeProcPre Ssh Sown G₂ P →
  HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left } (G₁ ++ G₂) P := by
  intro hDisjR hDisjL hDisjG hPre
  induction hPre generalizing G₁ Sframe with
  | skip =>
      exact HasTypeProcPre.skip
  | send hk hG hx =>
      have hk' :=
        lookupSEnv_all_frame_right_prefix (Ssh:=Ssh) (Sframe:=Sframe) hDisjR hDisjL hk
      have hx' :=
        lookupSEnv_all_frame_right_prefix (Ssh:=Ssh) (Sframe:=Sframe) hDisjR hDisjL hx
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.send hk' hG' hx'
  | recv hk hG hSsh =>
      have hk' :=
        lookupSEnv_all_frame_right_prefix (Ssh:=Ssh) (Sframe:=Sframe) hDisjR hDisjL hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.recv hk' hG' hSsh
  | select hk hG hFind =>
      have hk' :=
        lookupSEnv_all_frame_right_prefix (Ssh:=Ssh) (Sframe:=Sframe) hDisjR hDisjL hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.select hk' hG' hFind
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G₂ k procs e p bs
      have hk' :=
        lookupSEnv_all_frame_right_prefix (Ssh:=Ssh) (Sframe:=Sframe) hDisjR hDisjL hk
      have hG' := lookupG_frame_left hDisjG hG
      have hProcs' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left }
              (updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2)
              (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        have hDisj' : DisjointG G₁ (updateG G₂ e (bs.get ⟨i, hi⟩).2) :=
          DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=.branch p bs)
            (L':=(bs.get ⟨i, hi⟩).2) hDisjG hG
        have hPre' := ih i hi hip (Sframe:=Sframe) (G₁:=G₁) hDisjR hDisjL hDisj'
        have hNone : lookupG G₁ e = none := by
          have hDisjSym := DisjointG_symm hDisjG
          exact DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
        have hUpd :
            updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2 =
              G₁ ++ updateG G₂ e (bs.get ⟨i, hi⟩).2 :=
          updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:= (bs.get ⟨i, hi⟩).2) hNone
        have hPre'' :
            HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left }
              (updateG (G₁ ++ G₂) e (bs.get ⟨i, hi⟩).2)
              (procs.get ⟨i, hip⟩).2 := by
          rw [hUpd]
          exact hPre'
        exact hPre''
      exact HasTypeProcPre.branch hk' hG' hLen hLbl hProcs'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisjR hDisjL hDisjG) (ihQ hDisjR hDisjL hDisjG)
  | par hDisjS' hSplit hP hQ ihP ihQ =>
      rename_i Sown G₂ P Q S₁ S₂
      have hDisjS1 : DisjointS Sframe S₁ :=
        DisjointS_of_append_left (S₁:=Sframe) (S₂:=S₁) (S₃:=S₂) (by simpa [hSplit] using hDisjL)
      have hDisjS2 : DisjointS Sframe S₂ :=
        DisjointS_of_append_right (S₁:=Sframe) (S₂:=S₁) (S₃:=S₂) (by simpa [hSplit] using hDisjL)
      have hDisjR1 : DisjointS Sframe (({ right := Sown.right ++ S₂, left := S₁ } : OwnedEnv).right) := by
        simpa using (DisjointS_append_right hDisjR hDisjS2)
      have hDisjR2 : DisjointS Sframe (({ right := Sown.right ++ S₁, left := S₂ } : OwnedEnv).right) := by
        simpa using (DisjointS_append_right hDisjR hDisjS1)
      have hP' := ihP (Sframe:=Sframe) (G₁:=G₁) hDisjR1 hDisjS1 hDisjG
      have hQ' := ihQ (Sframe:=Sframe) (G₁:=G₁) hDisjR2 hDisjS2 hDisjG
      have hP'' :
          HasTypeProcPre Ssh { right := (Sframe ++ Sown.right) ++ S₂, left := S₁ } (G₁ ++ G₂) P := by
        simpa [List.append_assoc] using hP'
      have hQ'' :
          HasTypeProcPre Ssh { right := (Sframe ++ Sown.right) ++ S₁, left := S₂ } (G₁ ++ G₂) Q := by
        simpa [List.append_assoc] using hQ'
      have hSplit' :
          (({ right := Sframe ++ Sown.right, left := Sown.left } : OwnedEnv).left) = S₁ ++ S₂ := by
        simpa [hSplit]
      simpa [hSplit', List.append_assoc] using
        (HasTypeProcPre.par (Sown:={ right := Sframe ++ Sown.right, left := Sown.left })
          hDisjS' hSplit' hP'' hQ'')
  | assign hSsh hv =>
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
    lookupSEnv_append_left (S₁:=Ssh ++ S₁) (S₂:=S₂) (x:=x) (T:=T) (by
      simpa [SEnvAll_ofLeft] using hLookup)
  have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=S₁) (S₃:=S₂) (x:=x)
  simpa [SEnvAll_ofLeft, SEnvAll, hEq] using hLeft

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

/-- Right framing for pre-update typing. -/
private axiom HasTypeProcPre_frame_right
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS Sframe Sown.left →
    HasTypeProcPre Ssh Sown G₁ P →
    HasTypeProcPre Ssh { right := Sown.right, left := Sown.left ++ Sframe } (G₁ ++ G₂) P

/-- Left framing for skip. -/
private theorem frame_left_skip {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) .skip
      { right := S₁, left := S₂ } (G₁ ++ G₂) [] ∅ := by
  -- Skip leaves environments unchanged.
  simpa using
    (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂))

/-- Left framing for send. -/
private theorem frame_left_send
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {q : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.send q T L) →
    lookupSEnv (SEnvAll Ssh S₂) x = some T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.send k x)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hx
  have hk' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hk
  have hx' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hx
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂) hk' hG' hx')

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
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to show x is not in the left frame.
  intro hDisjS hDisjS' hDisjG hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := hx1
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft, hUpdG] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hRight hLeft)

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
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] ∅ := by
  -- Old recv: x already in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hk hG hSsh hSown
  have hk' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := hx1
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft, hUpdG] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hRight hLeft)

/-- Left framing for select. -/
private theorem frame_left_select
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {l : Label} {e : Endpoint}
    {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvAll Ssh S₂) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.select q bs) →
    bs.find? (fun b => b.1 == l) = some (l, L) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.select k l)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hFind
  have hk' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hFind)

/-- Frame-left helper for branch pre-typing. -/
private theorem frame_left_pre_updateG
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L0 →
    HasTypeProcPre Ssh S₂ (updateG G₂ e L) P →
    HasTypeProcPre Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L) P := by
  -- Frame pre-typing and rewrite the update on G.
  intro hDisjS hDisjG hG hPre
  have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
    DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hDisjG hG
  have hDisjR : DisjointS S₁ ([] : SEnv) := by
    simpa using (DisjointS_symm (DisjointS_left_empty S₁))
  have hPre' := HasTypeProcPre_frame_left (Sframe:=S₁) (Sown:=(S₂ : OwnedEnv))
    (G₁:=G₁) (G₂:=updateG G₂ e L) hDisjR hDisjS hDisjG' hPre
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
      HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) P
        { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.branch k procs)
      { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
  -- Frame each branch using the provided IH and rebuild the constructor.
  intro hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hDom ih
  have hk' := lookupSEnv_all_frame_prefix_ofLeft hDisjS hk
  have hG' := lookupG_frame_left hDisjG hG
  have hProcs' :
      ∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh { right := S₁, left := S₂ }
          (updateG (G₁ ++ G₂) e (bs.get ⟨j, hj⟩).2)
          (procs.get ⟨j, hjp⟩).2 := by
    intro j hj hjp
    exact frame_left_pre_updateG hDisjS hDisjG hG (hProcs j hj hjp)
  have hOut' :
      ∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L)
          P { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
    intro lbl P L hP hB
    have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
      DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=.branch p bs) (L':=L) hDisjG hG
    have hPre' := ih lbl P L hP hB hDisjS hDisjS' hDisjG'
    have hDisjSym := DisjointG_symm hDisjG
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
    have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
    simpa [hUpd] using hPre'
  exact HasTypeProcPreOut.branch hk' hG' hLen hLbl hProcs' hOut' hDom

/-- Left framing for assign_new. -/
private theorem frame_left_assign_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T : ValType} :
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to keep x absent from the left frame.
  intro hDisjS' hDisjG hSsh hSown hv
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hRight hLeft hv')

/-- Left framing for assign_old. -/
private theorem frame_left_assign_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] ∅ := by
  -- Old assignment: x is in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hSsh hSown hv
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hRight hLeft hv')

/-- Left framing for par: frame only the left component. -/
private axiom frame_left_par
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
      HasTypeProcPreOut Ssh { right := S₁, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁, left := S₁' } (G₁ ++ G₁') W₁ Δ₁) :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.par P Q)
      { right := S₁, left := Sfin } (G₁ ++ Gfin) Wfin Δfin


/-- Pre-out typing is stable under framing on the left of S/G. -/
axiom HasTypeProcPreOut_frame_left
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) P
      { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ

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
  have hRight : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).right x = none := by
    simpa [OwnedEnv.ofLeft] using (lookupSEnv_empty (x:=x))
  have hLeft : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).left x = none := by
    simpa [OwnedEnv.ofLeft] using hSown'
  simpa [hUpdS, hUpdG, OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂)
      hk' hG' hSsh hRight hLeft)

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
  have hRight : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).right x = none := by
    simpa [OwnedEnv.ofLeft] using (lookupSEnv_empty (x:=x))
  have hLeft : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).left x = some T' := by
    simpa [OwnedEnv.ofLeft] using hSown'
  simpa [hUpdS, hUpdG, OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂)
      hk' hG' hSsh hRight hLeft)

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
  have hRight : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).right x = none := by
    simpa [OwnedEnv.ofLeft] using (lookupSEnv_empty (x:=x))
  have hLeft : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).left x = none := by
    simpa [OwnedEnv.ofLeft] using hSown'
  simpa [hUpdS, OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂)
      hSsh hRight hLeft hv')

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
  have hRight : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).right x = none := by
    simpa [OwnedEnv.ofLeft] using (lookupSEnv_empty (x:=x))
  have hLeft : lookupSEnv (OwnedEnv.ofLeft (S₁ ++ S₂)).left x = some T' := by
    simpa [OwnedEnv.ofLeft] using hSown'
  simpa [hUpdS, OwnedEnv.updateLeft] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:=S₁ ++ S₂) (G:=G₁ ++ G₂)
      hSsh hRight hLeft hv')

/-- Right framing for par: frame only the right component. -/
private axiom frame_right_par
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
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) (.par P Q) (Sfin ++ S₂) (Gfin ++ G₂) Wfin Δfin

/-- Pre-out typing is stable under framing on the right of S/G. -/
axiom HasTypeProcPreOut_frame_right
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P : Process}
    {S₁' : SEnv} {G₁' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₂ S₁ →
    DisjointS S₂ S₁' →
    DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ

private axiom HasTypeProcPreOut_par_skip_left
    {Ssh Sown G Q Sfin Gfin Wfin Δfin} :
    HasTypeProcPreOut Ssh Sown G (.par .skip Q) Sfin Gfin Wfin Δfin →
    HasTypeProcPreOut Ssh Sown G Q Sfin Gfin Wfin Δfin

private axiom HasTypeProcPreOut_par_skip_right
    {Ssh Sown G P Sfin Gfin Wfin Δfin} :
    HasTypeProcPreOut Ssh Sown G (.par P .skip) Sfin Gfin Wfin Δfin →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin Wfin Δfin

private axiom HasTypeProcPreOut_reframe_right
    {Ssh R R' L : SEnv} {G : GEnv} {P : Process}
    {L' : SEnv} {G' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := R, left := L } G P { right := R, left := L' } G' W Δ →
    HasTypeProcPreOut Ssh { right := R', left := L } G P { right := R', left := L' } G' W Δ

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
      | recv_new hk' hG' hSsh hSownR hSownL =>
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
              (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G e L))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | recv_old hk' hG' hSsh hSownR hSownL =>
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
              (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G e L))
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
      | assign_new hSsh hSownR hSownL hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=G))
          · intro x hx; cases hx
          · intro x T hx; cases hx
      | assign_old hSsh hSownR hSownL hv' =>
          have hT := HasTypeVal_unique hv' hv
          cases hT
          refine ⟨[], ∅, ?_, ?_, ?_⟩
          · subst hSout
            simpa using (HasTypeProcPreOut.skip
              (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=G))
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
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step
      have hStore' : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right, left := split.S1 ++ split.S2 }) store := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      have hStoreL : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
        intro x v T hStoreX hLookup
        have hLookup' :
            lookupSEnv (Ssh ++ (Sown.right ++ (split.S2 ++ split.S1))) x = some T := by
          simpa [SEnvAll, List.append_assoc] using hLookup
        have hSwap :=
          lookupSEnv_swap_left_prefix (Ssh:=Ssh ++ Sown.right) (S₁:=split.S2) (S₂:=split.S1) (S₃:=(∅ : SEnv))
            (DisjointS_symm hDisjS) x
        have hSwap' :
            lookupSEnv (Ssh ++ (Sown.right ++ (split.S2 ++ split.S1))) x =
              lookupSEnv (Ssh ++ (Sown.right ++ (split.S1 ++ split.S2))) x := by
          simpa [SEnvAll, List.append_assoc] using hSwap
        have hLookup'' :
            lookupSEnv (Ssh ++ (Sown.right ++ (split.S1 ++ split.S2))) x = some T := by
          simpa [hSwap'] using hLookup'
        exact hStore' x v T hStoreX (by
          simpa [SEnvAll, List.append_assoc] using hLookup'')
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
          subst hS1
          subst hS2
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStoreL hP
          let splitOut : ParSplit (S₁_step ++ split.S2) (G₁_step ++ split.G2) :=
            { S1 := S₁_step, S2 := split.S2, G1 := G₁_step, G2 := split.G2, hS := rfl, hG := rfl }
          have hSubG_step : SessionsOf G₁_step ⊆ SessionsOf split.G1 :=
            SessionsOf_subset_of_TypedStep hTS
          have hDisjGOut : DisjointG G₁_step split.G2 := DisjointG_of_subset_left hSubG_step hDisjG
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomP := HasTypeProcPreOut_domsubset hP'
          have hDisjS_left0 : DisjointS S₁_step split.S2 :=
            DisjointS_of_domsubset_left hDomP hDisjS_left
          have hDisjS_left' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_left0
          have hDisjS_in_out0 : DisjointS S₁_step S₂_fin :=
            DisjointS_of_domsubset_left hDomP hDisjS''
          have hDisjS_in_out : DisjointS splitOut.S1 S₂_fin := by
            simpa [splitOut] using hDisjS_in_out0
          have hQ' :
              HasTypeProcPreOut Ssh { right := Sown.right ++ S₁_step, left := split.S2 } split.G2 Q
                { right := Sown.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ :=
            HasTypeProcPreOut_reframe_right
              (R:=Sown.right ++ split.S1) (R':=Sown.right ++ S₁_step) (L:=split.S2) (L':=S₂_fin) (G:=split.G2) (P:=Q) hQ
          have hDisjW' : DisjointW W₁' W₂ :=
            DisjointW_of_subset_left hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁' Δ₂ :=
            DisjointS_of_domsubset_left hSubΔ hDisjΔ
          refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_left' hDisjS_left hDisjS_in_out hDisjS'' hDisjW' hDisjΔ' rfl rfl hP' hQ'
          · simpa [hW] using (FootprintSubset_append_left hSubW)
          · simpa [hΔ] using (SEnvDomSubset_append_left_of_domsubset hSubΔ)
  | par_right split hTS hDisjG hDisjD hDisjS hConsL hConsR ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step
      have hStoreR : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      cases hPre with
      | par split' hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hEq : split' = split := ParSplit.unique split' split
          cases hEq
          rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
          subst hS1
          subst hS2
          obtain ⟨W₂', Δ₂', hQ', hSubW, hSubΔ⟩ := ih hStoreR hQ
          let splitOut : ParSplit (split.S1 ++ S₂_step) (split.G1 ++ G₂_step) :=
            { S1 := split.S1, S2 := S₂_step, G1 := split.G1, G2 := G₂_step, hS := rfl, hG := rfl }
          have hSubG_step : SessionsOf G₂_step ⊆ SessionsOf split.G2 :=
            SessionsOf_subset_of_TypedStep hTS
          have hDisjGsym : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
          have hDisjG' : DisjointG G₂_step split.G1 := DisjointG_of_subset_left hSubG_step hDisjGsym
          have hDisjGOut : DisjointG split.G1 G₂_step := DisjointG_symm hDisjG'
          have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
            simpa [splitOut] using hDisjGOut
          have hDomQ := HasTypeProcPreOut_domsubset hQ'
          have hDisjS_right0 : DisjointS split.S1 S₂_step :=
            DisjointS_of_domsubset_right hDomQ hDisjS_right
          have hDisjS_right' : DisjointS splitOut.S1 splitOut.S2 := by
            simpa [splitOut] using hDisjS_right0
          have hDisjS_left_in : DisjointS S₁_fin S₂_step :=
            DisjointS_of_domsubset_right hDomQ hDisjS''
          have hP_reframe :
              HasTypeProcPreOut Ssh { right := Sown.right ++ S₂_step, left := split.S1 } split.G1 P
                { right := Sown.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ :=
            HasTypeProcPreOut_reframe_right
              (R:=Sown.right ++ split.S2) (R':=Sown.right ++ S₂_step) (L:=split.S1) (L':=S₁_fin) (G:=split.G1) (P:=P) hP
          have hDisjW' : DisjointW W₁ W₂' :=
            DisjointW_of_subset_right hSubW hDisjW
          have hDisjΔ' : DisjointS Δ₁ Δ₂' :=
            DisjointS_of_domsubset_right hSubΔ hDisjΔ
          refine ⟨W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, ?_, ?_⟩
          · exact HasTypeProcPreOut.par splitOut hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_right' hDisjS_left_in hDisjS_right hDisjS'' hDisjW' hDisjΔ' rfl rfl hP_reframe hQ'
          · simpa [hW] using (FootprintSubset_append_right_of_subset hSubW)
          · simpa [hΔ] using (SEnvDomSubset_append_right_of_domsubset hSubΔ)
  | par_skip_left =>
      have hQ := HasTypeProcPreOut_par_skip_left hPre
      refine ⟨W, Δ, hQ, FootprintSubset_refl, SEnvDomSubset_refl⟩
  | par_skip_right =>
      have hP := HasTypeProcPreOut_par_skip_right hPre
      refine ⟨W, Δ, hP, FootprintSubset_refl, SEnvDomSubset_refl⟩

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
