
import Protocol.Typing.Preservation.CoherenceAndDisjointnessFrames

/-! # Store Typing Core Lemmas

Core rewriting and monotonicity lemmas for `StoreTyped` and
`StoreTypedStrong`, enabling GEnv and SEnv substitution. -/

/-
The Problem. Store typing `StoreTyped G S store` depends on both GEnv
(for channel value typing) and SEnv (for variable type lookup). When
either environment is rewritten or weakened, we need to show store
typing is preserved.

Solution Structure. Prove `StoreTyped_rewriteG` for GEnv substitution,
`StoreTyped_rewriteS` for SEnv substitution, and monotonicity variants.
Extend to `StoreTypedStrong` which includes same-domain conditions.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- GEnv Rewriting

lemma StoreTyped_rewriteG {G G' : GEnv} {S : SEnv} {store : VarStore}
    (hMono : ∀ e L, lookupG G e = some L → lookupG G' e = some L) :
    StoreTyped G S store → StoreTyped G' S store := by
  intro hStore x v T hStr hS
  exact HasTypeVal_mono G G' v T (hStore x v T hStr hS) hMono

lemma StoreTyped_rewriteS {G : GEnv} {S S' : SEnv} {store : VarStore}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTyped G S store → StoreTyped G S' store := by
  intro hStore x v T hStr hS'
  have hS : lookupSEnv S x = some T := by
    simpa [hEq x] using hS'
  exact hStore x v T hStr hS

lemma StoreTyped_weakenS {G : GEnv} {S S' : SEnv} {store : VarStore}
    (hMono : ∀ x T, lookupSEnv S' x = some T → lookupSEnv S x = some T) :
    StoreTyped G S store → StoreTyped G S' store := by
  intro hStore x v T hStr hS'
  exact hStore x v T hStr (hMono x T hS')

lemma StoreTypedStrong_rewriteG {G G' : GEnv} {S : SEnv} {store : VarStore}
    (hEq : ∀ e, lookupG G e = lookupG G' e) :
    StoreTypedStrong G S store → StoreTypedStrong G' S store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    exact hStore.sameDomain x
  ·
    apply StoreTyped_rewriteG (G:=G) (G':=G') (S:=S)
      (hMono:=by
        intro e L hLookup
        simpa [hEq e] using hLookup)
    exact hStore.typeCorr

lemma StoreTypedStrong_rewriteS {G : GEnv} {S S' : SEnv} {store : VarStore}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTypedStrong G S store → StoreTypedStrong G S' store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    simpa [hEq x] using hStore.sameDomain x
  ·
    apply StoreTyped_rewriteS (G:=G) (S:=S) (S':=S') hEq
    exact hStore.typeCorr

-- Disjoint-Lookup Commutation

lemma lookupG_none_of_disjoint_early {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {e : Endpoint} {L : LocalType} (hLookup : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
/- ## Structured Block 2 -/
  by_cases hNone : lookupG G₁ e = none
  · exact hNone
  · cases hSome : lookupG G₁ e with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hSid₁ : e.sid ∈ SessionsOf G₁ := ⟨e, L₁, hSome, rfl⟩
        have hSid₂ : e.sid ∈ SessionsOf G₂ := ⟨e, L, hLookup, rfl⟩
        have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid₁, hSid₂⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
        have : e.sid ∈ (∅ : Set SessionId) := by
          have hInter' := hInter
          simp [hEmpty] at hInter'
        exact this.elim

-- # Lookup Commutation on Disjoint Prefixes

lemma lookupG_comm_of_disjoint_early {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookupG_none_of_disjoint_early (G₁:=G₂) (G₂:=G₁) (DisjointG_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookupG_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simpa [hA, hB, hRight, hLeft]

-- # Left-Swap Lift Through Outer Append

lemma lookupG_swap_left {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG ((G₁ ++ G₂) ++ G₃) e = lookupG ((G₂ ++ G₁) ++ G₃) e := by
  intro e
  cases hLeft : lookupG (G₁ ++ G₂) e with
  | some L =>
      have hA := lookupG_append_left (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) (L:=L) hLeft
      have hSwap := lookupG_comm_of_disjoint_early hDisj e
      have hLeft' : lookupG (G₂ ++ G₁) e = some L := by
        simpa [hSwap] using hLeft
      have hB := lookupG_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) (L:=L) hLeft'
      have hA' : lookupG (G₁ ++ (G₂ ++ G₃)) e = some L := by
        simpa [List.append_assoc] using hA
      have hB' : lookupG (G₂ ++ (G₁ ++ G₃)) e = some L := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']
  | none =>
      have hA := lookupG_append_right (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) hLeft
      have hSwap := lookupG_comm_of_disjoint_early hDisj e
/- ## Structured Block 3 -/
      have hNone : lookupG (G₂ ++ G₁) e = none := by
        simpa [hSwap] using hLeft
      have hB := lookupG_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) hNone
      have hA' : lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG G₃ e := by
        simpa [List.append_assoc] using hA
      have hB' : lookupG (G₂ ++ (G₁ ++ G₃)) e = lookupG G₃ e := by
        simpa [List.append_assoc] using hB
      simpa [hA', hB']

-- Swap Rewrites for Strong Store Typing

lemma StoreTypedStrong_swap_G_left {G₁ G₂ G₃ : GEnv} {S : SEnv} {store : VarStore}
    (hDisj : DisjointG G₁ G₂) :
    StoreTypedStrong ((G₁ ++ G₂) ++ G₃) S store →
    StoreTypedStrong ((G₂ ++ G₁) ++ G₃) S store := by
  intro hStore
  apply StoreTypedStrong_rewriteG (G:=((G₁ ++ G₂) ++ G₃)) (G':=((G₂ ++ G₁) ++ G₃))
    (by
      intro e
      exact lookupG_swap_left (G₁:=G₁) (G₂:=G₂) (G₃:=G₃) hDisj e)
  exact hStore

lemma StoreTypedStrong_swap_S_left_prefix
    {Ssh S₁ S₂ S₃ : SEnv} {G : GEnv} {store : VarStore}
    (hDisj : DisjointS S₁ S₂) :
    StoreTypedStrong G (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) store →
    StoreTypedStrong G (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) store := by
  intro hStore
  apply StoreTypedStrong_rewriteS
    (S:=SEnvAll Ssh ((S₁ ++ S₂) ++ S₃))
    (S':=SEnvAll Ssh (S₂ ++ (S₁ ++ S₃)))
    (by
      intro x
      exact lookupSEnv_swap_left_prefix (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x)
  exact hStore

-- Store-Domain Update Lemmas

theorem lookupSEnv_none_of_disjoint_update
    {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (hDisj : DisjointS (updateSEnv S₁ x T) S₂) :
    lookupSEnv S₂ x = none := by
  -- Otherwise disjointness is violated at x.
  by_contra hSome
  cases hS2 : lookupSEnv S₂ x with
  | none => exact (hSome hS2).elim
  | some T₂ =>
      have hS1 : lookupSEnv (updateSEnv S₁ x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=S₁) (x:=x) (T:=T))
      exact (hDisj x T T₂ hS1 hS2).elim

/-- Same-domain is preserved by a matching SEnv/store update. -/
theorem StoreTypedStrong_sameDomain_update
    {S : SEnv} {store : VarStore} {x : Var} {T : ValType} {v : Value}
    (hDom : ∀ y, (lookupSEnv S y).isSome ↔ (lookupStr store y).isSome) :
    ∀ y, (lookupSEnv (updateSEnv S x T) y).isSome ↔
      (lookupStr (updateStr store x v) y).isSome := by
  -- Update is pointwise: only x changes.
  intro y
  by_cases hEq : y = x
  · subst hEq
/- ## Structured Block 4 -/
    simp [lookupSEnv_update_eq, lookupStr_update_eq]
  · have hS : lookupSEnv (updateSEnv S x T) y = lookupSEnv S y := by
      simpa using (lookupSEnv_update_neq (env:=S) (x:=x) (y:=y) (T:=T) (Ne.symm hEq))
    have hStr : lookupStr (updateStr store x v) y = lookupStr store y := by
      simpa using (lookupStr_update_neq store x y v (Ne.symm hEq))
    simpa [hS, hStr] using hDom y

-- Assignment/Receive Update Corollaries

/-- StoreTypedStrong is stable under updating G at a single endpoint. -/
theorem StoreTypedStrong_updateG
    {G : GEnv} {S : SEnv} {store : VarStore} {e : Endpoint} {L : LocalType}
    (hStore : StoreTypedStrong G S store) :
    StoreTypedStrong (updateG G e L) S store := by
  -- Same-domain is unchanged; typing weakens along updateG.
  refine ⟨?_, ?_⟩
  · intro x
    simpa using hStore.sameDomain x
  ·
    have hST : StoreTyped (updateG G e L) S store :=
      StoreTyped_send_preserved (G:=G) (S:=S) (store:=store) (e:=e) (L:=L) hStore.typeCorr
    exact hST

/-- Assignment preserves StoreTypedStrong on shared+owned SEnv. -/
theorem StoreTypedStrong_assign_update
    {G : GEnv} {Ssh Sown : SEnv} {store : VarStore} {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong G (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_assign_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store)
      (x:=x) (T:=T) (v:=v) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped G (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_assign_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (x:=x) (v:=v) (T:=T)
        hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

/-- Receive preserves StoreTypedStrong on shared+owned SEnv. -/
theorem StoreTypedStrong_recv_update
    {G : GEnv} {Ssh Sown : SEnv} {store : VarStore} {e : Endpoint} {L : LocalType}
    {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hNone : lookupSEnv Ssh x = none)
    (hv : HasTypeVal G v T) :
    StoreTypedStrong (updateG G e L) (SEnvAll Ssh (updateSEnv Sown x T)) (updateStr store x v) := by
  -- Same-domain updates pointwise; typing uses StoreTyped_recv_preserved.
  refine ⟨?_, ?_⟩
  ·
    have hDom := StoreTypedStrong_sameDomain_update (S:=SEnvAll Ssh Sown) (store:=store)
      (x:=x) (T:=T) (v:=v) hStore.sameDomain
    simpa [SEnvAll, updateSEnv_append_left hNone] using hDom
  ·
    have hST : StoreTyped (updateG G e L) (updateSEnv (SEnvAll Ssh Sown) x T) (updateStr store x v) :=
      StoreTyped_recv_preserved (G:=G) (S:=SEnvAll Ssh Sown) (store:=store) (e:=e) (L:=L)
        (x:=x) (v:=v) (T:=T) hStore.typeCorr hv
    simpa [SEnvAll, updateSEnv_append_left hNone] using hST

-- UpdateLeft Lookup Equivalence

/-- Updating only `Sown.left` under a fixed shared/right prefix is lookup-equivalent
    to updating the full combined environment at `x`. -/

/- ## Structured Block 5 -/
lemma lookupSEnv_append_erase_ne
    {Sright Srest : SEnv} {x y : Var} (hxy : y ≠ x) :
    lookupSEnv (eraseSEnv Sright x ++ Srest) y =
      lookupSEnv (Sright ++ Srest) y := by
  have hEraseNe : lookupSEnv (eraseSEnv Sright x) y = lookupSEnv Sright y :=
    lookupSEnv_erase_ne (S:=Sright) (x:=x) (y:=y) hxy
  cases hR : lookupSEnv Sright y with
  | some Ty =>
      have hEraseSome : lookupSEnv (eraseSEnv Sright x) y = some Ty := by
        simpa [hR] using hEraseNe
      have hL :=
        lookupSEnv_append_left (S₁:=eraseSEnv Sright x) (S₂:=Srest) (x:=y) (T:=Ty) hEraseSome
      have hRhs :=
        lookupSEnv_append_left (S₁:=Sright) (S₂:=Srest) (x:=y) (T:=Ty) hR
      simpa [hL, hRhs]
  | none =>
      have hEraseNone : lookupSEnv (eraseSEnv Sright x) y = none := by
        simpa [hR] using hEraseNe
      have hL :=
        lookupSEnv_append_right (S₁:=eraseSEnv Sright x) (S₂:=Srest) (x:=y) hEraseNone
      have hRhs :=
        lookupSEnv_append_right (S₁:=Sright) (S₂:=Srest) (x:=y) hR
      simpa [hRhs] using hL

theorem lookupSEnv_updateLeft_frame_eq_updateSEnv
    {Ssh : SEnv} {Sown : OwnedEnv} {S₂ : SEnv} {x : Var} {T : ValType}
    (hNoSh : lookupSEnv Ssh x = none) :
    ∀ y,
      lookupSEnv (SEnvAll Ssh (Sown.updateLeft x T ++ S₂)) y =
      lookupSEnv (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) y := by
  intro y
  by_cases hxy : y = x
  · subst y
    -- # Equal-Variable Case (`y = x`)
    have hPrefixNone : lookupSEnv (Ssh ++ eraseSEnv Sown.right x) x = none := by
      have hAppend := lookupSEnv_append_right (S₁:=Ssh) (S₂:=eraseSEnv Sown.right x) (x:=x) hNoSh
      simpa [lookupSEnv_erase_eq (S:=Sown.right) (x:=x)] using hAppend
    have hTarget : lookupSEnv (SEnvAll Ssh (Sown.updateLeft x T ++ S₂)) x = some T := by
      have hRight :
          lookupSEnv ((Ssh ++ eraseSEnv Sown.right x) ++ (updateSEnv Sown.left x T ++ S₂)) x =
            lookupSEnv (updateSEnv Sown.left x T ++ S₂) x :=
        lookupSEnv_append_right
          (S₁:=Ssh ++ eraseSEnv Sown.right x) (S₂:=updateSEnv Sown.left x T ++ S₂)
          (x:=x) hPrefixNone
      have hUpd : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hInner : lookupSEnv (updateSEnv Sown.left x T ++ S₂) x = some T :=
        lookupSEnv_append_left hUpd
      simpa [SEnvAll, OwnedEnv.updateLeft, List.append_assoc, hInner] using hRight
    have hUpdate : lookupSEnv (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) x = some T := by
      simpa using (lookupSEnv_update_eq (env:=SEnvAll Ssh (Sown ++ S₂)) (x:=x) (T:=T))
    exact hTarget.trans hUpdate.symm
/- ## Structured Block 6 -/
  · have hTargetBase :
      -- # Distinct-Variable Case (`y ≠ x`)
      lookupSEnv (SEnvAll Ssh (Sown.updateLeft x T ++ S₂)) y =
        lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y := by
      have hInner :
          lookupSEnv (SEnvAll (Ssh ++ eraseSEnv Sown.right x) (updateSEnv Sown.left x T ++ S₂)) y =
            lookupSEnv (SEnvAll (Ssh ++ eraseSEnv Sown.right x) (Sown.left ++ S₂)) y :=
        lookupSEnv_SEnvAll_update_neq (Ssh:=Ssh ++ eraseSEnv Sown.right x) (Sown:=Sown.left) (S₂:=S₂)
          (x:=x) (y:=y) (T:=T) hxy
      have hEraseMid :
          lookupSEnv (SEnvAll (Ssh ++ eraseSEnv Sown.right x) (Sown.left ++ S₂)) y =
            lookupSEnv (SEnvAll (Ssh ++ Sown.right) (Sown.left ++ S₂)) y := by
        cases hSh : lookupSEnv Ssh y with
        | some Ty =>
            have hL :
                lookupSEnv (Ssh ++ (eraseSEnv Sown.right x ++ (Sown.left ++ S₂))) y = some Ty :=
              lookupSEnv_append_left (S₁:=Ssh) (S₂:=eraseSEnv Sown.right x ++ (Sown.left ++ S₂))
                (x:=y) (T:=Ty) hSh
            have hR :
                lookupSEnv (Ssh ++ (Sown.right ++ (Sown.left ++ S₂))) y = some Ty :=
              lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.right ++ (Sown.left ++ S₂))
                (x:=y) (T:=Ty) hSh
            simpa [SEnvAll, List.append_assoc] using (hL.trans hR.symm)
        | none =>
            have hSuffix :
                lookupSEnv (eraseSEnv Sown.right x ++ (Sown.left ++ S₂)) y =
                  lookupSEnv (Sown.right ++ (Sown.left ++ S₂)) y :=
              lookupSEnv_append_erase_ne (Sright:=Sown.right) (Srest:=Sown.left ++ S₂) (x:=x) (y:=y) hxy
            have hL :
                lookupSEnv (Ssh ++ (eraseSEnv Sown.right x ++ (Sown.left ++ S₂))) y =
                  lookupSEnv (eraseSEnv Sown.right x ++ (Sown.left ++ S₂)) y :=
              lookupSEnv_append_right (S₁:=Ssh) (S₂:=eraseSEnv Sown.right x ++ (Sown.left ++ S₂))
                (x:=y) hSh
            have hR :
                lookupSEnv (Ssh ++ (Sown.right ++ (Sown.left ++ S₂))) y =
                  lookupSEnv (Sown.right ++ (Sown.left ++ S₂)) y :=
              lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.right ++ (Sown.left ++ S₂))
                (x:=y) hSh
            simpa [SEnvAll, List.append_assoc] using (hL.trans (hSuffix.trans hR.symm))
      simpa [SEnvAll, OwnedEnv.updateLeft, OwnedEnv.frameLeft, List.append_assoc] using hInner.trans hEraseMid
    have hUpdateNe :
        lookupSEnv (updateSEnv (SEnvAll Ssh (Sown ++ S₂)) x T) y =
          lookupSEnv (SEnvAll Ssh (Sown ++ S₂)) y := by
      simpa using
        (lookupSEnv_update_neq (env:=SEnvAll Ssh (Sown ++ S₂)) (x:=x) (y:=y) (T:=T)
          (Ne.symm hxy))
    exact hTargetBase.trans hUpdateNe.symm

-- Left-Frame Endpoint Update Theorems

/-- Frame: send updates G on the left under a right context. -/
theorem StoreTypedStrong_frame_send
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : VarStore}
    {e : Endpoint} {target : Role} {T : ValType} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
/- ## Structured Block 7 -/
    (hG : lookupG G e = some (.send target T L)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.send target T L) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: select updates G on the left under a right context. -/
theorem StoreTypedStrong_frame_select
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : VarStore}
    {e : Endpoint} {target : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.select target bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.select target bs) (L':=L) hG
  simpa [hGrew] using hStore'

/-- Frame: branch updates G on the left under a right context. -/
theorem StoreTypedStrong_frame_branch
    {G G₂ : GEnv} {Ssh Sown S₂ : SEnv} {store : VarStore}
    {e : Endpoint} {source : Role} {bs : List (Label × LocalType)} {L : LocalType}
    (hStore : StoreTypedStrong (G ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store)
    (hG : lookupG G e = some (.branch source bs)) :
    StoreTypedStrong (updateG G e L ++ G₂) (SEnvAll Ssh (Sown ++ S₂)) store := by
  -- Update G on the left; SEnv/store unchanged.
  have hStore' :
      StoreTypedStrong (updateG (G ++ G₂) e L) (SEnvAll Ssh (Sown ++ S₂)) store :=
    StoreTypedStrong_updateG (G:=G ++ G₂) (S:=SEnvAll Ssh (Sown ++ S₂))
      (store:=store) (e:=e) (L:=L) hStore
  have hGrew :
      updateG (G ++ G₂) e L = updateG G e L ++ G₂ :=
    updateG_append_left_hit (G₁:=G) (G₂:=G₂) (e:=e) (L:=.branch source bs) (L':=L) hG
  simpa [hGrew] using hStore'

end
