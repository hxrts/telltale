import Protocol.Typing.Progress.Helpers

/-! # Framing Inversions for Progress

Inversion lemmas relating visible SEnv lookups to full SEnvAll lookups,
enabling progress proofs to extract store values from typing judgments. -/

/-
The Problem. Progress proofs need to extract concrete values from the
store based on typing. Typing uses `SEnvVisible` but store typing uses
`SEnvAll`. We need inversion lemmas relating these.

Solution Structure. Prove `lookupSEnv_all_of_visible_prog` showing that
visible lookup implies full lookup under disjointness. Use this to
bridge typing judgments to store access in progress proofs.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Visible to Full Lookup -/

lemma lookupSEnv_all_of_visible_prog
    {Ssh : SEnv} {Sown : OwnedEnv} {x : Var} {T : ValType}
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hVis : lookupSEnv (Ssh ++ Sown.left) x = some T) :
    lookupSEnv (SEnvAll Ssh Sown) x = some T := by
  cases hSh : lookupSEnv Ssh x with
  | some Tsh =>
      have hEqT : Tsh = T := by
        have hShVis : lookupSEnv (Ssh ++ Sown.left) x = some Tsh :=
          lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.left) (x:=x) (T:=Tsh) hSh
        exact Option.some.inj (by simpa [hVis] using hShVis.symm)
      have hOwnNone : lookupSEnv (Sown : SEnv) x = none := by
        exact lookupSEnv_none_of_disjoint_left
          (S₁:=(Sown : SEnv)) (S₂:=Ssh) (x:=x) (T:=Tsh)
          (DisjointS_symm hDisjShAll) hSh
      have hRightNone : lookupSEnv Sown.right x = none := by
        cases hR : lookupSEnv Sown.right x with
        | none => exact rfl
        | some Tr =>
            have hOwnSome : lookupSEnv (Sown : SEnv) x = some Tr := by
              simpa [OwnedEnv.all] using
                (lookupSEnv_append_left (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tr) hR)
            have hOwnNone' : lookupSEnv (Sown.right ++ Sown.left) x = none := by
              simpa [OwnedEnv.all] using hOwnNone
            have hContra : False := by
              simpa [OwnedEnv.all, hOwnNone'] using hOwnSome
            cases hContra
      have hPrefixSh : lookupSEnv (Ssh ++ Sown.right) x = some Tsh := by
        have hPrefix := lookupSEnv_append_left (S₁:=Ssh) (S₂:=Sown.right) (x:=x) (T:=Tsh) hSh
        simpa [hRightNone] using hPrefix
      have hAllSh :
          lookupSEnv ((Ssh ++ Sown.right) ++ Sown.left) x = some Tsh :=
        lookupSEnv_append_left (S₁:=Ssh ++ Sown.right) (S₂:=Sown.left) (x:=x) (T:=Tsh) hPrefixSh
      simpa [SEnvAll, List.append_assoc, hEqT] using hAllSh
  | none =>
      have hLeftSome : lookupSEnv Sown.left x = some T := by
        have hVisRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=Sown.left) (x:=x) hSh
        simpa [hVisRight] using hVis
      have hRightNone : lookupSEnv Sown.right x = none := by
        exact lookupSEnv_none_of_disjoint_left
          (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) (T:=T)
          hOwnDisj hLeftSome
      have hOwnSome : lookupSEnv (Sown : SEnv) x = some T := by
        have hOwnRight := lookupSEnv_append_right (S₁:=Sown.right) (S₂:=Sown.left) (x:=x) hRightNone
        simpa [hOwnRight] using hLeftSome
      have hAll :
          lookupSEnv (SEnvAll Ssh Sown) x = some T := by
        have hAllRight := lookupSEnv_append_right (S₁:=Ssh) (S₂:=(Sown : SEnv)) (x:=x) hSh
        calc
          lookupSEnv (SEnvAll Ssh Sown) x = lookupSEnv (Sown : SEnv) x := by
            simpa [SEnvAll_all] using hAllRight
          _ = some T := hOwnSome
      exact hAll

lemma store_lookup_of_visible_lookup
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {x : Var} {T : ValType}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hVis : lookupSEnv (Ssh ++ Sown.left) x = some T) :
    ∃ v, lookupStr store x = some v ∧ HasTypeVal G v T := by
  have hStoreVis : StoreTypedStrongVisible G Ssh Sown store :=
    StoreTypedStrongVisible_of_allStrong (G:=G) (Ssh:=Ssh) (Sown:=Sown) (store:=store)
      hStore hDisjShAll hOwnDisj
  simpa [SEnvVisible] using
    (store_lookup_of_visible_lookup_strongVisible (G:=G) (Ssh:=Ssh) (Sown:=Sown)
      (store:=store) (x:=x) (T:=T) hStoreVis hVis)

lemma DisjointS_append_right {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₃ →
    DisjointS S₁ (S₂ ++ S₃) := by
  intro hDisj hDisj'
  have hLeft : DisjointS S₂ S₁ := DisjointS_symm hDisj
  have hRight : DisjointS S₃ S₁ := DisjointS_symm hDisj'
  have hAppend : DisjointS (S₂ ++ S₃) S₁ :=
    DisjointS_append_left hLeft hRight
  exact DisjointS_symm hAppend

lemma DisjointS_owned_right {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.right := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.right (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_left (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_owned_left {S₁ : SEnv} {Sown : OwnedEnv} :
    DisjointS S₁ (Sown : SEnv) →
    DisjointS S₁ Sown.left := by
  intro hDisj
  have hSub : SEnvDomSubset Sown.left (Sown : SEnv) := by
    simpa [OwnedEnv.all] using
      (SEnvDomSubset_append_right (S₁:=Sown.right) (S₂:=Sown.left))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_split_left {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₁ := by
  intro hDisj
  have hSub : SEnvDomSubset S₁ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_left (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_split_right {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh (S₁ ++ S₂) → DisjointS Ssh S₂ := by
  intro hDisj
  have hSub : SEnvDomSubset S₂ (S₁ ++ S₂) := by
    simpa using (SEnvDomSubset_append_right (S₁:=S₁) (S₂:=S₂))
  exact DisjointS_of_domsubset_right hSub hDisj

lemma DisjointS_split_from_owned_left
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv}
    (split : ParSplit Sown.left G) :
    DisjointS Ssh (Sown : SEnv) →
    DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 := by
  intro hDisj
  have hLeftAll : DisjointS Ssh (split.S1 ++ split.S2) := by
    simpa [split.hS] using (DisjointS_owned_left (Sown:=Sown) hDisj)
  exact ⟨DisjointS_split_left hLeftAll, DisjointS_split_right hLeftAll⟩

lemma DisjointS_owned_repack
    {Ssh : SEnv} {Sright Sleft Smid : SEnv} :
    DisjointS Ssh Sright →
    DisjointS Ssh Sleft →
    DisjointS Ssh Smid →
    DisjointS Ssh ({ right := Sright ++ Smid, left := Sleft } : OwnedEnv) := by
  intro hRight hLeft hMid
  have hRight' : DisjointS Ssh (Sright ++ Smid) :=
    DisjointS_append_right hRight hMid
  have hAll : DisjointS Ssh ((Sright ++ Smid) ++ Sleft) :=
    DisjointS_append_right hRight' hLeft
  simpa [OwnedEnv.all, List.append_assoc] using hAll

lemma OwnedDisjoint_sub_left
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR1 : DisjointS Sown.right split.S1 := DisjointS_split_left hOwnLeftAll
  have hS2S1 : DisjointS split.S2 split.S1 := DisjointS_symm hDisjS
  have hAll : DisjointS (Sown.right ++ split.S2) split.S1 :=
    DisjointS_append_left hR1 hS2S1
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

lemma OwnedDisjoint_sub_right
    {Sown : OwnedEnv} {G : GEnv} (split : ParSplit Sown.left G) :
    OwnedDisjoint Sown →
    DisjointS split.S1 split.S2 →
    OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
  intro hOwn hDisjS
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwn
  have hR2 : DisjointS Sown.right split.S2 := DisjointS_split_right hOwnLeftAll
  have hS1S2 : DisjointS split.S1 split.S2 := hDisjS
  have hAll : DisjointS (Sown.right ++ split.S1) split.S2 :=
    DisjointS_append_left hR2 hS1S2
  simpa [OwnedDisjoint, OwnedEnv.all] using hAll

lemma channel_endpoint_eq_of_store_visible
    {G : GEnv} {Ssh : SEnv} {Sown : OwnedEnv} {store : VarStore}
    {k : Var} {e e' : Endpoint}
    (hStore : StoreTypedStrong G (SEnvAll Ssh Sown) store)
    (hDisjShAll : DisjointS Ssh (Sown : SEnv))
    (hOwnDisj : OwnedDisjoint Sown)
    (hk : lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role))
    (hkStr : lookupStr store k = some (Value.chan e')) :
    e' = e := by
  obtain ⟨vk, hkStr', hkTyped⟩ :=
    store_lookup_of_visible_lookup hStore hDisjShAll hOwnDisj hk
  have hkChan : vk = Value.chan e := HasTypeVal_chan_inv hkTyped
  have hkStr'' : lookupStr store k = some (Value.chan e) := by
    simpa [hkChan] using hkStr'
  have hEqOpt : some (Value.chan e') = some (Value.chan e) := by
    simpa [hkStr] using hkStr''
  have hEq : (Value.chan e') = (Value.chan e) := Option.some.inj hEqOpt
  cases hEq
  rfl

lemma lookupSEnv_comm_of_disjoint {S₁ S₂ : SEnv} (hDisj : DisjointS S₁ S₂) :
    ∀ x, lookupSEnv (S₁ ++ S₂) x = lookupSEnv (S₂ ++ S₁) x := by
  intro x
  cases hLeft : lookupSEnv S₁ x with
  | some T =>
      have hNone : lookupSEnv S₂ x = none :=
        lookupSEnv_none_of_disjoint_left (S₁:=S₂) (S₂:=S₁) (DisjointS_symm hDisj) hLeft
      have hA := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T) hLeft
      have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hNone
      simpa [hA, hB, hLeft]
  | none =>
      have hA := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      cases hRight : lookupSEnv S₂ x with
      | some T =>
          have hB := lookupSEnv_append_left (S₁:=S₂) (S₂:=S₁) (x:=x) (T:=T) hRight
          simpa [hA, hB, hRight]
      | none =>
          have hB := lookupSEnv_append_right (S₁:=S₂) (S₂:=S₁) (x:=x) hRight
          simpa [hA, hB, hRight, hLeft]

lemma lookupSEnv_swap_left {S₁ S₂ S₃ : SEnv} (hDisj : DisjointS S₁ S₂) :
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

lemma StoreTypedStrong_rewriteS {G : GEnv} {S S' : SEnv} {store : VarStore}
    (hEq : ∀ x, lookupSEnv S x = lookupSEnv S' x) :
    StoreTypedStrong G S store → StoreTypedStrong G S' store := by
  intro hStore
  refine ⟨?_, ?_⟩
  · intro x
    simpa [hEq x] using hStore.sameDomain x
  ·
    intro x v T hStr hS'
    have hS : lookupSEnv S x = some T := by
      simpa [hEq x] using hS'
    exact hStore.typeCorr x v T hStr hS

lemma StoreTypedStrong_swap_S_left_prefix
    {G : GEnv} {Ssh S₁ S₂ S₃ : SEnv} {store : VarStore}
    (hDisj : DisjointS S₁ S₂) :
    StoreTypedStrong G (SEnvAll Ssh ((S₁ ++ S₂) ++ S₃)) store →
    StoreTypedStrong G (SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) store := by
  intro hStore
  apply StoreTypedStrong_rewriteS (S:=SEnvAll Ssh ((S₁ ++ S₂) ++ S₃))
    (S':=SEnvAll Ssh (S₂ ++ (S₁ ++ S₃))) (store:=store)
  · intro x
    exact lookupSEnv_swap_left_prefix (Ssh:=Ssh) (S₁:=S₁) (S₂:=S₂) (S₃:=S₃) hDisj x
  · exact hStore

/-! ## GEnv Framing for Pre-Out Typing -/

lemma HasTypeProcPreOut_send_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.send k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (T : ValType) (L : LocalType),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.send q T L) := by
  intro h
  cases h with
  | send hk hG hx => exact ⟨_, _, _, _, hk, hG⟩

lemma HasTypeProcPreOut_recv_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (T : ValType) (L : LocalType),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.recv p T L) := by
  intro h
  cases h with
  | recv_new hk hG hNoSh hNoOwnL => exact ⟨_, _, _, _, hk, hG⟩
  | recv_old hk hG hNoSh hOwn => exact ⟨_, _, _, _, hk, hG⟩

lemma HasTypeProcPreOut_select_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {l : Label}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.select k l) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (q : Role) (bs : List (Label × LocalType)),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.select q bs) := by
  intro h
  cases h with
  | select hk hG hbs => exact ⟨_, _, _, hk, hG⟩

lemma HasTypeProcPreOut_branch_inv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k : Var} {procs : List (Label × Process)}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G (.branch k procs) Sfin Gfin W Δ →
    ∃ (e : Endpoint) (p : Role) (bs : List (Label × LocalType)),
      lookupSEnv (Ssh ++ Sown.left) k = some (ValType.chan e.sid e.role) ∧
      lookupG G e = some (.branch p bs) := by
  intro h
  cases h with
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight => exact ⟨_, _, _, hk, hG⟩

lemma updateG_full_eq_updateG_mid
    {Gfull Gleft Gmid Gright : GEnv} {e : Endpoint} {L L' : LocalType} {G' : GEnv} :
    Gfull = Gleft ++ Gmid ++ Gright →
    DisjointG Gleft Gmid →
    lookupG Gmid e = some L →
    G' = updateG Gfull e L' →
    G' = Gleft ++ updateG Gmid e L' ++ Gright := by
  intro hGfull hDisjL hG hGout
  have hNoneLeft : lookupG Gleft e = none :=
    DisjointG_lookup_left (G₁:=Gmid) (G₂:=Gleft) (DisjointG_symm hDisjL) hG
  have hLookupMid : lookupG (Gleft ++ Gmid) e = some L := by
    have hEq' := lookupG_append_right (G₁:=Gleft) (G₂:=Gmid) (e:=e) hNoneLeft
    simpa [hEq'] using hG
  have hUpdRight :=
    updateG_append_left_hit (G₁:=Gleft ++ Gmid) (G₂:=Gright) (e:=e) (L':=L') hLookupMid
  have hUpdLeft :=
    updateG_append_left (G₁:=Gleft) (G₂:=Gmid) (e:=e) (L:=L') hNoneLeft
  have hGout' : G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := by
    simpa [hGfull, List.append_assoc] using hGout
  calc
    G' = updateG ((Gleft ++ Gmid) ++ Gright) e L' := hGout'
    _ = updateG (Gleft ++ Gmid) e L' ++ Gright := hUpdRight
    _ = Gleft ++ updateG Gmid e L' ++ Gright := by
      simp [hUpdLeft, List.append_assoc]

lemma TypedStep_preserves_frames_send
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.send k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases HasTypeProcPreOut_send_inv hOut with ⟨eOut, qOut, TOut, LOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

lemma TypedStep_preserves_frames_recv
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k x : Var} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.recv k x) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases HasTypeProcPreOut_recv_inv hOut with ⟨eOut, pOut, TOut, LOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

lemma TypedStep_preserves_frames_select
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {ℓ : Label} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.select k ℓ) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases HasTypeProcPreOut_select_inv hOut with ⟨eOut, qOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

lemma TypedStep_preserves_frames_branch
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {store : VarStore}
    {k : Var} {procs : List (Label × Process)} {eStep : Endpoint} {Lstep : LocalType}
    {G' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    (hGfull : Gfull = Gleft ++ Gmid ++ Gright) →
    (hDisjL : DisjointG Gleft Gmid) →
    (hStore : StoreTypedStrong Gfull (SEnvAll Ssh Sown) store) →
    (hDisjShAll : DisjointS Ssh (Sown : SEnv)) →
    (hOwnDisj : OwnedDisjoint Sown) →
    (hOut : HasTypeProcPreOut Ssh Sown Gmid (.branch k procs) Sfin Gfin W Δ) →
    (hkStr : lookupStr store k = some (.chan eStep)) →
    (hGout : G' = updateG Gfull eStep Lstep) →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hStore hDisjShAll hOwnDisj hOut hkStr hGout
  rcases HasTypeProcPreOut_branch_inv hOut with ⟨eOut, pOut, bsOut, hk, hG⟩
  have hEq : eStep = eOut :=
    channel_endpoint_eq_of_store_visible (hStore:=hStore) (k:=k) (e:=eOut) (e':=eStep)
      hDisjShAll hOwnDisj hk hkStr
  subst hEq
  refine ⟨updateG Gmid eStep Lstep, ?_⟩
  exact updateG_full_eq_updateG_mid hGfull hDisjL hG hGout

-- Use HasTypeProcPreOut_frame_G_right/left from Protocol.Typing.Framing.


end
