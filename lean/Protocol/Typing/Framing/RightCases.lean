import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.PreUpdateHelpers

/-
Right-frame step cases for pre-out preservation. These lemmas discharge each
TypedStep constructor when the right side of G is preserved.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ### Right-Frame Step Cases -/
/-- Helper: send case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_send
    {Gstore G₁ G₂ G G' Ssh Sown store k x e target T L G₂' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.send target T L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₂ (.send k x) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the send pre-out rule and rewrite the right update.
  intro hStore hDisj hEq hEq' hk hG hGout hPre
  cases hPre with
  | send hk' hG' hx' =>
      rename_i e' q' T' L'
      have hEqE : e = e' := endpoint_eq_of_store hStore hk hk'
      have hG₂e : lookupG G₂ e = some (.send q' T' L') := by
        simpa [hEqE] using hG'
      have hL : L' = L :=
        send_localtype_eq_right (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e)
          (target:=target) (q:=q') (T:=T) (T':=T') (L:=L) (L':=L')
          hDisj hEq hG₂e hG
      have hG₂' : G₂' = updateG G₂ e L :=
        updateG_right_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₂':=G₂') (e:=e)
          (L:=L) (L0:=.send q' T' L') hDisj hEq hEq' hG₂e hGout.symm
      refine ⟨[], ∅, ?_, ?_, ?_⟩
      · simpa [hG₂', hL, hEqE] using
          (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G₂ e L))
      · intro x hx0; cases hx0
      · intro x T hx0; cases hx0

/-- Helper: recv-new case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_recv_new
    {Gstore G₁ G₂ G G' Ssh Sown store k x e source T L G₂' Sown' Sfin Gfin W Δ}
    {e' : Endpoint} {p' : Role} {T' : ValType} {L' : LocalType} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = OwnedEnv.updateLeft Sown x T →
    Sfin = OwnedEnv.updateLeft Sown x T' →
    Gfin = updateG G₂ e' L' →
    lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) →
    lookupG G₂ e' = some (.recv p' T' L') →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use the recv-new pre-out premises and rewrite the right update.
  intro hStore hDisj hEq hEq' hk hG hGout hSout hSfin hGfin hk' hG'
  have hEqE : e = e' := endpoint_eq_of_store hStore hk hk'
  have hG₂e : lookupG G₂ e = some (.recv p' T' L') := by
    simpa [hEqE] using hG'
  have hTL : T' = T ∧ L' = L :=
    recv_types_eq_right (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
      (T:=T) (T':=T') (L:=L) (L':=L') hDisj hEq hG₂e hG
  have hG₂' : G₂' = updateG G₂ e L :=
    updateG_right_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₂':=G₂') (e:=e)
      (L:=L) (L0:=.recv p' T' L') hDisj hEq hEq' hG₂e hGout.symm
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₂', hTL.1, hTL.2, hEqE, hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G₂ e L))
  · intro x hx0; cases hx0
  · intro x T hx0; cases hx0

/-- Helper: recv-old case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_recv_old
    {Gstore G₁ G₂ G G' Ssh Sown store k x e source T L G₂' Sown' Sfin Gfin W Δ}
    {e' : Endpoint} {p' : Role} {T' : ValType} {L' : LocalType} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = OwnedEnv.updateLeft Sown x T →
    Sfin = OwnedEnv.updateLeft Sown x T' →
    Gfin = updateG G₂ e' L' →
    lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) →
    lookupG G₂ e' = some (.recv p' T' L') →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use the recv-old pre-out premises and rewrite the right update.
  intro hStore hDisj hEq hEq' hk hG hGout hSout hSfin hGfin hk' hG'
  have hEqE : e = e' := endpoint_eq_of_store hStore hk hk'
  have hG₂e : lookupG G₂ e = some (.recv p' T' L') := by
    simpa [hEqE] using hG'
  have hTL : T' = T ∧ L' = L :=
    recv_types_eq_right (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
      (T:=T) (T':=T') (L:=L) (L':=L') hDisj hEq hG₂e hG
  have hG₂' : G₂' = updateG G₂ e L :=
    updateG_right_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₂':=G₂') (e:=e)
      (L:=L) (L0:=.recv p' T' L') hDisj hEq hEq' hG₂e hGout.symm
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₂', hTL.1, hTL.2, hEqE, hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G₂ e L))
  · intro x hx0; cases hx0
  · intro x T hx0; cases hx0

/-- Helper: select case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_select
    {Gstore G₁ G₂ G G' Ssh Sown store k ℓ e target bs L G₂' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₂ (.select k ℓ) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the select pre-out rule and rewrite the right update.
  intro hStore hDisj hEq hEq' hk hG hFind hGout hPre
  cases hPre with
  | select hk' hG' hFind' =>
      rename_i e' q' bs' L'
      have hEqE : e = e' := endpoint_eq_of_store hStore hk hk'
      have hG₂e : lookupG G₂ e = some (.select q' bs') := by
        simpa [hEqE] using hG'
      have hBs : bs' = bs :=
        select_branches_eq_right (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (target:=target) (q:=q')
          (bs:=bs) (bs':=bs') hDisj hEq hG₂e hG
      have hL : L' = L :=
        select_label_eq (bs:=bs) (bs':=bs') (ℓ:=ℓ) (L:=L) (L':=L') hBs hFind' hFind
      have hG₂' : G₂' = updateG G₂ e L :=
        updateG_right_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₂':=G₂') (e:=e)
          (L:=L) (L0:=.select q' bs') hDisj hEq hEq' hG₂e hGout.symm
      refine ⟨[], ∅, ?_, ?_, ?_⟩
      · simpa [hG₂', hL, hEqE] using
          (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G₂ e L))
      · intro x hx0; cases hx0
      · intro x T hx0; cases hx0

/-- Helper: branch case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_branch
    {Gstore G₁ G₂ G G' Ssh Sown store k procs e source bs ℓ P L G₂' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G' = G₁ ++ G₂' →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.branch source bs) →
    procs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₂ (.branch k procs) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₂' P Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the branch pre-out rule and rewrite the right update.
  intro hStore hDisj hEq hEq' hk hG hFindP hFindT hGout hPre
  cases hPre with
  | branch hk' hG' hLen hLabels hPreAll hPost hDom =>
      rename_i e' p' bs'
      have hEqE : e = e' := endpoint_eq_of_store hStore hk hk'
      have hG₂e : lookupG G₂ e = some (.branch p' bs') := by
        simpa [hEqE] using hG'
      have hBs : bs' = bs :=
        branch_branches_eq_right (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
          (bs:=bs) (bs':=bs') hDisj hEq hG₂e hG
      have hFindT' : bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) :=
        branch_find_eq (bs:=bs) (bs':=bs') (ℓ:=ℓ) (L:=L) hBs hFindT
      have hPre' := hPost _ _ _ hFindP hFindT'
      have hG₂' : G₂' = updateG G₂ e L :=
        updateG_right_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₂':=G₂') (e:=e)
          (L:=L) (L0:=.branch p' bs') hDisj hEq hEq' hG₂e hGout.symm
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      simpa [hG₂', hEqE] using hPre'

/-- Helper: assign-new case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_assign_new
    {G₁ G₂ G Ssh Sown x v T_step Sown' G₂' Sfin Gfin W Δ} {T_pre : ValType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G = G₁ ++ G₂' →
    HasTypeVal G v T_step →
    Sown' = OwnedEnv.updateLeft Sown x T_step →
    Sfin = OwnedEnv.updateLeft Sown x T_pre →
    Gfin = G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv Sown.right x = none →
    lookupSEnv Sown.left x = none →
    HasTypeVal G₂ v T_pre →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use typing uniqueness to align the assigned type and cancel the frame.
  intro hDisj hEq hEq' hv hSout hSfin hGfin hSsh hSownR hSownL hv'
  have hv'' : HasTypeVal G v T_pre := by
    -- Strengthen the typing to the framed global environment.
    refine HasTypeVal_mono G₂ G v T_pre hv' ?_
    intro e L hLookup
    have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hLookup
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    have hLookup' : lookupG (G₁ ++ G₂) e = some L := by
      simpa [hEqG] using hLookup
    simpa [hEq] using hLookup'
  have hT := HasTypeVal_unique hv'' hv
  cases hT
  have hEqG : G₁ ++ G₂' = G₁ ++ G₂ := by
    have hEqG0 : G₁ ++ G₂' = G := by
      simpa using hEq'.symm
    simpa [hEq] using hEqG0
  have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₂', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T_step) (G:=G₂))
  · intro x hx; cases hx
  · intro x T hx; cases hx

/-- Helper: assign-old case for the right-frame preservation lemma. -/
lemma preserved_sub_right_frame_assign_old
    {G₁ G₂ G Ssh Sown x v T_step Sown' G₂' Sfin Gfin W Δ} {T_pre T_old : ValType} :
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G = G₁ ++ G₂' →
    HasTypeVal G v T_step →
    Sown' = OwnedEnv.updateLeft Sown x T_step →
    Sfin = OwnedEnv.updateLeft Sown x T_pre →
    Gfin = G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv Sown.right x = none →
    lookupSEnv Sown.left x = some T_old →
    HasTypeVal G₂ v T_pre →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₂' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use typing uniqueness to align the assigned type and cancel the frame.
  intro hDisj hEq hEq' hv hSout hSfin hGfin hSsh hSownR hSownL hv'
  have hv'' : HasTypeVal G v T_pre := by
    -- Strengthen the typing to the framed global environment.
    refine HasTypeVal_mono G₂ G v T_pre hv' ?_
    intro e L hLookup
    have hNone : lookupG G₁ e = none := lookupG_none_of_disjoint hDisj hLookup
    have hEqG := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    have hLookup' : lookupG (G₁ ++ G₂) e = some L := by
      simpa [hEqG] using hLookup
    simpa [hEq] using hLookup'
  have hT := HasTypeVal_unique hv'' hv
  cases hT
  have hEqG : G₁ ++ G₂' = G₁ ++ G₂ := by
    have hEqG0 : G₁ ++ G₂' = G := by
      simpa using hEq'.symm
    simpa [hEq] using hEqG0
  have hG₂' : G₂' = G₂ := append_right_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₂', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T_step) (G:=G₂))
  · intro x hx; cases hx
  · intro x T hx; cases hx

