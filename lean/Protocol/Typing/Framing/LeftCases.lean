import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.PreUpdateHelpers

/-! # Typing Framing: Left Cases

Left-frame step cases for pre-out preservation.
-/

/-
The Problem. When proving preservation, we need to show that framed typing
contexts are maintained after steps. The left-frame case handles steps
that affect only the left portion of a split environment.

Solution Structure. We prove case lemmas for each TypedStep constructor:
1. `preserved_sub_left_frame_send`: send case
2. Similar lemmas for recv, select, branch, newSession
Each shows that the left frame is preserved after the step.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Left-Frame Step Cases -/
/-- Helper: send case for the left-frame preservation lemma. -/
lemma preserved_sub_left_frame_send
    {Gstore G₁ G₂ G G' Ssh Sown store k x e target T L G₁' Sfin Gfin W Δ} :
    StoreTypedVisible Gstore Ssh Sown store →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.send target T L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₁ (.send k x) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the send pre-out rule and rewrite the left update.
  intro hStore hEq hEq' hk hG hGout hPre
  cases hPre with
  | send hk' hG' hx' =>
      rename_i e' q' T' L'
      have hEqE : e = e' :=
        endpoint_eq_of_store_visible hStore hk hk'
      have hG₁e : lookupG G₁ e = some (.send q' T' L') := by
        simpa [hEqE] using hG'
      have hL : L' = L := send_localtype_eq (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e)
        (target:=target) (q:=q') (T:=T) (T':=T') (L:=L) (L':=L') hEq hG₁e hG
      have hG₁' : G₁' = updateG G₁ e L :=
        updateG_left_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₁':=G₁') (e:=e)
          (L:=L) (L0:=.send q' T' L') hEq hEq' hG₁e hGout.symm
      refine ⟨[], ∅, ?_, ?_, ?_⟩
      · simpa [hG₁', hL, hEqE] using
          (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G₁ e L))
      · intro x hx0; cases hx0
      · intro x T hx0; cases hx0

/-- Helper: select case for the left-frame preservation lemma. -/
-- Left-Frame Select Case
lemma preserved_sub_left_frame_select
    {Gstore G₁ G₂ G G' Ssh Sown store k ℓ e target bs L G₁' Sfin Gfin W Δ} :
    StoreTypedVisible Gstore Ssh Sown store →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.select target bs) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₁ (.select k ℓ) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the select pre-out rule and rewrite the left update.
  intro hStore hEq hEq' hk hG hFind hGout hPre
  cases hPre with
  | select hk' hG' hFind' =>
      rename_i e' q' bs' L'
      have hEqE : e = e' :=
        endpoint_eq_of_store_visible hStore hk hk'
      have hG₁e : lookupG G₁ e = some (.select q' bs') := by
        simpa [hEqE] using hG'
      have hBs : bs' = bs :=
        select_branches_eq (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (target:=target) (q:=q')
          (bs:=bs) (bs':=bs') hEq hG₁e hG
      have hL : L' = L :=
        select_label_eq (bs:=bs) (bs':=bs') (ℓ:=ℓ) (L:=L) (L':=L') hBs hFind' hFind
      have hG₁' : G₁' = updateG G₁ e L :=
        updateG_left_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₁':=G₁') (e:=e)
          (L:=L) (L0:=.select q' bs') hEq hEq' hG₁e hGout.symm
      refine ⟨[], ∅, ?_, ?_, ?_⟩
      · simpa [hG₁', hL, hEqE] using
          (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=updateG G₁ e L))
      · intro x hx0; cases hx0
      · intro x T hx0; cases hx0

/-- Helper: branch case for the left-frame preservation lemma. -/
-- Left-Frame Branch Case
lemma preserved_sub_left_frame_branch
    {Gstore G₁ G₂ G G' Ssh Sown store k procs e source bs ℓ P L G₁' Sfin Gfin W Δ} :
    StoreTypedVisible Gstore Ssh Sown store →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.branch source bs) →
    procs.find? (fun b => b.1 == ℓ) = some (ℓ, P) →
    bs.find? (fun b => b.1 == ℓ) = some (ℓ, L) →
    G' = updateG G e L →
    HasTypeProcPreOut Ssh Sown G₁ (.branch k procs) Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown G₁' P Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Reduce to the branch pre-out rule and rewrite the left update.
  intro hStore hEq hEq' hk hG hFindP hFindT hGout hPre
  cases hPre with
  | branch hk' hG' hLen hLabels hPreAll hPost hSess hDom hRight =>
      rename_i e' p' bs'
      have hEqE : e = e' :=
        endpoint_eq_of_store_visible hStore hk hk'
      have hG₁e : lookupG G₁ e = some (.branch p' bs') := by
        simpa [hEqE] using hG'
      have hBs : bs' = bs :=
        branch_branches_eq (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
          (bs:=bs) (bs':=bs') hEq hG₁e hG
      have hFindT' : bs'.find? (fun b => b.1 == ℓ) = some (ℓ, L) :=
        branch_find_eq (bs:=bs) (bs':=bs') (ℓ:=ℓ) (L:=L) hBs hFindT
      have hPre' := hPost _ _ _ hFindP hFindT'
      have hG₁' : G₁' = updateG G₁ e L :=
        updateG_left_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₁':=G₁') (e:=e)
          (L:=L) (L0:=.branch p' bs') hEq hEq' hG₁e hGout.symm
      refine ⟨W, Δ, ?_, FootprintSubset_refl, SEnvDomSubset_refl⟩
      simpa [hG₁', hEqE] using hPre'

/-- Helper: assign-new case for the left-frame preservation lemma. -/
-- Left-Frame Assign-New Case
lemma preserved_sub_left_frame_assign_new
    {G₁ G₂ G Ssh Sown x v T_step Sown' G₁' Sfin Gfin W Δ} {T_pre : ValType} :
    G = G₁ ++ G₂ →
    G = G₁' ++ G₂ →
    HasTypeVal G v T_step →
    Sown' = OwnedEnv.updateLeft Sown x T_step →
    Sfin = OwnedEnv.updateLeft Sown x T_pre →
    Gfin = G₁ →
    lookupSEnv Ssh x = none →
    lookupSEnv Sown.left x = none →
    HasTypeVal G₁ v T_pre →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use typing uniqueness to align the assigned type and cancel the frame.
  intro hEq hEq' hv hSout hSfin hGfin hSsh hSownL hv'
  have hv'' : HasTypeVal G v T_pre := by
    -- Strengthen the typing to the framed global environment.
    refine HasTypeVal_mono G₁ G v T_pre hv' ?_
    intro e L hLookup
    have hLookup' : lookupG (G₁ ++ G₂) e = some L :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hLookup
    simpa [hEq] using hLookup'
  have hT := HasTypeVal_unique hv'' hv
  cases hT
  have hEqG : G₁' ++ G₂ = G₁ ++ G₂ := by
    have hEqG0 : G₁' ++ G₂ = G := by
      simpa using hEq'.symm
    simpa [hEq] using hEqG0
  have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₁', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T_step) (G:=G₁))
  · intro x hx; cases hx
  · intro x T hx; cases hx

/-- Helper: assign-old case for the left-frame preservation lemma. -/
-- Left-Frame Assign-Old Case
lemma preserved_sub_left_frame_assign_old
    {G₁ G₂ G Ssh Sown x v T_step Sown' G₁' Sfin Gfin W Δ} {T_pre T_old : ValType} :
    G = G₁ ++ G₂ →
    G = G₁' ++ G₂ →
    HasTypeVal G v T_step →
    Sown' = OwnedEnv.updateLeft Sown x T_step →
    Sfin = OwnedEnv.updateLeft Sown x T_pre →
    Gfin = G₁ →
    lookupSEnv Ssh x = none →
    lookupSEnv Sown.left x = some T_old →
    HasTypeVal G₁ v T_pre →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use typing uniqueness to align the assigned type and cancel the frame.
  intro hEq hEq' hv hSout hSfin hGfin hSsh hSownL hv'
  have hv'' : HasTypeVal G v T_pre := by
    -- Strengthen the typing to the framed global environment.
    refine HasTypeVal_mono G₁ G v T_pre hv' ?_
    intro e L hLookup
    have hLookup' : lookupG (G₁ ++ G₂) e = some L :=
      lookupG_append_left (G₁:=G₁) (G₂:=G₂) hLookup
    simpa [hEq] using hLookup'
  have hT := HasTypeVal_unique hv'' hv
  cases hT
  have hEqG : G₁' ++ G₂ = G₁ ++ G₂ := by
    have hEqG0 : G₁' ++ G₂ = G := by
      simpa using hEq'.symm
    simpa [hEq] using hEqG0
  have hG₁' : G₁' = G₁ := append_left_eq_of_eq hEqG
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₁', hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T_step) (G:=G₁))
  · intro x hx; cases hx
  · intro x T hx; cases hx

/-- Helper: recv-new case for the left-frame preservation lemma. -/
-- Left-Frame Recv-New Case
lemma preserved_sub_left_frame_recv_new
    {Gstore G₁ G₂ G G' Ssh Sown store k x e source T L G₁' Sown' Sfin Gfin W Δ}
    {e' : Endpoint} {p' : Role} {T' : ValType} {L' : LocalType} :
    StoreTypedVisible Gstore Ssh Sown store →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = OwnedEnv.updateLeft Sown x T →
    Sfin = OwnedEnv.updateLeft Sown x T' →
    Gfin = updateG G₁ e' L' →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e'.sid e'.role) →
    lookupG G₁ e' = some (.recv p' T' L') →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use the recv-new pre-out premises and rewrite the left update.
  intro hStore hEq hEq' hk hG hGout hSout hSfin hGfin hk' hG'
  have hEqE : e = e' :=
    endpoint_eq_of_store_visible hStore hk hk'
  have hG₁e : lookupG G₁ e = some (.recv p' T' L') := by
    simpa [hEqE] using hG'
  have hTL : T' = T ∧ L' = L :=
    recv_types_eq (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
      (T:=T) (T':=T') (L:=L) (L':=L') hEq hG₁e hG
  have hG₁' : G₁' = updateG G₁ e L :=
    updateG_left_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₁':=G₁') (e:=e)
      (L:=L) (L0:=.recv p' T' L') hEq hEq' hG₁e hGout.symm
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₁', hTL.1, hTL.2, hEqE, hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G₁ e L))
  · intro x hx0; cases hx0
  · intro x T hx0; cases hx0

/-- Helper: recv-old case for the left-frame preservation lemma. -/
-- Left-Frame Recv-Old Case
lemma preserved_sub_left_frame_recv_old
    {Gstore G₁ G₂ G G' Ssh Sown store k x e source T L G₁' Sown' Sfin Gfin W Δ}
    {e' : Endpoint} {p' : Role} {T' : ValType} {L' : LocalType} :
    StoreTypedVisible Gstore Ssh Sown store →
    G = G₁ ++ G₂ →
    G' = G₁' ++ G₂ →
    lookupStr store k = some (.chan e) →
    lookupG G e = some (.recv source T L) →
    G' = updateG G e L →
    Sown' = OwnedEnv.updateLeft Sown x T →
    Sfin = OwnedEnv.updateLeft Sown x T' →
    Gfin = updateG G₁ e' L' →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e'.sid e'.role) →
    lookupG G₁ e' = some (.recv p' T' L') →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G₁' .skip Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  -- Use the recv-old pre-out premises and rewrite the left update.
  intro hStore hEq hEq' hk hG hGout hSout hSfin hGfin hk' hG'
  have hEqE : e = e' :=
    endpoint_eq_of_store_visible hStore hk hk'
  have hG₁e : lookupG G₁ e = some (.recv p' T' L') := by
    simpa [hEqE] using hG'
  have hTL : T' = T ∧ L' = L :=
    recv_types_eq (G₁:=G₁) (G₂:=G₂) (G:=G) (e:=e) (source:=source) (p:=p')
      (T:=T) (T':=T') (L:=L) (L':=L') hEq hG₁e hG
  have hG₁' : G₁' = updateG G₁ e L :=
    updateG_left_of_step (G₁:=G₁) (G₂:=G₂) (G:=G) (G':=G') (G₁':=G₁') (e:=e)
      (L:=L) (L0:=.recv p' T' L') hEq hEq' hG₁e hGout.symm
  refine ⟨[], ∅, ?_, ?_, ?_⟩
  · subst hSout
    simpa [hG₁', hTL.1, hTL.2, hEqE, hSfin, hGfin] using
      (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown.updateLeft x T) (G:=updateG G₁ e L))
  · intro x hx0; cases hx0
  · intro x T hx0; cases hx0
