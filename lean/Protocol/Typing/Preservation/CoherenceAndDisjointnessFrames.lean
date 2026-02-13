
import Protocol.Typing.Preservation.CoherenceAndDisjointnessCore

/-! # Coherence and Disjointness Frame Preservation

Preservation lemmas for SEnv disjointness through typed steps,
particularly for recv and assign operations that update owned envs. -/

/-
The Problem. Typed steps may update the owned SEnv (recv assigns to
a variable, assign writes a value). We need to show disjointness
between shared and owned envs is preserved.

Solution Structure. Prove `DisjointS_preserved_TypedStep_right_recv`
and `_assign` by case analysis on the pre-out typing. Use the fact
that updated variables are absent from the shared env.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

-- Recv Disjointness Preservation

lemma DisjointS_preserved_TypedStep_right_recv
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var} {T : ValType}
    {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh (OwnedEnv.updateLeft Sown x T) := by
  -- Both recv cases update the owned-left, with x absent from shared env.
  intro hPre hDisj
  cases hPre with
  | recv_new _ _ hNoSh _ =>
      exact DisjointS_updateLeft (S₁:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisj hNoSh
  | recv_old _ _ hNoSh _ =>
      exact DisjointS_updateLeft (S₁:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisj hNoSh

/-- Assignment preserves disjointness between shared and owned envs. -/
-- Assign Disjointness Preservation
lemma DisjointS_preserved_TypedStep_right_assign
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {x : Var} {v : Value} {T : ValType}
    {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    DisjointS Ssh (OwnedEnv.updateLeft Sown x T) := by
  -- Both assign cases update the owned-left, with x absent from shared env.
  intro hPre hDisj
  cases hPre with
  | assign_new hNoSh _ _ =>
      exact DisjointS_updateLeft (S₁:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisj hNoSh
  | assign_old hNoSh _ _ =>
      exact DisjointS_updateLeft (S₁:=Ssh) (Sown:=Sown) (x:=x) (T:=T) hDisj hNoSh

/-- Par-left step preserves disjointness on the owned env. -/
-- Par-Left Disjointness Preservation (Right Projection)
lemma DisjointS_preserved_TypedStep_right_par_left
    {Ssh : SEnv} {Sown : OwnedEnv} {P Q : Process} {G : GEnv} {S₁' : SEnv}
    {nS nG : Nat} {Sfin Gfin W Δ}
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
        (ih : ∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G P Sfin Gfin W Δ →
      DisjointS Ssh ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) →
      DisjointS (Sown.right ++ split.S2) split.S1 →
      DisjointS (Sown.right ++ split.S2) Sfin.left →
      DisjointS Ssh ({ right := Sown.right ++ split.S2, left := S₁' } : OwnedEnv))
    (hPre : HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin W Δ)
    (hDisj : DisjointS Ssh Sown)
    (hOwnDisj : OwnedDisjoint Sown)
    (hDisjRightFin : DisjointS Sown.right Sfin.left) :
    DisjointS Ssh ({ right := Sown.right, left := S₁' ++ split.S2 } : OwnedEnv) := by
  -- Align splits, repackage disjointness for the left step, then rebuild the result.
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁_fin, W₂_fin, Δ₁_fin, Δ₂_fin,
      hSfin, hGfin, hW, hΔ, hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
/- ## Structured Block 2 -/
    HasTypeProcPreOut_par_inv_witness hPre
  let split_pre : ParSplit Sown.left G := pw.split
  have hS1eq : split.S1 = split_pre.S1 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
  have hS2eq : split.S2 = split_pre.S2 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
  have hDisjG : DisjointG split_pre.G1 split_pre.G2 := hDisjG_pre
  have hDisjS : DisjointS split.S1 split.S2 := by
    simpa [hS1eq, hS2eq] using hDisjS_pre
  have hDisjS_left : DisjointS S₁_fin split.S2 := by
    simpa [hS2eq] using hDisjS_left_pre
  have hP :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split_pre.G1 P
        { right := Sown.right ++ split.S2, left := S₁_fin } G₁_fin W₁_fin Δ₁_fin := by
    simpa [hS1eq, hS2eq] using hP_pre
  -- # Repackage Owned/Shared Disjointness for IH
  rcases DisjointS_split_from_owned_left (Sown:=Sown) (split:=split) hDisj with ⟨hDisjS1, hDisjS2⟩
  have hDisjRight : DisjointS Ssh Sown.right := DisjointS_owned_right hDisj
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwnDisj
  have hDisjRightS1 : DisjointS Sown.right split.S1 := DisjointS_split_left hOwnLeftAll
  have hDisjInP : DisjointS (Sown.right ++ split.S2) split.S1 :=
    DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
  have hDisjRightFin' : DisjointS Sown.right (S₁_fin ++ S₂_fin) := by
    simpa [hSfin] using hDisjRightFin
  have hDisjRightS1' : DisjointS Sown.right S₁_fin := DisjointS_split_left hDisjRightFin'
  have hDisjOutP : DisjointS (Sown.right ++ split.S2) S₁_fin :=
    DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
  have hInner : DisjointS Ssh ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
    DisjointS_owned_repack (Sright:=Sown.right) (Sleft:=split.S1) (Smid:=split.S2)
      hDisjRight hDisjS1 hDisjS2
  have hP_full_pre := HasTypeProcPreOut_frame_G_right_par (split:=split_pre) hDisjG hP_pre
  have hP_full :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G P
        { right := Sown.right ++ split.S2, left := S₁_fin } (G₁_fin ++ split_pre.G2) W₁_fin Δ₁_fin := by
    simpa [hS1eq, hS2eq] using hP_full_pre
  have hInnerRes := ih hP_full hInner hDisjInP hDisjOutP
  exact DisjointS_par_left_finish (SownR:=Sown.right) (S₂:=split.S2) (S₁':=S₁')
    hDisjRight hDisjS2 hInnerRes

/-- Par-right step preserves disjointness on the owned env. -/
-- Par-Right Disjointness Preservation (Right Projection)
lemma DisjointS_preserved_TypedStep_right_par_right
    {Ssh : SEnv} {Sown : OwnedEnv} {P Q : Process} {G : GEnv} {S₂' : SEnv}
    {nS nG : Nat} {Sfin Gfin W Δ}
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
        (ih : ∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G Q Sfin Gfin W Δ →
      DisjointS Ssh ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) →
      DisjointS (Sown.right ++ split.S1) split.S2 →
      DisjointS (Sown.right ++ split.S1) Sfin.left →
/- ## Structured Block 3 -/
      DisjointS Ssh ({ right := Sown.right ++ split.S1, left := S₂' } : OwnedEnv))
    (hPre : HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin W Δ)
    (hDisj : DisjointS Ssh Sown)
    (hOwnDisj : OwnedDisjoint Sown)
    (hDisjRightFin : DisjointS Sown.right Sfin.left) :
    DisjointS Ssh ({ right := Sown.right, left := split.S1 ++ S₂' } : OwnedEnv) := by
  -- Align splits, repackage disjointness for the right step, then rebuild the result.
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁_fin, W₂_fin, Δ₁_fin, Δ₂_fin,
      hSfin, hGfin, hW, hΔ, hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
    HasTypeProcPreOut_par_inv_witness hPre
  let split_pre : ParSplit Sown.left G := pw.split
  have hS1eq : split.S1 = split_pre.S1 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
  have hS2eq : split.S2 = split_pre.S2 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
  have hDisjG : DisjointG split_pre.G1 split_pre.G2 := hDisjG_pre
  have hDisjS : DisjointS split.S1 split.S2 := by
    simpa [hS1eq, hS2eq] using hDisjS_pre
  have hDisjS_right : DisjointS split.S1 S₂_fin := by
    simpa [hS1eq] using hDisjS_right_pre
  have hQ :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split_pre.G2 Q
        { right := Sown.right ++ split.S1, left := S₂_fin } G₂_fin W₂_fin Δ₂_fin := by
    simpa [hS1eq, hS2eq] using hQ_pre
  -- # Repackage Owned/Shared Disjointness for IH
  rcases DisjointS_split_from_owned_left (Sown:=Sown) (split:=split) hDisj with ⟨hDisjS1, hDisjS2⟩
  have hDisjRight : DisjointS Ssh Sown.right := DisjointS_owned_right hDisj
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwnDisj
  have hDisjRightS2 : DisjointS Sown.right split.S2 := DisjointS_split_right hOwnLeftAll
  have hDisjInQ : DisjointS (Sown.right ++ split.S1) split.S2 :=
    DisjointS_append_left hDisjRightS2 hDisjS
  have hDisjRightFin' : DisjointS Sown.right (S₁_fin ++ S₂_fin) := by
    simpa [hSfin] using hDisjRightFin
  have hDisjRightS2' : DisjointS Sown.right S₂_fin := DisjointS_split_right hDisjRightFin'
  have hDisjOutQ : DisjointS (Sown.right ++ split.S1) S₂_fin :=
    DisjointS_append_left hDisjRightS2' hDisjS_right
  have hInner : DisjointS Ssh ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
    DisjointS_owned_repack (Sright:=Sown.right) (Sleft:=split.S2) (Smid:=split.S1)
      hDisjRight hDisjS2 hDisjS1
  have hQ_full_pre := HasTypeProcPreOut_frame_G_left_par (split:=split_pre) hDisjG
    (by simpa [hS1eq, hS2eq] using hDisjInQ) hQ_pre (by simpa [hS1eq, hS2eq] using hDisjOutQ)
  have hQ_full :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G Q
        { right := Sown.right ++ split.S1, left := S₂_fin } (split_pre.G1 ++ G₂_fin) W₂_fin Δ₂_fin := by
    simpa [hS1eq, hS2eq] using hQ_full_pre
  exact DisjointS_par_right_finish (SownR:=Sown.right) (S₁:=split.S1) (S₂':=S₂')
    hDisjRight hDisjS1 (ih hQ_full hInner hDisjInQ hDisjOutQ)

/-- Recv preserves disjointness against the left owned env. -/
-- Recv Disjointness Preservation (Left Projection)
lemma DisjointS_preserved_TypedStep_left_recv
/- ## Structured Block 4 -/
    {Sframe Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {k x : Var} {T : ValType}
    {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.recv k x) Sfin Gfin W Δ →
    lookupSEnv Sown.right x = none →
    DisjointS Sframe Sown.left →
    SEnvDomSubset Sframe Sown.right →
    DisjointS Sframe (updateSEnv Sown.left x T) := by
  -- x cannot be in the frame if absent from right; old case also follows from left disjointness.
  intro hPre hNoOwnR hDisj hSub
  cases hPre with
  | recv_new _ _ _ hNoOwnL =>
      have hNone : lookupSEnv Sframe x = none :=
        lookupSEnv_none_of_domsubset_right (Sframe:=Sframe) (Sright:=Sown.right) hSub hNoOwnR
      exact DisjointS_update_right (S₁:=Sframe) (S₂:=Sown.left) hDisj hNone
  | recv_old _ _ _ hOwnL =>
      have hNone : lookupSEnv Sframe x = none :=
        lookupSEnv_none_of_disjoint_left hDisj hOwnL
      exact DisjointS_update_right (S₁:=Sframe) (S₂:=Sown.left) hDisj hNone

/-- Assignment preserves disjointness against the left owned env. -/
-- Assign Disjointness Preservation (Left Projection)
lemma DisjointS_preserved_TypedStep_left_assign
    {Sframe Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {x : Var} {v : Value} {T : ValType}
    {Sfin Gfin W Δ} :
    HasTypeProcPreOut Ssh Sown G (.assign x v) Sfin Gfin W Δ →
    lookupSEnv Sown.right x = none →
    DisjointS Sframe Sown.left →
    SEnvDomSubset Sframe Sown.right →
    DisjointS Sframe (updateSEnv Sown.left x T) := by
  -- x cannot be in the frame if absent from right; old case also follows from left disjointness.
  intro hPre hNoOwnR hDisj hSub
  cases hPre with
  | assign_new _ hNoOwnL _ =>
      have hNone : lookupSEnv Sframe x = none :=
        lookupSEnv_none_of_domsubset_right (Sframe:=Sframe) (Sright:=Sown.right) hSub hNoOwnR
      exact DisjointS_update_right (S₁:=Sframe) (S₂:=Sown.left) hDisj hNone
  | assign_old _ hOwnL _ =>
      have hNone : lookupSEnv Sframe x = none :=
        lookupSEnv_none_of_disjoint_left hDisj hOwnL
      exact DisjointS_update_right (S₁:=Sframe) (S₂:=Sown.left) hDisj hNone

/-- Par-left step preserves disjointness on the left owned env. -/
-- Par-Left Disjointness Preservation (Left Projection)
lemma DisjointS_preserved_TypedStep_left_par_left
    {Sframe Ssh : SEnv} {Sown : OwnedEnv} {P Q : Process} {G : GEnv} {S₁' : SEnv}
    {nS nG : Nat} {Sfin Gfin W Δ}
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
        (ih : ∀ {Sfin Gfin W Δ},
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G P Sfin Gfin W Δ →
      DisjointS Sframe split.S1 →
      SEnvDomSubset Sframe (Sown.right ++ split.S2) →
      DisjointS (Sown.right ++ split.S2) split.S1 →
      DisjointS (Sown.right ++ split.S2) Sfin.left →
      ({ right := Sown.right ++ split.S2, left := S₁' } : OwnedEnv).right = (Sown.right ++ split.S2) →
      DisjointS Sframe S₁')
    (hPre : HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin W Δ)
    (hDisj : DisjointS Sframe Sown.left)
/- ## Structured Block 5 -/
    (hSub : SEnvDomSubset Sframe Sown.right)
    (hOwnDisj : OwnedDisjoint Sown)
    (hDisjRightFin : DisjointS Sown.right Sfin.left) :
    DisjointS Sframe (S₁' ++ split.S2) := by
  -- Align splits, then apply IH on the left subprocess.
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁_fin, W₂_fin, Δ₁_fin, Δ₂_fin,
      hSfin, hGfin, hW, hΔ, hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
    HasTypeProcPreOut_par_inv_witness hPre
  let split_pre : ParSplit Sown.left G := pw.split
  have hS1eq : split.S1 = split_pre.S1 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
  have hS2eq : split.S2 = split_pre.S2 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
  have hDisjG : DisjointG split_pre.G1 split_pre.G2 := hDisjG_pre
  have hDisjS : DisjointS split.S1 split.S2 := by
    simpa [hS1eq, hS2eq] using hDisjS_pre
  have hDisjS_left : DisjointS S₁_fin split.S2 := by
    simpa [hS2eq] using hDisjS_left_pre
  have hP :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split_pre.G1 P
        { right := Sown.right ++ split.S2, left := S₁_fin } G₁_fin W₁_fin Δ₁_fin := by
    simpa [hS1eq, hS2eq] using hP_pre
  -- # Establish IH Side Conditions
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwnDisj
  have hDisjRightS1 : DisjointS Sown.right split.S1 := DisjointS_split_left hOwnLeftAll
  have hDisjInP : DisjointS (Sown.right ++ split.S2) split.S1 :=
    DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
  have hDisjRightFin' : DisjointS Sown.right (S₁_fin ++ S₂_fin) := by
    simpa [hSfin] using hDisjRightFin
  have hDisjRightS1' : DisjointS Sown.right S₁_fin := DisjointS_split_left hDisjRightFin'
  have hDisjOutP : DisjointS (Sown.right ++ split.S2) S₁_fin :=
    DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
  rcases DisjointS_split_both (by simpa [split.hS] using hDisj) with ⟨hDisjS1, hDisjS2⟩
  have hSubInner : SEnvDomSubset Sframe (Sown.right ++ split.S2) := by
    exact SEnvDomSubset_trans hSub
      (SEnvDomSubset_append_left (S₁:=Sown.right) (S₂:=split.S2))
  have hP_full_pre := HasTypeProcPreOut_frame_G_right_par (split:=split_pre) hDisjG hP_pre
  have hP_full :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G P
        { right := Sown.right ++ split.S2, left := S₁_fin } (G₁_fin ++ split_pre.G2) W₁_fin Δ₁_fin := by
    simpa [hS1eq, hS2eq] using hP_full_pre
  exact DisjointS_append_right (ih hP_full hDisjS1 hSubInner hDisjInP hDisjOutP rfl) hDisjS2

/-- Par-right step preserves disjointness on the left owned env. -/
-- Par-Right Disjointness Preservation (Left Projection)
lemma DisjointS_preserved_TypedStep_left_par_right
    {Sframe Ssh : SEnv} {Sown : OwnedEnv} {P Q : Process} {G : GEnv} {S₂' : SEnv}
    {nS nG : Nat} {Sfin Gfin W Δ}
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
        (ih : ∀ {Sfin Gfin W Δ},
/- ## Structured Block 6 -/
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G Q Sfin Gfin W Δ →
      DisjointS Sframe split.S2 →
      SEnvDomSubset Sframe (Sown.right ++ split.S1) →
      OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) →
      DisjointS (Sown.right ++ split.S1) Sfin.left →
      ({ right := Sown.right ++ split.S1, left := S₂' } : OwnedEnv).right = (Sown.right ++ split.S1) →
      DisjointS Sframe S₂')
    (hPre : HasTypeProcPreOut Ssh Sown G (.par nS nG P Q) Sfin Gfin W Δ)
    (hDisj : DisjointS Sframe Sown.left)
    (hSub : SEnvDomSubset Sframe Sown.right)
    (hOwnDisj : OwnedDisjoint Sown)
    (hDisjRightFin : DisjointS Sown.right Sfin.left) :
    DisjointS Sframe (split.S1 ++ S₂') := by
  -- Align splits, then apply IH on the right subprocess.
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁_fin, W₂_fin, Δ₁_fin, Δ₂_fin,
      hSfin, hGfin, hW, hΔ, hDisjG_pre, hDisjS_pre, hDisjS_left_pre, hDisjS_right_pre,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
    HasTypeProcPreOut_par_inv_witness hPre
  let split_pre : ParSplit Sown.left G := pw.split
  have hS1eq : split.S1 = split_pre.S1 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).1
  have hS2eq : split.S2 = split_pre.S2 := by
    simpa [split_pre] using
      (ParSplit.sides_eq_of_witness (split:=split) (pw:=pw) hSlen).2
  have hDisjG : DisjointG split_pre.G1 split_pre.G2 := hDisjG_pre
  have hDisjS : DisjointS split.S1 split.S2 := by
    simpa [hS1eq, hS2eq] using hDisjS_pre
  have hDisjS_right : DisjointS split.S1 S₂_fin := by
    simpa [hS1eq] using hDisjS_right_pre
  have hQ :
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split_pre.G2 Q
        { right := Sown.right ++ split.S1, left := S₂_fin } G₂_fin W₂_fin Δ₂_fin := by
    simpa [hS1eq, hS2eq] using hQ_pre
  -- # Establish IH Side Conditions
  have hOwnLeftAll : DisjointS Sown.right (split.S1 ++ split.S2) := by
    simpa [OwnedDisjoint, split.hS] using hOwnDisj
  have hDisjRightS2 : DisjointS Sown.right split.S2 := DisjointS_split_right hOwnLeftAll
  have hDisjInQ : DisjointS (Sown.right ++ split.S1) split.S2 :=
    DisjointS_append_left hDisjRightS2 hDisjS
  have hDisjRightFin' : DisjointS Sown.right (S₁_fin ++ S₂_fin) := by
    simpa [hSfin] using hDisjRightFin
  have hDisjRightS2' : DisjointS Sown.right S₂_fin := DisjointS_split_right hDisjRightFin'
  have hDisjOutQ : DisjointS (Sown.right ++ split.S1) S₂_fin :=
    DisjointS_append_left hDisjRightS2' hDisjS_right
  rcases DisjointS_split_both (by simpa [split.hS] using hDisj) with ⟨hDisjS1, hDisjS2⟩
  have hSubInner : SEnvDomSubset Sframe (Sown.right ++ split.S1) := by
    exact SEnvDomSubset_trans hSub
      (SEnvDomSubset_append_left (S₁:=Sown.right) (S₂:=split.S1))
  have hQ_full_pre := HasTypeProcPreOut_frame_G_left_par (split:=split_pre) hDisjG
    (by simpa [hS1eq, hS2eq] using hDisjInQ) hQ_pre (by simpa [hS1eq, hS2eq] using hDisjOutQ)
  have hQ_full :
/- ## Structured Block 7 -/
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G Q
        { right := Sown.right ++ split.S1, left := S₂_fin } (split_pre.G1 ++ G₂_fin) W₂_fin Δ₂_fin := by
    simpa [hS1eq, hS2eq] using hQ_full_pre
  exact DisjointS_append_right hDisjS1 (ih hQ_full hDisjS2 hSubInner hDisjInQ hDisjOutQ rfl)

-- Global Right-Preservation Theorem

theorem DisjointS_preserved_TypedStep_right
    {G D Ssh Sown store bufs Q G' D' Sown' store' bufs' Q' Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs Q G' D' Sown' store' bufs' Q' →
    HasTypeProcPreOut Ssh Sown G Q Sfin Gfin W Δ →
    DisjointS Ssh Sown →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    DisjointS Ssh Sown' := by
  -- Induction on steps; trivial cases close by simp.
  intro hTS hPre hDisj hOwnDisj hDisjRightFin
  induction hTS generalizing Sfin Gfin W Δ <;> try (cases hPre <;> simpa using hDisj)
  case recv G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
    have hDisj' := DisjointS_preserved_TypedStep_right_recv (k:=k) (x:=x) (T:=T) hPre hDisj
    simpa [hSout] using hDisj'
  case assign G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut =>
    have hDisj' := DisjointS_preserved_TypedStep_right_assign (x:=x) (v:=v) (T:=T) hPre hDisj
    simpa [hSout] using hDisj'
  case seq_step _ ih =>
    cases hPre with
    | seq hP hQ =>
        have hDomQ := HasTypeProcPreOut_domsubset hQ
        have hDisjRightMid := DisjointS_of_domsubset_right hDomQ hDisjRightFin
        exact ih hP hDisj hOwnDisj hDisjRightMid
  case par_left split hSlen _ _ _ _ ih =>
    exact DisjointS_preserved_TypedStep_right_par_left
      (split:=split) (hSlen:=hSlen) (ih:=ih)
      (hPre:=hPre) hDisj hOwnDisj hDisjRightFin
  case par_right split hSlen _ _ _ _ ih =>
    exact DisjointS_preserved_TypedStep_right_par_right
      (split:=split) (hSlen:=hSlen) (ih:=ih)
      (hPre:=hPre) hDisj hOwnDisj hDisjRightFin

-- Global Left-Preservation Theorem

theorem DisjointS_preserved_TypedStep_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sframe Sfin Gfin W Δ} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Sframe Sown.left →
    SEnvDomSubset Sframe Sown.right →
    OwnedDisjoint Sown →
    DisjointS Sown.right Sfin.left →
    Sown'.right = Sown.right →
    DisjointS Sframe Sown'.left := by
  -- Induction on steps; trivial cases close by simp.
  intro hTS hPre hDisj hSub hOwnDisj hDisjRightFin hRightEq
  induction hTS generalizing Sfin Gfin W Δ <;> try (cases hPre <;> simpa using hDisj)
  case recv G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
    have hUpdRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
/- ## Structured Block 8 -/
      simpa [hSout] using hRightEq
    have hEraseEq : eraseSEnv Sown.right x = Sown.right := by
      simpa [OwnedEnv.updateLeft] using hUpdRightEq
    have hNoOwnR : lookupSEnv Sown.right x = none := by
      have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
        lookupSEnv_erase_eq (S:=Sown.right) (x:=x)
      simpa [hEraseEq] using hNoneErase
    have hDisj' :=
      DisjointS_preserved_TypedStep_left_recv (k:=k) (x:=x) (T:=T) hPre hNoOwnR hDisj hSub
    simpa [hSout] using hDisj'
  case assign G D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut =>
    have hUpdRightEq : (OwnedEnv.updateLeft Sown x T).right = Sown.right := by
      simpa [hSout] using hRightEq
    have hEraseEq : eraseSEnv Sown.right x = Sown.right := by
      simpa [OwnedEnv.updateLeft] using hUpdRightEq
    have hNoOwnR : lookupSEnv Sown.right x = none := by
      have hNoneErase : lookupSEnv (eraseSEnv Sown.right x) x = none :=
        lookupSEnv_erase_eq (S:=Sown.right) (x:=x)
      simpa [hEraseEq] using hNoneErase
    have hDisj' :=
      DisjointS_preserved_TypedStep_left_assign (x:=x) (v:=v) (T:=T) hPre hNoOwnR hDisj hSub
    simpa [hSout] using hDisj'
  -- # Structural Cases (Seq/Par)
  case seq_step _ ih =>
    cases hPre with
    | seq hP hQ =>
        have hDomQ := HasTypeProcPreOut_domsubset hQ
        have hDisjRightMid := DisjointS_of_domsubset_right hDomQ hDisjRightFin
        exact ih hP hDisj hSub hOwnDisj hDisjRightMid hRightEq
  case par_left split hSlen _ _ _ _ ih =>
    exact DisjointS_preserved_TypedStep_left_par_left
      (split:=split) (hSlen:=hSlen) (ih:=ih)
      (hPre:=hPre) hDisj hSub hOwnDisj hDisjRightFin
  case par_right split hSlen _ _ _ _ ih =>
    exact DisjointS_preserved_TypedStep_left_par_right
      (split:=split) (hSlen:=hSlen) (ih:=ih)
      (hPre:=hPre) hDisj hSub hOwnDisj hDisjRightFin


end
