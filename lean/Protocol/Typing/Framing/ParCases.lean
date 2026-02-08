import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-- Helper: align S-splits by length under a shared SEnv. -/
private lemma par_split_S_eq
    {S : SEnv} {G G' : GEnv} {split : ParSplit S G} {split_pre : ParSplit S G'} {nS : Nat} :
    split.S1.length = nS →
    split_pre.S1.length = nS →
    split.S1 = split_pre.S1 ∧ split.S2 = split_pre.S2 := by
  -- Use the shared S decomposition and length to align the split.
  intro hSlen hSlenPre
  have hSlen' : split.S1.length = split_pre.S1.length := by
    calc
      split.S1.length = nS := hSlen
      _ = split_pre.S1.length := hSlenPre.symm
  have hSeq : split.S1 ++ split.S2 = split_pre.S1 ++ split_pre.S2 := by
    calc
      split.S1 ++ split.S2 = S := by simpa [split.hS]
      _ = split_pre.S1 ++ split_pre.S2 := by simpa [split_pre.hS]
  exact ⟨List.append_inj_left hSeq hSlen', List.append_inj_right hSeq hSlen'⟩

/-- Helper: align G-splits by length under a right frame. -/
private lemma par_split_G_eq
    {S : SEnv} {G₁ G₂ G : GEnv} {split : ParSplit S G} {split_pre : ParSplit S G₁} {nG : Nat} :
    split.G1.length = nG →
    split_pre.G1.length = nG →
    G = G₁ ++ G₂ →
    split.G1 = split_pre.G1 ∧ split.G2 = split_pre.G2 ++ G₂ := by
  -- Use the shared length and frame equality to align the split.
  intro hGlen hGlenPre hEq
  have hGlen' : split.G1.length = split_pre.G1.length := by
    calc
      split.G1.length = nG := hGlen
      _ = split_pre.G1.length := hGlenPre.symm
  have hGeq : split.G1 ++ split.G2 = split_pre.G1 ++ (split_pre.G2 ++ G₂) := by
    calc
      split.G1 ++ split.G2 = G := by simpa [split.hG]
      _ = G₁ ++ G₂ := hEq
      _ = (split_pre.G1 ++ split_pre.G2) ++ G₂ := by simpa [split_pre.hG]
      _ = split_pre.G1 ++ (split_pre.G2 ++ G₂) := by simp [List.append_assoc]
  exact ⟨List.append_inj_left hGeq hGlen', List.append_inj_right hGeq hGlen'⟩

/-- Helper: align S/G splits under a right frame. -/
private lemma par_split_eqs
    {S : SEnv} {G G₁ G₂ : GEnv} {split : ParSplit S G} {split_pre : ParSplit S G₁} {nS nG : Nat} :
    split.S1.length = nS →
    split_pre.S1.length = nS →
    split.G1.length = nG →
    split_pre.G1.length = nG →
    G = G₁ ++ G₂ →
    split.S1 = split_pre.S1 ∧ split.S2 = split_pre.S2 ∧
      split.G1 = split_pre.G1 ∧ split.G2 = split_pre.G2 ++ G₂ := by
  -- Combine the S/G split alignment lemmas.
  intro hSlen hSlenPre hGlen hGlenPre hEq
  have hS := par_split_S_eq (S:=S) (G:=G) (G':=G₁) (split:=split) (split_pre:=split_pre)
    (nS:=nS) hSlen hSlenPre
  have hG := par_split_G_eq (S:=S) (G₁:=G₁) (G₂:=G₂) (G:=G) (split:=split) (split_pre:=split_pre)
    (nG:=nG) hGlen hGlenPre hEq
  exact ⟨hS.1, hS.2, hG.1, hG.2⟩

/-- Helper: derive inner disjointness/equality for left-step par. -/
private lemma par_left_inner_eqs
    {S : SEnv} {G₁ G₂ G : GEnv} {split_pre : ParSplit S G₁} :
    G = G₁ ++ G₂ →
    DisjointG G₁ G₂ →
    DisjointG split_pre.G1 split_pre.G2 →
    DisjointG split_pre.G1 (split_pre.G2 ++ G₂) ∧
      G = split_pre.G1 ++ (split_pre.G2 ++ G₂) := by
  -- Use session subset facts to extend disjointness and rewrite the split.
  intro hEq hDisj hDisjG'
  have hSubG1 : SessionsOf split_pre.G1 ⊆ SessionsOf G₁ := by
    have hSub := SessionsOf_append_left (G₁:=split_pre.G1) (G₂:=split_pre.G2)
    simpa [split_pre.hG] using hSub
  have hDisjG1G2 : DisjointG split_pre.G1 G₂ :=
    DisjointG_of_subset_left hSubG1 hDisj
  have hDisjG_inner : DisjointG split_pre.G1 (split_pre.G2 ++ G₂) :=
    DisjointG_append_right hDisjG' hDisjG1G2
  have hEq_inner : G = split_pre.G1 ++ (split_pre.G2 ++ G₂) := by
    calc
      G = G₁ ++ G₂ := hEq
      _ = (split_pre.G1 ++ split_pre.G2) ++ G₂ := by simpa [split_pre.hG]
      _ = split_pre.G1 ++ (split_pre.G2 ++ G₂) := by simp [List.append_assoc]
  exact ⟨hDisjG_inner, hEq_inner⟩

/-- Helper: derive inner disjointness/equality for right-step par. -/
private lemma par_right_inner_eqs
    {S : SEnv} {G₁ G₂ G : GEnv} {split_pre : ParSplit S G₁} :
    G = G₁ ++ G₂ →
    DisjointG G₁ G₂ →
    DisjointG split_pre.G1 G₂ ∧ DisjointG split_pre.G2 G₂ ∧
      G = split_pre.G1 ++ split_pre.G2 ++ G₂ := by
  -- Use session subset facts to extend disjointness and rewrite the split.
  intro hEq hDisj
  have hSubG1 : SessionsOf split_pre.G1 ⊆ SessionsOf G₁ := by
    have hSub := SessionsOf_append_left (G₁:=split_pre.G1) (G₂:=split_pre.G2)
    simpa [split_pre.hG] using hSub
  have hSubG2 : SessionsOf split_pre.G2 ⊆ SessionsOf G₁ := by
    have hSub := SessionsOf_append_right (G₁:=split_pre.G1) (G₂:=split_pre.G2)
    simpa [split_pre.hG] using hSub
  have hDisjG1G2 : DisjointG split_pre.G1 G₂ :=
    DisjointG_of_subset_left hSubG1 hDisj
  have hDisjG2G2 : DisjointG split_pre.G2 G₂ :=
    DisjointG_of_subset_left hSubG2 hDisj
  have hEq_inner : G = split_pre.G1 ++ split_pre.G2 ++ G₂ := by
    calc
      G = G₁ ++ G₂ := hEq
      _ = (split_pre.G1 ++ split_pre.G2) ++ G₂ := by simpa [split_pre.hG]
      _ = split_pre.G1 ++ split_pre.G2 ++ G₂ := by simp [List.append_assoc]
  exact ⟨hDisjG1G2, hDisjG2G2, hEq_inner⟩

/-! ### Par Split Setup Helpers -/

/-- Helper: align splits and inner equalities for the left-step par case. -/
private lemma par_left_setup
    {S : SEnv} {G G₁ G₂ : GEnv} {split : ParSplit S G} {split_pre : ParSplit S G₁}
    {G₁_step : GEnv} {nS nG : Nat} :
    split.S1.length = nS →
    split_pre.S1.length = nS →
    split.G1.length = nG →
    split_pre.G1.length = nG →
    G = G₁ ++ G₂ →
    DisjointG G₁ G₂ →
    DisjointG split_pre.G1 split_pre.G2 →
    split.S1 = split_pre.S1 ∧
      split.S2 = split_pre.S2 ∧
      split.G2 = split_pre.G2 ++ G₂ ∧
      DisjointG split_pre.G1 (split_pre.G2 ++ G₂) ∧
      G = split_pre.G1 ++ (split_pre.G2 ++ G₂) ∧
      G₁_step ++ split.G2 = G₁_step ++ (split_pre.G2 ++ G₂) := by
  intro hSlen hSlenPre hGlen hGlenPre hEq hDisj hDisjG'
  have hEqSplits :
      split.S1 = split_pre.S1 ∧ split.S2 = split_pre.S2 ∧
        split.G1 = split_pre.G1 ∧ split.G2 = split_pre.G2 ++ G₂ :=
    par_split_eqs (S:=S) (G:=G) (G₁:=G₁) (G₂:=G₂)
      (split:=split) (split_pre:=split_pre) (nS:=nS) (nG:=nG)
      hSlen hSlenPre hGlen hGlenPre hEq
  have hS1eq : split.S1 = split_pre.S1 := hEqSplits.1
  have hS2eq : split.S2 = split_pre.S2 := hEqSplits.2.1
  have hG2eq : split.G2 = split_pre.G2 ++ G₂ := hEqSplits.2.2.2
  have hInner := par_left_inner_eqs (S:=S) (G₁:=G₁) (G₂:=G₂) (G:=G)
    (split_pre:=split_pre) hEq hDisj hDisjG'
  have hDisjG_inner : DisjointG split_pre.G1 (split_pre.G2 ++ G₂) := hInner.1
  have hEq_inner : G = split_pre.G1 ++ (split_pre.G2 ++ G₂) := hInner.2
  have hEq'_inner : G₁_step ++ split.G2 = G₁_step ++ (split_pre.G2 ++ G₂) := by
    simpa [hG2eq]
  exact ⟨hS1eq, hS2eq, hG2eq, hDisjG_inner, hEq_inner, hEq'_inner⟩

/-- Helper: align splits and inner equalities for the right-step par case. -/
private lemma par_right_setup
    {S : SEnv} {G G₁ G₂ : GEnv} {split : ParSplit S G} {split_pre : ParSplit S G₁}
    {nS nG : Nat} :
    split.S1.length = nS →
    split_pre.S1.length = nS →
    split.G1.length = nG →
    split_pre.G1.length = nG →
    G = G₁ ++ G₂ →
    DisjointG G₁ G₂ →
    split.S1 = split_pre.S1 ∧
      split.S2 = split_pre.S2 ∧
      split.G1 = split_pre.G1 ∧
      split.G2 = split_pre.G2 ++ G₂ ∧
      DisjointG split_pre.G1 G₂ ∧
      DisjointG split_pre.G2 G₂ ∧
      G = split_pre.G1 ++ split_pre.G2 ++ G₂ := by
  intro hSlen hSlenPre hGlen hGlenPre hEq hDisj
  have hEqSplits :
      split.S1 = split_pre.S1 ∧ split.S2 = split_pre.S2 ∧
        split.G1 = split_pre.G1 ∧ split.G2 = split_pre.G2 ++ G₂ :=
    par_split_eqs (S:=S) (G:=G) (G₁:=G₁) (G₂:=G₂)
      (split:=split) (split_pre:=split_pre) (nS:=nS) (nG:=nG)
      hSlen hSlenPre hGlen hGlenPre hEq
  have hInner := par_right_inner_eqs (S:=S) (G₁:=G₁) (G₂:=G₂) (G:=G)
    (split_pre:=split_pre) hEq hDisj
  exact ⟨hEqSplits.1, hEqSplits.2.1, hEqSplits.2.2.1, hEqSplits.2.2.2,
    hInner.1, hInner.2.1, hInner.2.2⟩

/-- Helper: rewrite the right-step TypedStep along aligned splits. -/
private lemma par_right_reframe_step
    {G G₁ : GEnv} {D₁ D₂ : DEnv} {Ssh : SEnv} {Sown : OwnedEnv}
    {store store' : VarStore} {bufs bufs' : Buffers} {Q Q' : Process}
    {G₂_step : GEnv} {D₂_step : DEnv} {S₂_step : SEnv}
    {split : ParSplit Sown.left G} {split_pre : ParSplit Sown.left G₁} :
    TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 } store bufs Q
      (split.G1 ++ G₂_step) (D₁ ++ D₂_step)
      { right := Sown.right ++ split.S1, left := S₂_step } store' bufs' Q' →
    split.S1 = split_pre.S1 →
    split.S2 = split_pre.S2 →
    split.G1 = split_pre.G1 →
    TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } store bufs Q
      (split_pre.G1 ++ G₂_step) (D₁ ++ D₂_step)
      { right := Sown.right ++ split_pre.S1, left := S₂_step } store' bufs' Q' := by
  intro hTS hS1eq hS2eq hG1eq
  simpa [hS1eq, hS2eq, hG1eq, List.append_assoc] using hTS

/-- Helper: build the left-par split disjointness. -/
private lemma par_left_disjS_out
    {S₁_step S₁_fin S₂_fin S₂ : SEnv} :
    SEnvDomSubset S₁_step S₁_fin →
    DisjointS S₁_fin S₂ →
    DisjointS S₁_fin S₂_fin →
    DisjointS S₁_step S₂ ∧ DisjointS S₁_step S₂_fin := by
  -- Shrink disjointness via dom-subset.
  intro hDom hDisjS_left hDisjS''
  exact ⟨DisjointS_of_domsubset_left hDom hDisjS_left, DisjointS_of_domsubset_left hDom hDisjS''⟩

/-- Helper: reframe the right-hand pre-out in the left-par case. -/
private lemma par_left_reframe_Q
    {Ssh : SEnv} {Sown : OwnedEnv} {S : SEnv} {G₁ : GEnv} {split_pre : ParSplit S G₁}
    {S₁_step S₂_fin : SEnv} {G₂_fin : GEnv} {W₂ : Footprint} {Δ₂ : DeltaSEnv} {Q : Process} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } split_pre.G2 Q
      { right := Sown.right ++ split_pre.S1, left := S₂_fin } G₂_fin W₂ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₁_step, left := split_pre.S2 } split_pre.G2 Q
      { right := Sown.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ := by
  -- Reframe the right environment across the updated left owned set.
  intro hQ
  exact HasTypeProcPreOut_reframe_right
    (R:=Sown.right ++ split_pre.S1) (R':=Sown.right ++ S₁_step)
    (L:=split_pre.S2) (L':=S₂_fin) (G:=split_pre.G2) (P:=Q) hQ


/-- Helper: build the right-par split disjointness. -/
private lemma par_right_disjS_out
    {S₁ S₂_step S₂_fin S₁_fin : SEnv} :
    SEnvDomSubset S₂_step S₂_fin →
    DisjointS S₁ S₂_fin →
    DisjointS S₁_fin S₂_fin →
    DisjointS S₁ S₂_step ∧ DisjointS S₁_fin S₂_step := by
  -- Shrink disjointness via dom-subset.
  intro hDom hDisjS_right hDisjS''
  exact ⟨DisjointS_of_domsubset_right hDom hDisjS_right, DisjointS_of_domsubset_right hDom hDisjS''⟩

/-- Helper: reframe the left pre-out judgment into the split. -/
private lemma par_left_reframe_P_in
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {G₁ : GEnv}
    {split : ParSplit Sown.left G} {split_pre : ParSplit Sown.left G₁}
    {P : Process} {S₁_fin : SEnv} {G₁_fin : GEnv} {W₁ : Footprint} {Δ₁ : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S2, left := split_pre.S1 } split_pre.G1 P
      { right := Sown.right ++ split_pre.S2, left := S₁_fin } G₁_fin W₁ Δ₁ →
    split.S1 = split_pre.S1 →
    split.S2 = split_pre.S2 →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split_pre.G1 P
      { right := Sown.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
  -- Rewrite the split to match the pre-out judgment.
  intro hP hS1eq hS2eq
  simpa [hS1eq, hS2eq] using hP

/-- Helper: compute the updated left G prefix for par-left. -/
private lemma par_left_update_G1
    {S : SEnv} {G : GEnv} {G₁' G₂ G₁_step : GEnv} {split_pre : ParSplit S G} :
    G₁' ++ G₂ = G₁_step ++ (split_pre.G2 ++ G₂) →
    G₁' = G₁_step ++ split_pre.G2 := by
  -- Cancel the shared right frame.
  intro hEq
  apply append_left_eq_of_eq
  calc
    G₁' ++ G₂ = G₁_step ++ (split_pre.G2 ++ G₂) := hEq
    _ = (G₁_step ++ split_pre.G2) ++ G₂ := by simp [List.append_assoc]

/-- Helper: compute the updated left G prefix for par-right. -/
private lemma par_right_update_G1
    {S : SEnv} {G : GEnv} {G₁' G₂ : GEnv} {split_pre : ParSplit S G} {G₂_step_left : GEnv} :
    G₁' ++ G₂ = split_pre.G1 ++ G₂_step_left ++ G₂ →
    G₁' = split_pre.G1 ++ G₂_step_left := by
  -- Cancel the shared right frame.
  intro hEq
  apply append_left_eq_of_eq
  simpa [List.append_assoc] using hEq

/-- Helper: reframe the left-hand pre-out in the right-par case. -/
private lemma par_right_reframe_P
    {Ssh : SEnv} {Sown : OwnedEnv} {S : SEnv} {G₁ : GEnv} {split_pre : ParSplit S G₁}
    {S₂_step S₁_fin : SEnv} {G₁_fin : GEnv} {W₁ : Footprint} {Δ₁ : DeltaSEnv} {P : Process} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S2, left := split_pre.S1 } split_pre.G1 P
      { right := Sown.right ++ split_pre.S2, left := S₁_fin } G₁_fin W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₂_step, left := split_pre.S1 } split_pre.G1 P
      { right := Sown.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ := by
  -- Reframe the right environment across the updated left owned set.
  intro hP
  exact HasTypeProcPreOut_reframe_right
    (R:=Sown.right ++ split_pre.S2) (R':=Sown.right ++ S₂_step)
    (L:=split_pre.S1) (L':=S₁_fin) (G:=split_pre.G1) (P:=P) hP

/-! ### Left-Frame Helpers (Par Cases) -/

/-- Helper: package the left-par split witness and disjointness after a step. -/
private lemma par_left_splitOut_payload
    {Ssh : SEnv} {Sown : OwnedEnv} {S : SEnv} {G₁ : GEnv} {split_pre : ParSplit S G₁}
    {S₁_step S₁_fin S₂_fin : SEnv} {G₁_step G₁_fin : GEnv} {W₁' : Footprint} {Δ₁' : DeltaSEnv}
    {P' Q : Process} {G₂_fin : GEnv} {W₂ : Footprint} {Δ₂ : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S2, left := S₁_step } G₁_step P'
      { right := Sown.right ++ split_pre.S2, left := S₁_fin } G₁_fin W₁' Δ₁' →
    DisjointG G₁_step split_pre.G2 →
    DisjointS S₁_fin split_pre.S2 →
    DisjointS S₁_fin S₂_fin →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } split_pre.G2 Q
      { right := Sown.right ++ split_pre.S1, left := S₂_fin } G₂_fin W₂ Δ₂ →
    ∃ splitOut : ParSplit (S₁_step ++ split_pre.S2) (G₁_step ++ split_pre.G2),
      splitOut.S1 = S₁_step ∧ splitOut.S2 = split_pre.S2 ∧
      splitOut.G1 = G₁_step ∧ splitOut.G2 = split_pre.G2 ∧
      DisjointG splitOut.G1 splitOut.G2 ∧
      DisjointS splitOut.S1 splitOut.S2 ∧
      DisjointS S₁_fin splitOut.S2 ∧
      DisjointS splitOut.S1 S₂_fin ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P'
        { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁' Δ₁' ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q
        { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
  intro hP' hDisjGOut hDisjS_left hDisjS'' hQ
  let splitOut : ParSplit (S₁_step ++ split_pre.S2) (G₁_step ++ split_pre.G2) :=
    { S1 := S₁_step, S2 := split_pre.S2, G1 := G₁_step, G2 := split_pre.G2, hS := rfl, hG := rfl }
  have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
    simpa [splitOut] using hDisjGOut
  have hDomP := HasTypeProcPreOut_domsubset hP'
  have hDisjS_out0 :
      DisjointS S₁_step split_pre.S2 ∧ DisjointS S₁_step S₂_fin :=
    par_left_disjS_out (S₁_step:=S₁_step) (S₁_fin:=S₁_fin) (S₂_fin:=S₂_fin)
      (S₂:=split_pre.S2) hDomP hDisjS_left hDisjS''
  have hDisjS_left' : DisjointS splitOut.S1 splitOut.S2 := by
    simpa [splitOut] using hDisjS_out0.1
  have hDisjS_left_in : DisjointS S₁_fin splitOut.S2 := by
    simpa [splitOut] using hDisjS_left
  have hDisjS_in_out : DisjointS splitOut.S1 S₂_fin := by
    simpa [splitOut] using hDisjS_out0.2
  have hP_reframe :
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P'
        { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁' Δ₁' := by
    simpa [splitOut] using hP'
  have hQ' :=
    par_left_reframe_Q (Sown:=Sown) (split_pre:=split_pre) (S₁_step:=S₁_step) (S₂_fin:=S₂_fin) hQ
  have hQ_reframe :
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q
        { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
    simpa [splitOut] using hQ'
  exact ⟨splitOut, rfl, rfl, rfl, rfl, hDisjGOut', hDisjS_left', hDisjS_left_in,
    hDisjS_in_out, hP_reframe, hQ_reframe⟩

/-- Helper: package the right-par split witness and disjointness after a step. -/
private lemma par_right_splitOut_payload
    {Ssh : SEnv} {Sown : OwnedEnv} {S : SEnv} {G₁ : GEnv} {split_pre : ParSplit S G₁}
    {S₂_step S₁_fin S₂_fin : SEnv} {G₂_step_left : GEnv}
    {P Q' : Process} {G₁_fin G₂_fin : GEnv} {W₁ : Footprint} {Δ₁ : DeltaSEnv}
    {W₂' : Footprint} {Δ₂' : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S1, left := S₂_step } G₂_step_left Q'
      { right := Sown.right ++ split_pre.S1, left := S₂_fin } G₂_fin W₂' Δ₂' →
    DisjointG split_pre.G1 G₂_step_left →
    DisjointS split_pre.S1 S₂_fin →
    DisjointS S₁_fin S₂_fin →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₂_step, left := split_pre.S1 } split_pre.G1 P
      { right := Sown.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ →
    ∃ splitOut : ParSplit (split_pre.S1 ++ S₂_step) (split_pre.G1 ++ G₂_step_left),
      splitOut.S1 = split_pre.S1 ∧ splitOut.S2 = S₂_step ∧
      splitOut.G1 = split_pre.G1 ∧ splitOut.G2 = G₂_step_left ∧
      DisjointG splitOut.G1 splitOut.G2 ∧
      DisjointS splitOut.S1 splitOut.S2 ∧
      DisjointS splitOut.S1 S₂_fin ∧
      DisjointS S₁_fin splitOut.S2 ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P
        { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁ Δ₁ ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q'
        { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂' Δ₂' := by
  intro hQ' hDisjGOut hDisjS_right hDisjS'' hP
  let splitOut : ParSplit (split_pre.S1 ++ S₂_step) (split_pre.G1 ++ G₂_step_left) :=
    { S1 := split_pre.S1, S2 := S₂_step, G1 := split_pre.G1, G2 := G₂_step_left, hS := rfl, hG := rfl }
  have hDisjGOut' : DisjointG splitOut.G1 splitOut.G2 := by
    simpa [splitOut] using hDisjGOut
  have hDomQ := HasTypeProcPreOut_domsubset hQ'
  have hDisjS_out0 :
      DisjointS split_pre.S1 S₂_step ∧ DisjointS S₁_fin S₂_step :=
    par_right_disjS_out (S₁:=split_pre.S1) (S₂_step:=S₂_step) (S₂_fin:=S₂_fin) (S₁_fin:=S₁_fin)
      hDomQ hDisjS_right hDisjS''
  have hDisjS_right' : DisjointS splitOut.S1 splitOut.S2 := by
    simpa [splitOut] using hDisjS_out0.1
  have hDisjS_right_in : DisjointS splitOut.S1 S₂_fin := by
    simpa [splitOut] using hDisjS_right
  have hDisjS_left_in : DisjointS S₁_fin splitOut.S2 := by
    simpa [splitOut] using hDisjS_out0.2
  have hP_reframe :
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P
        { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
    simpa [splitOut] using hP
  have hQ_reframe :
      HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q'
        { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂' Δ₂' := by
    simpa [splitOut] using hQ'
  exact ⟨splitOut, rfl, rfl, rfl, rfl, hDisjGOut', hDisjS_right', hDisjS_right_in,
    hDisjS_left_in, hP_reframe, hQ_reframe⟩

/-! ### Par Assembly Helpers -/

/-- Helper: assemble a left-step parallel pre-out judgment. -/
private lemma par_left_build_par
    {Ssh : SEnv} {Sown : OwnedEnv} {Sleft : SEnv} {Gleft : GEnv}
    {splitOut : ParSplit Sleft Gleft} {S₁_fin S₂_fin : SEnv} {G₁_fin G₂_fin : GEnv}
    {W₁' W₂ : Footprint} {Δ₁' Δ₂ : DeltaSEnv} {P' Q : Process} {Sfin : OwnedEnv} {Gfin : GEnv} :
    Sfin = { right := Sown.right, left := S₁_fin ++ S₂_fin } →
    Gfin = G₁_fin ++ G₂_fin →
    DisjointG splitOut.G1 splitOut.G2 →
    DisjointS splitOut.S1 splitOut.S2 →
    DisjointS S₁_fin splitOut.S2 →
    DisjointS splitOut.S1 S₂_fin →
    DisjointS S₁_fin S₂_fin →
    DisjointW W₁' W₂ →
    DisjointS Δ₁' Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P'
      { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁' Δ₁' →
    HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q
      { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right, left := Sleft } Gleft
      (.par splitOut.S1.length splitOut.G1.length P' Q)
      Sfin Gfin (W₁' ++ W₂) (Δ₁' ++ Δ₂) := by
  intro hSfin hGfin hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ
  exact HasTypeProcPreOut.par splitOut rfl rfl hSfin hGfin rfl rfl hDisjG hDisjS hDisjS_left hDisjS_right
    hDisjS' hDisjW hDisjΔ rfl rfl hP hQ

/-- Helper: assemble a right-step parallel pre-out judgment. -/
private lemma par_right_build_par
    {Ssh : SEnv} {Sown : OwnedEnv} {Sleft : SEnv} {Gleft : GEnv}
    {splitOut : ParSplit Sleft Gleft} {S₁_fin S₂_fin : SEnv} {G₁_fin G₂_fin : GEnv}
    {W₁ W₂' : Footprint} {Δ₁ Δ₂' : DeltaSEnv} {P Q' : Process} {Sfin : OwnedEnv} {Gfin : GEnv} :
    Sfin = { right := Sown.right, left := S₁_fin ++ S₂_fin } →
    Gfin = G₁_fin ++ G₂_fin →
    DisjointG splitOut.G1 splitOut.G2 →
    DisjointS splitOut.S1 splitOut.S2 →
    DisjointS S₁_fin splitOut.S2 →
    DisjointS splitOut.S1 S₂_fin →
    DisjointS S₁_fin S₂_fin →
    DisjointW W₁ W₂' →
    DisjointS Δ₁ Δ₂' →
    HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S2, left := splitOut.S1 } splitOut.G1 P
      { right := Sown.right ++ splitOut.S2, left := S₁_fin } G₁_fin W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ splitOut.S1, left := splitOut.S2 } splitOut.G2 Q'
      { right := Sown.right ++ splitOut.S1, left := S₂_fin } G₂_fin W₂' Δ₂' →
    HasTypeProcPreOut Ssh { right := Sown.right, left := Sleft } Gleft
      (.par splitOut.S1.length splitOut.G1.length P Q')
      Sfin Gfin (W₁ ++ W₂') (Δ₁ ++ Δ₂') := by
  intro hSfin hGfin hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ
  exact HasTypeProcPreOut.par splitOut rfl rfl hSfin hGfin rfl rfl hDisjG hDisjS hDisjS_left hDisjS_right
    hDisjS' hDisjW hDisjΔ rfl rfl hP hQ

/-! ### Left-Frame Par Cases -/

/-- Helper: package the left-branch IH output and disjointness. -/
private lemma par_left_after_ih
    {Gstore G₁ G₂ G G₁_step : GEnv} {D₁ D₂ D₁_step : DEnv} {Ssh : SEnv} {Sown : OwnedEnv}
    {split : ParSplit Sown.left G} {split_pre : ParSplit Sown.left G₁}
    {S₁_step S₁_fin : SEnv} {G₁_fin : GEnv} {W₁ : Footprint} {Δ₁ : DeltaSEnv}
    {store store' : VarStore} {bufs bufs' : Buffers} {P P' : Process} :
    (ih :
      ∀ {G₁ G₂ G₁' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv},
        StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store →
          DisjointG G₁ G₂ →
            G = G₁ ++ G₂ →
              G₁_step ++ split.G2 = G₁' ++ G₂ →
                HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G₁ P Sfin Gfin W Δ →
                  ∃ W' Δ',
                    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := S₁_step } G₁' P' Sfin Gfin W' Δ' ∧
                      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ) →
    (hStoreL : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store) →
    (hDisjG_inner : DisjointG split_pre.G1 (split_pre.G2 ++ G₂)) →
    (hEq_inner : G = split_pre.G1 ++ (split_pre.G2 ++ G₂)) →
    (hEq'_inner : G₁_step ++ split.G2 = G₁_step ++ (split_pre.G2 ++ G₂)) →
    (hP0 : HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split_pre.G1 P
      { right := Sown.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁) →
    (hDisjG' : DisjointG split_pre.G1 split_pre.G2) →
    (hTS : TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 } store bufs P
      (G₁_step ++ split.G2) (D₁_step ++ D₂) { right := Sown.right ++ split.S2, left := S₁_step } store' bufs' P') →
    ∃ W₁' Δ₁', HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := S₁_step } G₁_step P'
      { right := Sown.right ++ split.S2, left := S₁_fin } G₁_fin W₁' Δ₁' ∧
      FootprintSubset W₁' W₁ ∧ SEnvDomSubset Δ₁' Δ₁ ∧
      DisjointG G₁_step split_pre.G2 := by
  intro ih hStoreL hDisjG_inner hEq_inner hEq'_inner hP0 hDisjG' hTS
  obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ :=
    ih hStoreL hDisjG_inner hEq_inner hEq'_inner hP0
  have hSubG_step : SessionsOf G₁_step ⊆ SessionsOf split_pre.G1 :=
    SessionsOf_subset_of_TypedStep_left_frame hDisjG_inner hEq_inner hEq'_inner hTS
  have hDisjGOut : DisjointG G₁_step split_pre.G2 :=
    DisjointG_of_subset_left hSubG_step hDisjG'
  exact ⟨W₁', Δ₁', hP', hSubW, hSubΔ, hDisjGOut⟩

/-- Helper: package the right-branch middle-frame output and disjointness. -/
private lemma par_right_middle_data
    {Gstore G₁ G₂ G : GEnv} {D₁ D₂ D₂_step : DEnv} {Ssh : SEnv} {Sown : OwnedEnv}
    {split_pre : ParSplit Sown.left G₁} {store : VarStore} {bufs : Buffers}
    {Q Q' : Process} {S₂_step S₂_fin : SEnv} {G₂_fin : GEnv} {W₂ : Footprint} {Δ₂ : DeltaSEnv}
    {G₂_step : GEnv} {store' : VarStore} {bufs' : Buffers} :
    (hStoreR' : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 }) store) →
    (hDisjG_pre : DisjointG split_pre.G1 split_pre.G2) →
    (hDisjG1G2 : DisjointG split_pre.G1 G₂) →
    (hDisjG2G2 : DisjointG split_pre.G2 G₂) →
    (hEq_inner : G = split_pre.G1 ++ split_pre.G2 ++ G₂) →
    (hTS' : TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } store bufs Q
      (split_pre.G1 ++ G₂_step) (D₁ ++ D₂_step) { right := Sown.right ++ split_pre.S1, left := S₂_step } store' bufs' Q') →
    (hQ : HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } split_pre.G2 Q
      { right := Sown.right ++ split_pre.S1, left := S₂_fin } G₂_fin W₂ Δ₂) →
    ∃ G₂_step_left W₂' Δ₂',
      split_pre.G1 ++ G₂_step = split_pre.G1 ++ G₂_step_left ++ G₂ ∧
      DisjointG split_pre.G1 G₂_step_left ∧
      HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S1, left := S₂_step } G₂_step_left Q'
        { right := Sown.right ++ split_pre.S1, left := S₂_fin } G₂_fin W₂' Δ₂' ∧
      FootprintSubset W₂' W₂ ∧ SEnvDomSubset Δ₂' Δ₂ := by
  intro hStoreR' hDisjG_pre hDisjG1G2 hDisjG2G2 hEq_inner hTS' hQ
  obtain ⟨G₂_step_left, W₂', Δ₂', hEqG', hSubSess, hQ', hSubW, hSubΔ⟩ :=
    HasTypeProcPreOut_preserved_sub_middle_frame
      (Gstore:=Gstore) (Gleft:=split_pre.G1) (Gmid:=split_pre.G2) (Gright:=G₂)
      (G:=G) (G':=split_pre.G1 ++ G₂_step)
      (D:=D₁ ++ D₂) (Ssh:=Ssh)
      (Sown:={ right := Sown.right ++ split_pre.S1, left := split_pre.S2 })
      (store:=store) (bufs:=bufs) (P:=Q)
      (Sfin:={ right := Sown.right ++ split_pre.S1, left := S₂_fin }) (Gfin:=G₂_fin) (W:=W₂) (Δ:=Δ₂)
      hStoreR' hDisjG_pre hDisjG1G2 hDisjG2G2 hEq_inner hTS' hQ
  have hDisjGsym : DisjointG split_pre.G2 split_pre.G1 := DisjointG_symm hDisjG_pre
  have hDisjG_step_left : DisjointG G₂_step_left split_pre.G1 :=
    DisjointG_of_subset_left hSubSess hDisjGsym
  have hDisjGOut : DisjointG split_pre.G1 G₂_step_left := DisjointG_symm hDisjG_step_left
  exact ⟨G₂_step_left, W₂', Δ₂', hEqG', hDisjGOut, hQ', hSubW, hSubΔ⟩

/-- Helper: par-left case for the left-frame preservation lemma. -/
lemma preserved_sub_left_frame_par_left
    {Gstore G₁ G₂ G G₁' D₁ D₂ G₁_step D₁_step S₁_step Ssh Sown store bufs store' bufs' P P' Q
      Sfin Gfin W Δ nS nG} :
    (split : ParSplit Sown.left G) →
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    G₁_step ++ split.G2 = G₁' ++ G₂ →
    split.S1.length = nS →
    split.G1.length = nG →
    TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 } store bufs P
      (G₁_step ++ split.G2) (D₁_step ++ D₂) { right := Sown.right ++ split.S2, left := S₁_step } store' bufs' P' →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    (∀ {G₁ G₂ G₁' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv},
      StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store →
        DisjointG G₁ G₂ →
          G = G₁ ++ G₂ →
            G₁_step ++ split.G2 = G₁' ++ G₂ →
              HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } G₁ P Sfin Gfin W Δ →
                ∃ W' Δ',
                  HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := S₁_step } G₁' P' Sfin Gfin W' Δ' ∧
                    FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ) →
    HasTypeProcPreOut Ssh Sown G₁ (.par nS nG P Q) Sfin Gfin W Δ →
    ∃ W' Δ',
      HasTypeProcPreOut Ssh { right := Sown.right, left := S₁_step ++ split.S2 } G₁'
        (.par S₁_step.length G₁_step.length P' Q) Sfin Gfin W' Δ' ∧
        FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro split hStoreL hDisj hEq hEq' hSlen hGlen hTS hDisjG hDisjS ih hPre
  cases hPre with
  | par split_pre hSlenPre hGlenPre hSfin hGfin hW hΔ
      hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
      rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
      subst hS1; subst hS2
      obtain ⟨hS1eq, hS2eq, hG2eq, hDisjG_inner, hEq_inner, hEq'_inner⟩ :=
        par_left_setup (S:=Sown.left) (G:=G) (G₁:=G₁) (G₂:=G₂)
          (split:=split) (split_pre:=split_pre) (G₁_step:=G₁_step) (nS:=nS) (nG:=nG)
          hSlen hSlenPre hGlen hGlenPre hEq hDisj hDisjG'
      have hP0 :=
        par_left_reframe_P_in (Sown:=Sown) (split:=split) (split_pre:=split_pre) (P:=P) (S₁_fin:=S₁_fin)
          (G₁_fin:=G₁_fin) (W₁:=W₁) (Δ₁:=Δ₁) hP hS1eq hS2eq
      obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ, hDisjGOut⟩ :=
        par_left_after_ih (ih:=ih) (hStoreL:=hStoreL) (hDisjG_inner:=hDisjG_inner)
          (hEq_inner:=hEq_inner) (hEq'_inner:=hEq'_inner) (hP0:=hP0) (hDisjG':=hDisjG') (hTS:=hTS)
      have hP'' :
          HasTypeProcPreOut Ssh { right := Sown.right ++ split_pre.S2, left := S₁_step } G₁_step P'
            { right := Sown.right ++ split_pre.S2, left := S₁_fin } G₁_fin W₁' Δ₁' := by
        simpa [hS2eq] using hP'
      obtain ⟨splitOut, hS1out, hS2out, hG1out, hG2out, hDisjGOut', hDisjS_left', hDisjS_left_in,
          hDisjS_in_out, hP_reframe, hQ_reframe⟩ :=
        par_left_splitOut_payload (Sown:=Sown) (split_pre:=split_pre)
          (S₁_step:=S₁_step) (S₁_fin:=S₁_fin) (S₂_fin:=S₂_fin)
          (G₁_step:=G₁_step) (G₁_fin:=G₁_fin) (P':=P') (Q:=Q)
          (G₂_fin:=G₂_fin) (W₂:=W₂) (Δ₂:=Δ₂)
          hP'' hDisjGOut hDisjS_left hDisjS'' hQ
      have hDisjW' : DisjointW W₁' W₂ :=
        DisjointW_of_subset_left hSubW hDisjW
      have hDisjΔ' : DisjointS Δ₁' Δ₂ :=
        DisjointS_of_domsubset_left hSubΔ hDisjΔ
      have hG₁' : G₁' = G₁_step ++ split_pre.G2 := by
        refine par_left_update_G1 (S:=Sown.left) (G:=G₁) (G₂:=G₂) (split_pre:=split_pre) ?_
        calc
          G₁' ++ G₂ = G₁_step ++ split.G2 := by simpa using hEq'.symm
          _ = G₁_step ++ (split_pre.G2 ++ G₂) := by simpa [hG2eq]
      refine ⟨W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, ?_, ?_⟩
      ·
        have hPar :=
          par_left_build_par (splitOut:=splitOut) (Sfin:=Sfin) (Gfin:=Gfin)
            hSfin hGfin hDisjGOut' hDisjS_left' hDisjS_left_in
            hDisjS_in_out hDisjS'' hDisjW' hDisjΔ' hP_reframe hQ_reframe
        simpa [hS1out, hS2out, hS2eq, hG1out, hG2out, hG₁'] using hPar
      · simpa [hW] using (FootprintSubset_append_left hSubW)
      · simpa [hΔ] using (SEnvDomSubset_append_left_of_domsubset hSubΔ)

/-- Helper: par-right case for the left-frame preservation lemma. -/
lemma preserved_sub_left_frame_par_right
    {Gstore G₁ G₂ G G₁' D₁ D₂ G₂_step D₂_step S₂_step Ssh Sown store bufs store' bufs' P Q Q'
      Sfin Gfin W Δ nS nG} :
    (split : ParSplit Sown.left G) →
    StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store →
    DisjointG G₁ G₂ →
    G = G₁ ++ G₂ →
    split.G1 ++ G₂_step = G₁' ++ G₂ →
    split.S1.length = nS →
    split.G1.length = nG →
    TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 } store bufs Q
      (split.G1 ++ G₂_step) (D₁ ++ D₂_step) { right := Sown.right ++ split.S1, left := S₂_step } store' bufs' Q' →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    (∀ {G₁ G₂ G₁' : GEnv} {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv},
      StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store →
        DisjointG G₁ G₂ →
          G = G₁ ++ G₂ →
            split.G1 ++ G₂_step = G₁' ++ G₂ →
              HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } G₁ Q Sfin Gfin W Δ →
                ∃ W' Δ',
                  HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := S₂_step } G₁' Q' Sfin Gfin W' Δ' ∧
                    FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ) →
    HasTypeProcPreOut Ssh Sown G₁ (.par nS nG P Q) Sfin Gfin W Δ →
    ∃ W' Δ',
      HasTypeProcPreOut Ssh { right := Sown.right, left := split.S1 ++ S₂_step } G₁'
        (.par split.S1.length split.G1.length P Q') Sfin Gfin W' Δ' ∧
        FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro split hStoreR hDisj hEq hEq' hSlen hGlen hTS hDisjG hDisjS ih hPre
  cases hPre with
  | par split_pre hSlenPre hGlenPre hSfin hGfin hW hΔ
      hDisjG_pre hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
      rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
      subst hS1; subst hS2
      obtain ⟨hS1eq, hS2eq, hG1eq, hG2eq, hDisjG1G2, hDisjG2G2, hEq_inner⟩ :=
        par_right_setup (S:=Sown.left) (G:=G) (G₁:=G₁) (G₂:=G₂)
          (split:=split) (split_pre:=split_pre) (nS:=nS) (nG:=nG)
          hSlen hSlenPre hGlen hGlenPre hEq hDisj
      have hTS' :
          TypedStep G (D₁ ++ D₂) Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 } store bufs Q
            (split_pre.G1 ++ G₂_step) (D₁ ++ D₂_step)
            { right := Sown.right ++ split_pre.S1, left := S₂_step } store' bufs' Q' :=
        par_right_reframe_step (split:=split) (split_pre:=split_pre) hTS hS1eq hS2eq hG1eq
      have hStoreR' :
          StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split_pre.S1, left := split_pre.S2 }) store := by
        simpa [hS1eq, hS2eq] using hStoreR
      obtain ⟨G₂_step_left, W₂', Δ₂', hEqG', hDisjGOut, hQ', hSubW, hSubΔ⟩ :=
        par_right_middle_data (hStoreR':=hStoreR') (hDisjG_pre:=hDisjG_pre) (hDisjG1G2:=hDisjG1G2)
          (hDisjG2G2:=hDisjG2G2) (hEq_inner:=hEq_inner) (hTS':=hTS') (hQ:=hQ)
      have hP_reframe :=
        par_right_reframe_P (Sown:=Sown) (split_pre:=split_pre) (S₂_step:=S₂_step) (S₁_fin:=S₁_fin) hP
      obtain ⟨splitOut, hS1out, hS2out, hG1out, hG2out, hDisjGOut', hDisjS_right', hDisjS_right_in,
          hDisjS_left_in, hP_reframe', hQ_reframe⟩ :=
        par_right_splitOut_payload (Sown:=Sown) (split_pre:=split_pre)
          (S₂_step:=S₂_step) (S₁_fin:=S₁_fin) (S₂_fin:=S₂_fin)
          (G₂_step_left:=G₂_step_left) (P:=P) (Q':=Q') (G₁_fin:=G₁_fin) (G₂_fin:=G₂_fin)
          (W₁:=W₁) (Δ₁:=Δ₁) (W₂':=W₂') (Δ₂':=Δ₂')
          hQ' hDisjGOut hDisjS_right hDisjS'' hP_reframe
      have hDisjW' : DisjointW W₁ W₂' :=
        DisjointW_of_subset_right hSubW hDisjW
      have hDisjΔ' : DisjointS Δ₁ Δ₂' :=
        DisjointS_of_domsubset_right hSubΔ hDisjΔ
      have hEq'_inner : split_pre.G1 ++ G₂_step = G₁' ++ G₂ := by
        have hEq'0 : split.G1 ++ G₂_step = G₁' ++ G₂ := by
          simpa using hEq'
        simpa [hG1eq] using hEq'0
      have hG₁' : G₁' = split_pre.G1 ++ G₂_step_left := by
        refine par_right_update_G1 (S:=Sown.left) (G:=G₁) (G₂:=G₂) (split_pre:=split_pre) ?_
        calc
          G₁' ++ G₂ = split_pre.G1 ++ G₂_step := by simpa using hEq'_inner.symm
          _ = split_pre.G1 ++ G₂_step_left ++ G₂ := hEqG'
      refine ⟨W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, ?_, ?_⟩
      ·
        have hPar :=
          par_right_build_par (splitOut:=splitOut) (Sfin:=Sfin) (Gfin:=Gfin)
            hSfin hGfin hDisjGOut' hDisjS_right' hDisjS_left_in
            hDisjS_right_in hDisjS'' hDisjW' hDisjΔ' hP_reframe' hQ_reframe
        simpa [hS1out, hS2out, hS1eq, hG1eq, hG1out, hG2out, hG₁'] using hPar
      · simpa [hW] using (FootprintSubset_append_right_of_subset hSubW)
      · simpa [hΔ] using (SEnvDomSubset_append_right_of_domsubset hSubΔ)
