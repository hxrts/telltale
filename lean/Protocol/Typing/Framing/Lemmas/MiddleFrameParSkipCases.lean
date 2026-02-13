import Protocol.Typing.Framing.Lemmas.MiddleFrameCases

/-! # Middle Frame `par_skip` Cases

`par_skip_left` and `par_skip_right` branches extracted from the main
middle-frame induction to keep the main theorem module focused and below
the style-guide size threshold.
-/

/-
The Problem. The `par_skip_left` and `par_skip_right` branches in the
middle-frame proof are self-contained but lengthy, pushing the main theorem
module past the size cap.

Solution Structure. Extract those two branches into dedicated lemmas that
preserve the same hypotheses/conclusions, then call them from
`MiddleFrameMain`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Extracted `par_skip` Branches

lemma preserved_sub_middle_par_skip_left
    {Gleft Gmid Gright G Ssh Sown Q nS nG Sfin Gfin W Δ}
    (hOwn : OwnedDisjoint Sown)
    (hEqG : G = Gleft ++ Gmid ++ Gright)
    (hDisjRightFin : DisjointS Sown.right Sfin.left)
    (hPre : HasTypeProcPreOut Ssh Sown Gmid (.par nS nG .skip Q) Sfin Gfin W Δ)
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
    (hS1Nil : split.S1 = ([] : SEnv)) :
    ∃ Gmid' W' Δ',
      G = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' Q Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧
      SEnvDomSubset Δ' Δ := by
  -- `par_skip_left`: Invert Parallel Witness
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
      hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
    HasTypeProcPreOut_par_inv_witness hPre
  let splitMid : ParSplit Sown.left Gmid := pw.split
  have hSlenEq : split.S1.length = splitMid.S1.length := by
    calc
      split.S1.length = nS := hSlen
      _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
  have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
  have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
  have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
  have hS1MidNil : splitMid.S1 = ([] : SEnv) := by
    simpa [hS1Eq] using hS1Nil
  have hSownLeftEq : Sown.left = splitMid.S2 := by
    have hSownSplit : Sown.left = splitMid.S1 ++ splitMid.S2 := by
      simpa [splitMid] using splitMid.hS
    simpa [hS1MidNil] using hSownSplit
  cases hP_pre
  simp at hS1MidNil
  -- `par_skip_left`: Reframe Surviving Branch
  have hQ0 :
      HasTypeProcPreOut Ssh Sown splitMid.G2 Q
        { right := Sown.right, left := S₂_fin } G₂_fin W₂ Δ₂ := by
    cases Sown with
    | mk R L =>
        simp at hSownLeftEq
        simpa [splitMid, hSownLeftEq, hS1MidNil, List.nil_append] using hQ_pre
  have hDisjRightIn0 : DisjointS Sown.right Sown.left := by
    simpa [OwnedDisjoint] using hOwn
  have hDisjRightOut0 : DisjointS Sown.right S₂_fin := by
    have hTmp : DisjointS Sown.right (splitMid.S1 ++ S₂_fin) := by
      simpa [hSfin] using hDisjRightFin
    simpa [hS1MidNil] using hTmp
  have hQfull :
      HasTypeProcPreOut Ssh Sown Gmid Q
        { right := Sown.right, left := S₂_fin } (splitMid.G1 ++ G₂_fin) W₂ Δ₂ := by
    have hTmp :=
      HasTypeProcPreOut_frame_G_left_local
        (Ssh:=Ssh) (Sown:=Sown) (Gfr:=splitMid.G1) (G:=splitMid.G2)
        (P:=Q) (Sfin:={ right := Sown.right, left := S₂_fin }) (Gfin:=G₂_fin)
        (W:=W₂) (Δ:=Δ₂) hDisjG_mid hDisjRightIn0 hQ0 hDisjRightOut0
    simpa [splitMid, splitMid.hG, List.append_assoc] using hTmp
  have hSfinQ : Sfin = { right := Sown.right, left := S₂_fin } := by
    calc
      Sfin = { right := Sown.right, left := splitMid.S1 ++ S₂_fin } := by
        simpa [splitMid] using hSfin
      _ = { right := Sown.right, left := S₂_fin } := by
        simp [hS1MidNil]
  have hGfinQ : Gfin = splitMid.G1 ++ G₂_fin := by
    simpa [splitMid] using hGfin
  have hWQ : W = W₂ := by
    simpa using hW
  have hΔQ : Δ = Δ₂ := by
    simpa using hΔ
  -- `par_skip_left`: Package Subgoal
  refine ⟨Gmid, W₂, Δ₂, hEqG, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hs
  · simpa [hSfinQ, hGfinQ] using hQfull
  · simpa [hWQ] using (FootprintSubset_refl (W:=W₂))
  · simpa [hΔQ] using (SEnvDomSubset_refl (S:=Δ₂))

-- `par_skip_right` Branch

lemma preserved_sub_middle_par_skip_right
    {Gleft Gmid Gright G Ssh Sown P nS nG Sfin Gfin W Δ}
    (hOwn : OwnedDisjoint Sown)
    (hEqG : G = Gleft ++ Gmid ++ Gright)
    (hDisjRightFin : DisjointS Sown.right Sfin.left)
    (hPre : HasTypeProcPreOut Ssh Sown Gmid (.par nS nG P .skip) Sfin Gfin W Δ)
    (split : ParSplit Sown.left G)
    (hSlen : split.S1.length = nS)
    (hS2Nil : split.S2 = ([] : SEnv)) :
    ∃ Gmid' W' Δ',
      G = Gleft ++ Gmid' ++ Gright ∧
      SessionsOf Gmid' ⊆ SessionsOf Gmid ∧
      HasTypeProcPreOut Ssh Sown Gmid' P Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧
      SEnvDomSubset Δ' Δ := by
  -- `par_skip_right`: Invert Parallel Witness
  obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
      hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
      hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
    HasTypeProcPreOut_par_inv_witness hPre
  let splitMid : ParSplit Sown.left Gmid := pw.split
  have hSlenEq : split.S1.length = splitMid.S1.length := by
    calc
      split.S1.length = nS := hSlen
      _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
  have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
  have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
  have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
  have hS2MidNil : splitMid.S2 = ([] : SEnv) := by
    simpa [hS2Eq] using hS2Nil
  have hSownLeftEq : Sown.left = splitMid.S1 := by
    have hSownSplit : Sown.left = splitMid.S1 ++ splitMid.S2 := by
      simpa [splitMid] using splitMid.hS
    simpa [hS2MidNil] using hSownSplit
  cases hQ_pre
  simp at hS2MidNil
  -- `par_skip_right`: Reframe Surviving Branch
  have hP0 :
      HasTypeProcPreOut Ssh Sown splitMid.G1 P
        { right := Sown.right, left := S₁_fin } G₁_fin W₁ Δ₁ := by
    cases Sown with
    | mk R L =>
        simp at hSownLeftEq
        simpa [splitMid, hSownLeftEq, hS2MidNil, List.append_nil] using hP_pre
  have hPfull :
      HasTypeProcPreOut Ssh Sown Gmid P
        { right := Sown.right, left := S₁_fin } (G₁_fin ++ splitMid.G2) W₁ Δ₁ := by
    have hTmp :=
      HasTypeProcPreOut_frame_G_right_local
        (Ssh:=Ssh) (Sown:=Sown) (G:=splitMid.G1) (Gfr:=splitMid.G2)
        (P:=P) (Sfin:={ right := Sown.right, left := S₁_fin }) (Gfin:=G₁_fin)
        (W:=W₁) (Δ:=Δ₁) hDisjG_mid hP0
    simpa [splitMid, splitMid.hG, List.append_assoc] using hTmp
  have hSfinP : Sfin = { right := Sown.right, left := S₁_fin } := by
    calc
      Sfin = { right := Sown.right, left := S₁_fin ++ splitMid.S2 } := by
        simpa [splitMid] using hSfin
      _ = { right := Sown.right, left := S₁_fin } := by
        simp [hS2MidNil]
  have hGfinP : Gfin = G₁_fin ++ splitMid.G2 := by
    simpa [splitMid] using hGfin
  have hWP : W = W₁ := by
    simpa using hW
  have hΔP : Δ = Δ₁ := by
    simpa using hΔ
  -- `par_skip_right`: Package Subgoal
  refine ⟨Gmid, W₁, Δ₁, hEqG, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hs
  · simpa [hSfinP, hGfinP] using hPfull
  · simpa [hWP] using (FootprintSubset_refl (W:=W₁))
  · simpa [hΔP] using (SEnvDomSubset_refl (S:=Δ₁))

end
