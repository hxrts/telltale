import Protocol.Typing.Framing.Lemmas.MiddleFrameCases
import Protocol.Typing.Framing.Lemmas.MiddleFrameParSkipCases

/-! # Middle Frame Main Theorem

Main proof of the middle-frame preservation theorem, combining all
per-constructor cases into a complete induction on `TypedStep`. -/

/-
The Problem. The middle-frame specification requires proving that any
`TypedStep` in a three-way split `G = Gleft ++ Gmid ++ Gright` preserves
the structure: the step produces `G' = Gleft ++ Gmid' ++ Gright` with
appropriate subset and typing properties.

Solution Structure. Prove `HasTypeProcPreOut_preserved_sub_middle_frame`
by induction on `TypedStep`. Dispatch each constructor to its case lemma
from `MiddleFrameCases`. Handle recursive cases (seq, par) by invoking
the induction hypothesis.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Main Theorem

theorem HasTypeProcPreOut_preserved_sub_middle_frame :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec := by
  intro Gstore Gleft Gmid Gright G D Ssh Sown store bufs P
    G' D' Sown' store' bufs' P' Sfin Gfin W Δ
    hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR hEqG hTS hDisjRightFin hPre
  induction hTS generalizing Gstore Gleft Gmid Gright Sfin Gfin W Δ with
  -- Communication Constructors
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      exact preserved_sub_middle_send hStore hOwn hDisjLM hEqG hk hG hGout
        (TypedStep.send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut) hPre
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      exact preserved_sub_middle_recv hStore hOwn hDisjLM hEqG hk hG hGout hSout
        (TypedStep.recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut) hPre
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      exact preserved_sub_middle_select hStore hOwn hDisjLM hEqG hk hG hFind hGout
        (TypedStep.select hk hG hFind hReady hEdge hGout hDout hBufsOut) hPre
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      exact preserved_sub_middle_branch hStore hOwn hDisjLM hEqG hk hG hFindP hFindT hGout
        (TypedStep.branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut) hPre
  -- Assignment Constructor
  | assign hv hSout hStoreOut =>
      rename_i G D Ssh Sown store bufs x v Tstep Sown' store'
      exact preserved_sub_middle_assign
        (D:=D) (bufs:=bufs) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (G':=G) (Ssh:=Ssh) (Sown:=Sown) (Sown':=Sown')
        (store:=store) (store':=store') (x:=x) (v:=v) (Tstep:=Tstep)
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hDisjLM hEqG rfl hSout hv
        (TypedStep.assign (D:=D) (bufs:=bufs) hv hSout hStoreOut) hPre
  -- Sequential Constructors
  | seq_step hStep ih =>
      rename_i G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q
      have hMiddle : MiddleFrameGoal (hTS := hStep) := by
        intro Gstore0 Gleft0 Gmid0 Gright0 Sfin0 Gfin0 W0 Δ0
          hStore0 hDisjSh0 hOwn0 hDisjLM0 hDisjLR0 hDisjMR0 hEqG0 hDisjRight0 hPre0
        exact ih hStore0 hDisjSh0 hOwn0 hDisjLM0 hDisjLR0 hDisjMR0 hEqG0 hDisjRight0 hPre0
      exact preserved_sub_middle_seq_step hStore hDisjShAll hOwn hDisjLM hDisjLR hDisjMR
        hEqG hStep hMiddle hDisjRightFin hPre
  | seq_skip =>
      rename_i G D Ssh Sown store bufs Q
      exact preserved_sub_middle_seq_skip
        (D:=D) (store:=store) (bufs:=bufs) (Gleft:=Gleft) (Gmid:=Gmid) (Gright:=Gright)
        (G:=G) (Ssh:=Ssh) (Sown:=Sown) (Q:=Q)
        (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
        hEqG (TypedStep.seq_skip (D:=D) (store:=store) (bufs:=bufs) (Q:=Q)) hPre
  -- Parallel-Left Constructor
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 P0' Q0
        G0 D₁0 D₂0 G₁_step D₁_step S₁_step nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      -- `par_left`: Build Inner Framing Context
      have hStoreInner :
          StoreTyped Gstore (SEnvAll Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 }) store0 :=
        StoreTyped_par_left_inner (split:=split) hDisjS hStore
      have hShAll :
          DisjointS Ssh0 (Sown0.right ++ (split.S1 ++ split.S2)) := by
        simpa [OwnedEnv.all, split.hS, List.append_assoc] using hDisjShAll
      have hShR : DisjointS Ssh0 Sown0.right := DisjointS_of_append_left hShAll
      have hSh12 : DisjointS Ssh0 (split.S1 ++ split.S2) := DisjointS_of_append_right hShAll
      have hShS1 : DisjointS Ssh0 split.S1 := DisjointS_of_append_left hSh12
      have hShS2 : DisjointS Ssh0 split.S2 := DisjointS_of_append_right hSh12
      have hDisjShInner :
          DisjointS Ssh0 ({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) := by
        have hTmp : DisjointS Ssh0 ((Sown0.right ++ split.S2) ++ split.S1) :=
          DisjointS_append_right (DisjointS_append_right hShR hShS2) hShS1
        simpa [OwnedEnv.all, List.append_assoc] using hTmp
      have hOwnAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwn
      have hDisjRightS1 : DisjointS Sown0.right split.S1 := DisjointS_of_append_left hOwnAll
      have hDisjRightS2 : DisjointS Sown0.right split.S2 := DisjointS_of_append_right hOwnAll
      have hOwnInner :
          OwnedDisjoint ({ right := Sown0.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
      -- `par_left`: Session/Disjointness Projections
      have hSubG1 : SessionsOf splitMid.G1 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hSubG2 : SessionsOf splitMid.G2 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hDisjLeftG1 : DisjointG Gleft splitMid.G1 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
        exact DisjointG_symm hTmp
      have hDisjLeftG2 : DisjointG Gleft splitMid.G2 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
        exact DisjointG_symm hTmp
      have hDisjG1Right : DisjointG splitMid.G1 Gright := DisjointG_of_subset_left hSubG1 hDisjMR
      have hDisjLeftRightInner : DisjointG Gleft (splitMid.G2 ++ Gright) :=
        DisjointG_append_right hDisjLeftG2 hDisjLR
      have hDisjMidRightInner : DisjointG splitMid.G1 (splitMid.G2 ++ Gright) :=
        DisjointG_append_right hDisjG_mid hDisjG1Right
      have hEqInner : G0 = Gleft ++ splitMid.G1 ++ (splitMid.G2 ++ Gright) := by
        calc
          G0 = Gleft ++ Gmid ++ Gright := hEqG
          _ = Gleft ++ (splitMid.G1 ++ splitMid.G2) ++ Gright := by
                simpa [splitMid, splitMid.hG]
          _ = Gleft ++ splitMid.G1 ++ (splitMid.G2 ++ Gright) := by
                simp [List.append_assoc]
      have hDisjS_left : DisjointS S₁_fin split.S2 := by
        simpa [splitMid, hS2Eq] using hDisjS_left_mid
      have hDisjRightFinAll : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS1Fin : DisjointS Sown0.right S₁_fin :=
        DisjointS_of_append_left hDisjRightFinAll
      have hDisjOutP : DisjointS (Sown0.right ++ split.S2) S₁_fin :=
        DisjointS_append_left hDisjRightS1Fin (DisjointS_symm hDisjS_left)
      have hP0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } splitMid.G1 P0
            { right := Sown0.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hP_pre
      -- `par_left`: Apply IH On Left Branch
      obtain ⟨G₁_mid', W₁', Δ₁', hEqShape, hSubSess1, hP', hSubW1, hSubΔ1⟩ :=
        ih (Gstore:=Gstore) (Gleft:=Gleft) (Gmid:=splitMid.G1) (Gright:=splitMid.G2 ++ Gright)
          (Sfin:={ right := Sown0.right ++ split.S2, left := S₁_fin })
          (Gfin:=G₁_fin) (W:=W₁) (Δ:=Δ₁)
          hStoreInner hDisjShInner hOwnInner hDisjLeftG1 hDisjLeftRightInner hDisjMidRightInner
          hEqInner hDisjOutP hP0
      have hDomStep : SEnvDomSubset S₁_step S₁_fin := by
        simpa using (HasTypeProcPreOut_domsubset hP')
      have hStepS2 : DisjointS S₁_step split.S2 := by
        have hTmp : DisjointS split.S2 S₁_step :=
          DisjointS_of_domsubset_right hDomStep (DisjointS_symm hDisjS_left)
        exact DisjointS_symm hTmp
      have hStepS2fin : DisjointS S₁_step S₂_fin := by
        have hTmp : DisjointS S₂_fin S₁_step :=
          DisjointS_of_domsubset_right hDomStep (DisjointS_symm hDisjS_fin)
        exact DisjointS_symm hTmp
      have hDisjRightS2Fin : DisjointS Sown0.right S₂_fin :=
        DisjointS_of_append_right hDisjRightFinAll
      have hDisjInQNew : DisjointS (Sown0.right ++ S₁_step) split.S2 :=
        DisjointS_append_left hDisjRightS2 hStepS2
      have hDisjOutQNew : DisjointS (Sown0.right ++ S₁_step) S₂_fin :=
        DisjointS_append_left hDisjRightS2Fin hStepS2fin
      have hQ0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ split.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hQ_pre
      have hQ1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₁_step, left := splitMid.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        have hTmp :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₁_step, left := split.S2 } splitMid.G2 Q0
              { right := Sown0.right ++ S₁_step, left := S₂_fin } G₂_fin W₂ Δ₂ :=
          HasTypeProcPreOut_reframe_right
            (R:=Sown0.right ++ split.S1) (R':=Sown0.right ++ S₁_step)
            (L:=split.S2) (L':=S₂_fin) (G:=splitMid.G2) (P:=Q0)
            hDisjInQNew hDisjOutQNew hQ0
        simpa [splitMid, hS2Eq] using hTmp
      -- `par_left`: Reconstruct Combined Result
      have hP1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ splitMid.S2, left := S₁_step } G₁_mid' P0'
            { right := Sown0.right ++ splitMid.S2, left := S₁_fin } G₁_fin W₁' Δ₁' := by
        simpa [splitMid, hS2Eq] using hP'
      -- `par_left`: Final Packing And Subsets
      have hDisjGFinal : DisjointG G₁_mid' splitMid.G2 :=
        DisjointG_of_subset_left hSubSess1 hDisjG_mid
      have hStepS2mid : DisjointS S₁_step splitMid.S2 := by
        simpa [splitMid, hS2Eq] using hStepS2
      have hDisjS1FinS2 : DisjointS S₁_fin splitMid.S2 := by
        simpa [splitMid] using hDisjS_left_mid
      have hDisjW' : DisjointW W₁' W₂ := DisjointW_of_subset_left hSubW1 hDisjW
      have hDisjΔ' : DisjointS Δ₁' Δ₂ := DisjointS_of_domsubset_left hSubΔ1 hDisjΔ
      let splitOut : ParSplit ({ right := Sown0.right, left := S₁_step ++ splitMid.S2 } : OwnedEnv).left
          (G₁_mid' ++ splitMid.G2) :=
        { S1 := S₁_step
          S2 := splitMid.S2
          G1 := G₁_mid'
          G2 := splitMid.G2
          hS := rfl
          hG := rfl }
      have hParMid :
          HasTypeProcPreOut Ssh0 { right := Sown0.right, left := S₁_step ++ splitMid.S2 }
            (G₁_mid' ++ splitMid.G2) (.par S₁_step.length nG0 P0' Q0)
            Sfin Gfin (W₁' ++ W₂) (Δ₁' ++ Δ₂) :=
        HasTypeProcPreOut.par splitOut rfl hSfin hGfin rfl rfl
          hDisjGFinal hStepS2mid hDisjS1FinS2 hStepS2fin hDisjS_fin hDisjW' hDisjΔ'
          hP1 hQ1
      have hEqGFinal : G₁_step ++ split.G2 = Gleft ++ (G₁_mid' ++ splitMid.G2) ++ Gright := by
        simpa [List.append_assoc] using hEqShape
      have hSubSessFinal : SessionsOf (G₁_mid' ++ splitMid.G2) ⊆ SessionsOf Gmid := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=G₁_mid') (G₂:=splitMid.G2) hs
        cases hs' with
        | inl hsL =>
            have hsMid1 : s ∈ SessionsOf splitMid.G1 := hSubSess1 hsL
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsMid1)
        | inr hsR =>
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsR)
      have hSubWFinal : FootprintSubset (W₁' ++ W₂) W := by
        have hSubW12 : FootprintSubset (W₁' ++ W₂) (W₁ ++ W₂) :=
          FootprintSubset_append_left hSubW1
        simpa [hW] using hSubW12
      have hSubΔFinal : SEnvDomSubset (Δ₁' ++ Δ₂) Δ := by
        have hSubΔ12 : SEnvDomSubset (Δ₁' ++ Δ₂) (Δ₁ ++ Δ₂) :=
          SEnvDomSubset_append_left_of_domsubset hSubΔ1
        simpa [hΔ] using hSubΔ12
      refine ⟨G₁_mid' ++ splitMid.G2, W₁' ++ W₂, Δ₁' ++ Δ₂, ?_, hSubSessFinal, ?_, hSubWFinal, hSubΔFinal⟩
      · simpa [hEqGFinal]
      · simpa [splitMid, hS2Eq, List.append_assoc] using hParMid
  -- Parallel-Right Constructor
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh0 Sown0 store0 bufs0 store0' bufs0' P0 Q0 Q0'
        G0 D₁0 D₂0 G₂_step D₂_step S₂_step nS0 nG0
      obtain ⟨pw, S₁_fin, S₂_fin, G₁_fin, G₂_fin, W₁, W₂, Δ₁, Δ₂,
          hSfin, hGfin, hW, hΔ, hDisjG_mid, hDisjS_mid, hDisjS_left_mid, hDisjS_right_mid,
          hDisjS_fin, hDisjW, hDisjΔ, hP_pre, hQ_pre⟩ :=
        HasTypeProcPreOut_par_inv_witness hPre
      let splitMid : ParSplit Sown0.left Gmid := pw.split
      have hSlenEq : split.S1.length = splitMid.S1.length := by
        calc
          split.S1.length = nS0 := hSlen
          _ = splitMid.S1.length := by simpa [splitMid] using pw.hSlen.symm
      have hSidesEq := ParSplit.sides_eq_of_len (split₁:=split) (split₂:=splitMid) hSlenEq
      have hS1Eq : split.S1 = splitMid.S1 := hSidesEq.1
      have hS2Eq : split.S2 = splitMid.S2 := hSidesEq.2
      -- `par_right`: Build Inner Framing Context
      have hStoreInner :
          StoreTyped Gstore (SEnvAll Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 }) store0 := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      have hShAll :
          DisjointS Ssh0 (Sown0.right ++ (split.S1 ++ split.S2)) := by
        simpa [OwnedEnv.all, split.hS, List.append_assoc] using hDisjShAll
      have hDisjShInner :
          DisjointS Ssh0 ({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) := by
        simpa [OwnedEnv.all, List.append_assoc] using hShAll
      have hOwnAll : DisjointS Sown0.right (split.S1 ++ split.S2) := by
        simpa [OwnedDisjoint, split.hS] using hOwn
      have hDisjRightS1 : DisjointS Sown0.right split.S1 := DisjointS_of_append_left hOwnAll
      have hDisjRightS2 : DisjointS Sown0.right split.S2 := DisjointS_of_append_right hOwnAll
      have hOwnInner :
          OwnedDisjoint ({ right := Sown0.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
        DisjointS_append_left hDisjRightS2 hDisjS
      -- `par_right`: Session/Disjointness Projections
      have hSubG1 : SessionsOf splitMid.G1 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hSubG2 : SessionsOf splitMid.G2 ⊆ SessionsOf Gmid := by
        intro s hs
        simpa [splitMid, splitMid.hG] using
          (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hs)
      have hDisjLeftG1 : DisjointG Gleft splitMid.G1 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
        exact DisjointG_symm hTmp
      have hDisjLeftG2 : DisjointG Gleft splitMid.G2 := by
        have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjLM
        have hTmp : DisjointG splitMid.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
        exact DisjointG_symm hTmp
      have hDisjG1Right : DisjointG splitMid.G1 Gright := DisjointG_of_subset_left hSubG1 hDisjMR
      have hDisjG2Right : DisjointG splitMid.G2 Gright := DisjointG_of_subset_left hSubG2 hDisjMR
      have hDisjLeftMidInner : DisjointG (Gleft ++ splitMid.G1) splitMid.G2 :=
        DisjointG_append_left hDisjLeftG2 hDisjG_mid
      have hDisjLeftRightInner : DisjointG (Gleft ++ splitMid.G1) Gright :=
        DisjointG_append_left hDisjLR hDisjG1Right
      have hEqInner : G0 = (Gleft ++ splitMid.G1) ++ splitMid.G2 ++ Gright := by
        calc
          G0 = Gleft ++ Gmid ++ Gright := hEqG
          _ = Gleft ++ (splitMid.G1 ++ splitMid.G2) ++ Gright := by
                simpa [splitMid, splitMid.hG]
          _ = (Gleft ++ splitMid.G1) ++ splitMid.G2 ++ Gright := by
                simp [List.append_assoc]
      have hDisjS_right : DisjointS split.S1 S₂_fin := by
        simpa [splitMid, hS1Eq] using hDisjS_right_mid
      have hDisjRightFinAll : DisjointS Sown0.right (S₁_fin ++ S₂_fin) := by
        simpa [hSfin] using hDisjRightFin
      have hDisjRightS2Fin : DisjointS Sown0.right S₂_fin :=
        DisjointS_of_append_right hDisjRightFinAll
      have hDisjOutQ : DisjointS (Sown0.right ++ split.S1) S₂_fin :=
        DisjointS_append_left hDisjRightS2Fin hDisjS_right
      have hQ0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S1, left := split.S2 } splitMid.G2 Q0
            { right := Sown0.right ++ split.S1, left := S₂_fin } G₂_fin W₂ Δ₂ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hQ_pre
      -- `par_right`: Apply IH On Right Branch
      obtain ⟨G₂_mid', W₂', Δ₂', hEqShape, hSubSess2, hQ', hSubW2, hSubΔ2⟩ :=
        ih (Gstore:=Gstore) (Gleft:=Gleft ++ splitMid.G1) (Gmid:=splitMid.G2) (Gright:=Gright)
          (Sfin:={ right := Sown0.right ++ split.S1, left := S₂_fin })
          (Gfin:=G₂_fin) (W:=W₂) (Δ:=Δ₂)
          hStoreInner hDisjShInner hOwnInner hDisjLeftMidInner hDisjLeftRightInner hDisjG2Right
          hEqInner hDisjOutQ hQ0
      have hDomStep : SEnvDomSubset S₂_step S₂_fin := by
        simpa using (HasTypeProcPreOut_domsubset hQ')
      have hStepS1 : DisjointS S₂_step split.S1 := by
        have hTmp : DisjointS split.S1 S₂_step :=
          DisjointS_of_domsubset_right hDomStep hDisjS_right
        exact DisjointS_symm hTmp
      have hStepS1fin : DisjointS S₂_step S₁_fin := by
        have hTmp : DisjointS S₁_fin S₂_step :=
          DisjointS_of_domsubset_right hDomStep hDisjS_fin
        exact DisjointS_symm hTmp
      have hDisjRightS1Fin : DisjointS Sown0.right S₁_fin :=
        DisjointS_of_append_left hDisjRightFinAll
      have hDisjInPNew : DisjointS (Sown0.right ++ S₂_step) split.S1 :=
        DisjointS_append_left hDisjRightS1 hStepS1
      have hDisjOutPNew : DisjointS (Sown0.right ++ S₂_step) S₁_fin :=
        DisjointS_append_left hDisjRightS1Fin hStepS1fin
      have hP0 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ split.S2, left := split.S1 } splitMid.G1 P0
            { right := Sown0.right ++ split.S2, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        simpa [splitMid, hS1Eq, hS2Eq] using hP_pre
      have hP1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₂_step, left := splitMid.S1 } splitMid.G1 P0
            { right := Sown0.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ := by
        have hTmp :
            HasTypeProcPreOut Ssh0 { right := Sown0.right ++ S₂_step, left := split.S1 } splitMid.G1 P0
              { right := Sown0.right ++ S₂_step, left := S₁_fin } G₁_fin W₁ Δ₁ :=
          HasTypeProcPreOut_reframe_right
            (R:=Sown0.right ++ split.S2) (R':=Sown0.right ++ S₂_step)
            (L:=split.S1) (L':=S₁_fin) (G:=splitMid.G1) (P:=P0)
            hDisjInPNew hDisjOutPNew hP0
        simpa [splitMid, hS1Eq] using hTmp
      -- `par_right`: Reconstruct Combined Result
      have hQ1 :
          HasTypeProcPreOut Ssh0 { right := Sown0.right ++ splitMid.S1, left := S₂_step } G₂_mid' Q0'
            { right := Sown0.right ++ splitMid.S1, left := S₂_fin } G₂_fin W₂' Δ₂' := by
        simpa [splitMid, hS1Eq] using hQ'
      -- `par_right`: Final Packing And Subsets
      have hDisjGFinal : DisjointG splitMid.G1 G₂_mid' := by
        have hTmp : DisjointG G₂_mid' splitMid.G1 :=
          DisjointG_of_subset_left hSubSess2 (DisjointG_symm hDisjG_mid)
        exact DisjointG_symm hTmp
      have hStepS1mid : DisjointS splitMid.S1 S₂_step := by
        simpa [splitMid, hS1Eq] using (DisjointS_symm hStepS1)
      have hDisjS1FinStep : DisjointS S₁_fin S₂_step := by
        simpa using (DisjointS_symm hStepS1fin)
      have hDisjW' : DisjointW W₁ W₂' := DisjointW_of_subset_right hSubW2 hDisjW
      have hDisjΔ' : DisjointS Δ₁ Δ₂' := DisjointS_of_domsubset_right hSubΔ2 hDisjΔ
      let splitOut : ParSplit ({ right := Sown0.right, left := splitMid.S1 ++ S₂_step } : OwnedEnv).left
          (splitMid.G1 ++ G₂_mid') :=
        { S1 := splitMid.S1
          S2 := S₂_step
          G1 := splitMid.G1
          G2 := G₂_mid'
          hS := rfl
          hG := rfl }
      have hParMid :
          HasTypeProcPreOut Ssh0 { right := Sown0.right, left := splitMid.S1 ++ S₂_step }
            (splitMid.G1 ++ G₂_mid') (.par splitMid.S1.length nG0 P0 Q0')
            Sfin Gfin (W₁ ++ W₂') (Δ₁ ++ Δ₂') :=
        HasTypeProcPreOut.par splitOut rfl hSfin hGfin rfl rfl
          hDisjGFinal hStepS1mid hDisjS1FinStep hDisjS_right_mid hDisjS_fin hDisjW' hDisjΔ'
          hP1 hQ1
      have hEqGFinal : split.G1 ++ G₂_step = Gleft ++ (splitMid.G1 ++ G₂_mid') ++ Gright := by
        simpa [List.append_assoc] using hEqShape
      have hSubSessFinal : SessionsOf (splitMid.G1 ++ G₂_mid') ⊆ SessionsOf Gmid := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=splitMid.G1) (G₂:=G₂_mid') hs
        cases hs' with
        | inl hsL =>
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_left (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsL)
        | inr hsR =>
            have hsMid2 : s ∈ SessionsOf splitMid.G2 := hSubSess2 hsR
            simpa [splitMid, splitMid.hG] using
              (SessionsOf_append_right (G₁:=splitMid.G1) (G₂:=splitMid.G2) hsMid2)
      have hSubWFinal : FootprintSubset (W₁ ++ W₂') W := by
        have hSubW12 : FootprintSubset (W₁ ++ W₂') (W₁ ++ W₂) :=
          FootprintSubset_append_right_of_subset hSubW2
        simpa [hW] using hSubW12
      have hSubΔFinal : SEnvDomSubset (Δ₁ ++ Δ₂') Δ := by
        have hSubΔ12 : SEnvDomSubset (Δ₁ ++ Δ₂') (Δ₁ ++ Δ₂) :=
          SEnvDomSubset_append_right_of_domsubset hSubΔ2
        simpa [hΔ] using hSubΔ12
      refine ⟨splitMid.G1 ++ G₂_mid', W₁ ++ W₂', Δ₁ ++ Δ₂', ?_, hSubSessFinal, ?_, hSubWFinal, hSubΔFinal⟩
      · simpa [hEqGFinal]
      · simpa [splitMid, hS1Eq, List.append_assoc] using hParMid
  -- Parallel Skip Constructors
  | par_skip_left split hSlen hS1Nil =>
      rename_i G0 D0 Ssh0 Sown0 store0 bufs0 Q0 nS0 nG0
      exact preserved_sub_middle_par_skip_left
        (hOwn:=hOwn) (hEqG:=hEqG) (hDisjRightFin:=hDisjRightFin)
        (hPre:=hPre) (split:=split) (hSlen:=hSlen) (hS1Nil:=hS1Nil)
  | par_skip_right split hSlen hS2Nil =>
      rename_i G0 D0 Ssh0 Sown0 store0 bufs0 P0 nS0 nG0
      exact preserved_sub_middle_par_skip_right
        (hOwn:=hOwn) (hEqG:=hEqG) (hDisjRightFin:=hDisjRightFin)
        (hPre:=hPre) (split:=split) (hSlen:=hSlen) (hS2Nil:=hS2Nil)


end
