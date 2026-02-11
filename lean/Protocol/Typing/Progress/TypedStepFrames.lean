import Protocol.Typing.Progress.FramingInversions

/-! # TypedStep Frame Preservation

Frame preservation lemma showing that `TypedStep` in a three-way
split `Gleft ++ Gmid ++ Gright` produces output with the same structure. -/

/-
The Problem. For compositional progress, we need to show that a step
in the middle portion of a framed GEnv preserves the left and right
frame portions unchanged.

Solution Structure. Prove `TypedStep_preserves_frames` by induction
on `TypedStep`. Each constructor case shows the update stays within
Gmid by endpoint locality, producing `G' = Gleft ++ Gmid' ++ Gright`.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Frame Preservation Main Lemma -/

lemma TypedStep_preserves_frames
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfull Gleft Gmid Gright : GEnv}
    {D : DEnv} {store : VarStore} {bufs : Buffers} {P : Process}
    {G' : GEnv} {D' : DEnv} {Sown' : OwnedEnv} {store' : VarStore} {bufs' : Buffers} {P' : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    Gfull = Gleft ++ Gmid ++ Gright →
    DisjointG Gleft Gmid →
    DisjointG Gleft Gright →
    DisjointG Gmid Gright →
    StoreTypedStrong Gfull (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    HasTypeProcPreOut Ssh Sown Gmid P Sfin Gfin W Δ →
    TypedStep Gfull D Ssh Sown store bufs P
      G' D' Sown' store' bufs' P' →
    ∃ Gmid', G' = Gleft ++ Gmid' ++ Gright := by
  intro hGfull hDisjL hDisjLR hDisjR hStore hDisjShAll hOwnDisj hOut hStep
  induction hStep generalizing Gleft Gmid Gright Sfin Gfin W Δ with
  | send =>
      rename_i Gfull D Ssh Sown store bufs k x eStep target Tstep Lstep v sendEdge G' D' bufs'
        hkStr hxStr hGStep hS hv hRecvReady hEdge hGout hDout hBufsOut
      exact TypedStep_preserves_frames_send (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) hDisjShAll hOwnDisj (hOut:=hOut) hkStr hGout
  | recv =>
      rename_i Gfull D Ssh Sown store bufs k x eStep source Tstep Lstep v vs recvEdge G' D' Sown' store' bufs'
        hkStr hGStep hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut
      exact TypedStep_preserves_frames_recv (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) hDisjShAll hOwnDisj (hOut:=hOut) hkStr hGout
  | select =>
      rename_i Gfull D Ssh Sown store bufs k ℓ eStep target bsStep Lstep selectEdge G' D' bufs'
        hkStr hGStep hFind hTargetReady hEdge hGout hDout hBufsOut
      exact TypedStep_preserves_frames_select (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) hDisjShAll hOwnDisj (hOut:=hOut) hkStr hGout
  | branch =>
      rename_i Gfull D Ssh Sown store bufs k procs eStep source bsStep ℓ P Lstep vs branchEdge G' D' bufs'
        hkStr hGStep hEdge hBuf hFindP hFindBs hTrace hGout hDout hBufsOut
      exact TypedStep_preserves_frames_branch (hGfull:=hGfull) (hDisjL:=hDisjL)
        (hStore:=hStore) hDisjShAll hOwnDisj (hOut:=hOut) hkStr hGout
  | assign =>
      rename_i Gfull D Ssh Sown store bufs x v T S' store' hv hSout hStoreOut
      cases hOut <;> refine ⟨Gmid, ?_⟩ <;> simpa [List.append_assoc, hGfull]
  | seq_step =>
      rename_i Gfull D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q hStepP ih
      cases hOut with
      | seq hP hQ =>
          exact ih hGfull hDisjL hDisjLR hDisjR hStore hDisjShAll hOwnDisj hP
  | seq_skip =>
      rename_i Gfull D Ssh Sown store bufs Q
      cases hOut with
      | seq hP hQ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc, hGfull]
  | par_left splitFull hSlen' hStepP hDisjGfull hDisjD hDisjSfull ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q Gfull D₁ D₂ G₁' D₁' S₁' nS nG
      cases hOut with
      | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hP hQ =>
          rename_i S1out S2out S1out' S2out' G1out G2out W1out W2out Δ1out Δ2out
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
          have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
          have hDisjGleftG1 : DisjointG Gleft split.G1 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
            exact DisjointG_symm hTmp
          have hDisjGleftG2 : DisjointG Gleft split.G2 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
            exact DisjointG_symm hTmp
          have hDisjG1Right : DisjointG split.G1 Gright :=
            DisjointG_of_subset_left hSubG1 hDisjR
          have hDisjG2Right : DisjointG split.G2 Gright :=
            DisjointG_of_subset_left hSubG2 hDisjR
          have hDisjLeftRight : DisjointG Gleft (split.G2 ++ Gright) := by
            have hLeft : DisjointG split.G2 Gleft := DisjointG_symm hDisjGleftG2
            have hRight : DisjointG Gright Gleft := DisjointG_symm hDisjLR
            have hCombined : DisjointG (split.G2 ++ Gright) Gleft :=
              DisjointG_append_left hLeft hRight
            exact DisjointG_symm hCombined
          have hDisjMidRight : DisjointG split.G1 (split.G2 ++ Gright) := by
            have hLeft : DisjointG split.G2 split.G1 := DisjointG_symm hDisjG
            have hRight : DisjointG Gright split.G1 := DisjointG_symm hDisjG1Right
            have hTmp : DisjointG (split.G2 ++ Gright) split.G1 :=
              DisjointG_append_left hLeft hRight
            exact DisjointG_symm hTmp
          have hGfull' : Gfull = Gleft ++ split.G1 ++ (split.G2 ++ Gright) := by
            calc
              Gfull = Gleft ++ Gmid ++ Gright := hGfull
              _ = Gleft ++ (split.G1 ++ split.G2) ++ Gright := by
                simpa [split.hG]
              _ = Gleft ++ split.G1 ++ (split.G2 ++ Gright) := by
                simp [List.append_assoc]
          have hStoreL' :
              StoreTypedStrong (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreL
          have hStoreL'' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [hGfull'] using hStoreL'
          have hStoreL''' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ splitFull.S2, left := splitFull.S1 }) store := by
            simpa [hS1Eq, hS2Eq] using hStoreL''
          have hP' :
              HasTypeProcPreOut Ssh { right := Sown.right ++ splitFull.S2, left := splitFull.S1 } split.G1 P
                { right := Sown.right ++ splitFull.S2, left := S1out' } G1out W1out Δ1out := by
            simpa [hS1Eq, hS2Eq] using hP
          have hStepP' :
              TypedStep (Gleft ++ split.G1 ++ (split.G2 ++ Gright))
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                store bufs P
                (G₁' ++ splitFull.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' := by
            simpa [hGfull', hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepP
          have hStepP'' :
              TypedStep Gfull (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S2, left := split.S1 }
                store bufs P
                (G₁' ++ splitFull.G2) (D₁' ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁' } store' bufs' P' := by
            simpa [hGfull'] using hStepP'
          have hDisjShRight : DisjointS Ssh Sown.right := DisjointS_owned_right hDisjShAll
          have hDisjShSplit : DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 :=
            DisjointS_split_from_owned_left split hDisjShAll
          have hDisjShSubL :
              DisjointS Ssh ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
            DisjointS_owned_repack hDisjShRight hDisjShSplit.1 hDisjShSplit.2
          have hOwnSubL :
              OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
            OwnedDisjoint_sub_left (Sown:=Sown) (split:=split) hOwnDisj hDisjS
          have hDisjShSubL' :
              DisjointS Ssh ({ right := Sown.right ++ splitFull.S2, left := splitFull.S1 } : OwnedEnv) := by
            simpa [hS1Eq, hS2Eq] using hDisjShSubL
          have hOwnSubL' :
              OwnedDisjoint ({ right := Sown.right ++ splitFull.S2, left := splitFull.S1 } : OwnedEnv) := by
            simpa [hS1Eq, hS2Eq] using hOwnSubL
          rcases ih hGfull' hDisjGleftG1 hDisjLeftRight hDisjMidRight hStoreL''' hDisjShSubL' hOwnSubL' hP' with
            ⟨Gmid', hShape⟩
          refine ⟨Gmid' ++ split.G2, ?_⟩
          simp [hShape, List.append_assoc]
  | par_right splitFull hSlen' hStepQ hDisjGfull hDisjD hDisjSfull ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' Gfull D₁ D₂ G₂' D₂' S₂' nS nG
      cases hOut with
      | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
          hDisjW hDisjΔ hP hQ =>
          rename_i S1out S2out S1out' S2out' G1out G2out W1out W2out Δ1out Δ2out
          have hSeq : splitFull.S1 ++ splitFull.S2 = split.S1 ++ split.S2 := by
            rw [← splitFull.hS, ← split.hS]
          have hSlenEq : splitFull.S1.length = split.S1.length :=
            hSlen'.trans hSlen.symm
          have hS1Eq : splitFull.S1 = split.S1 := List.append_inj_left hSeq hSlenEq
          have hS2Eq : splitFull.S2 = split.S2 := List.append_inj_right hSeq hSlenEq
          have hStoreBase :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) ((split.S1 ++ split.S2) ++ (∅ : SEnv))) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hStoreSwap :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll (Ssh ++ Sown.right) (split.S2 ++ (split.S1 ++ (∅ : SEnv)))) store :=
            StoreTypedStrong_swap_S_left_prefix (Ssh:=Ssh ++ Sown.right)
              (S₁:=split.S1) (S₂:=split.S2) (S₃:=∅) hDisjS
              (by simpa [List.append_assoc] using hStoreBase)
          have hStoreL :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S2, left := split.S1 }) store := by
            simpa [SEnvAll, List.append_assoc] using hStoreSwap
          have hStoreR :
              StoreTypedStrong (Gleft ++ Gmid ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull, SEnvAll, split.hS, List.append_assoc] using hStore
          have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_left (G₂:=split.G2) hs
          have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf Gmid := by
            intro s hs
            simpa [split.hG] using SessionsOf_append_right (G₁:=split.G1) hs
          have hDisjGleftG1 : DisjointG Gleft split.G1 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G1 Gleft := DisjointG_of_subset_left hSubG1 hSym
            exact DisjointG_symm hTmp
          have hDisjGleftG2 : DisjointG Gleft split.G2 := by
            have hSym : DisjointG Gmid Gleft := DisjointG_symm hDisjL
            have hTmp : DisjointG split.G2 Gleft := DisjointG_of_subset_left hSubG2 hSym
            exact DisjointG_symm hTmp
          have hDisjG1Right : DisjointG split.G1 Gright :=
            DisjointG_of_subset_left hSubG1 hDisjR
          have hDisjG2Right : DisjointG split.G2 Gright :=
            DisjointG_of_subset_left hSubG2 hDisjR
          have hDisjLeftMid : DisjointG (Gleft ++ split.G1) split.G2 :=
            DisjointG_append_left hDisjGleftG2 hDisjG
          have hDisjLeftRight : DisjointG (Gleft ++ split.G1) Gright :=
            DisjointG_append_left hDisjLR hDisjG1Right
          have hGfull' : Gfull = (Gleft ++ split.G1) ++ split.G2 ++ Gright := by
            calc
              Gfull = Gleft ++ Gmid ++ Gright := hGfull
              _ = Gleft ++ (split.G1 ++ split.G2) ++ Gright := by
                simpa [split.hG]
              _ = (Gleft ++ split.G1) ++ split.G2 ++ Gright := by
                simp [List.append_assoc]
          have hStoreR' :
              StoreTypedStrong ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [split.hG, List.append_assoc] using hStoreR
          have hStoreR'' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
            simpa [hGfull'] using hStoreR'
          have hStoreR''' :
              StoreTypedStrong Gfull
                (SEnvAll Ssh { right := Sown.right ++ splitFull.S1, left := splitFull.S2 }) store := by
            simpa [hS1Eq, hS2Eq] using hStoreR''
          have hQ' :
              HasTypeProcPreOut Ssh { right := Sown.right ++ splitFull.S1, left := splitFull.S2 } split.G2 Q
                { right := Sown.right ++ splitFull.S1, left := S2out' } G2out W2out Δ2out := by
            simpa [hS1Eq, hS2Eq] using hQ
          have hStepQ' :
              TypedStep ((Gleft ++ split.G1) ++ split.G2 ++ Gright)
                (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                store bufs Q
                (splitFull.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' := by
            simpa [hGfull', hS1Eq, hS2Eq, split.hG, List.append_assoc] using hStepQ
          have hStepQ'' :
              TypedStep Gfull (D₁ ++ D₂) Ssh { right := Sown.right ++ split.S1, left := split.S2 }
                store bufs Q
                (splitFull.G1 ++ G₂') (D₁ ++ D₂')
                { right := Sown.right ++ split.S1, left := S₂' } store' bufs' Q' := by
            simpa [hGfull'] using hStepQ'
          have hDisjShRight : DisjointS Ssh Sown.right := DisjointS_owned_right hDisjShAll
          have hDisjShSplit : DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 :=
            DisjointS_split_from_owned_left split hDisjShAll
          have hDisjShSubR :
              DisjointS Ssh ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
            DisjointS_owned_repack hDisjShRight hDisjShSplit.2 hDisjShSplit.1
          have hOwnSubR :
              OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
            OwnedDisjoint_sub_right (Sown:=Sown) (split:=split) hOwnDisj hDisjS
          have hDisjShSubR' :
              DisjointS Ssh ({ right := Sown.right ++ splitFull.S1, left := splitFull.S2 } : OwnedEnv) := by
            simpa [hS1Eq, hS2Eq] using hDisjShSubR
          have hOwnSubR' :
              OwnedDisjoint ({ right := Sown.right ++ splitFull.S1, left := splitFull.S2 } : OwnedEnv) := by
            simpa [hS1Eq, hS2Eq] using hOwnSubR
          rcases ih hGfull' hDisjLeftMid hDisjLeftRight hDisjG2Right hStoreR''' hDisjShSubR' hOwnSubR' hQ' with
            ⟨Gmid', hShape⟩
          refine ⟨split.G1 ++ Gmid', ?_⟩
          simp [hShape, List.append_assoc]
  | par_skip_left =>
      rename_i Gfull D Ssh Sown store bufs Q nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc] using hGfull
  | par_skip_right =>
      rename_i Gfull D Ssh Sown store bufs P nS nG
      cases hOut with
      | par _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          refine ⟨Gmid, ?_⟩
          simpa [List.append_assoc] using hGfull


end
