import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.FramedPreUpdate

/-
The Problem. Show that pre-out typing survives a single runtime step, producing
new post-environments and smaller footprints/domains as needed.

Solution Structure. Induct on the TypedStep derivation, reducing each case to
the corresponding pre-out rule or to the framed pre-update lemmas.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ### Pre-Update Typing Preservation -/

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
private theorem HasTypeProcPreOut_preserved_sub
    {Gstore G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hStore hDisjShAll hOwnDisj hTS hPre
  induction hTS generalizing Sfin Gfin W Δ with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      cases hPre with
      | send hk' hG' hx' =>
          rename_i e' q' T' L'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
            lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=k)
              (T:=.chan e'.sid e'.role) hDisjShAll hOwnDisj hk'
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
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
            lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=k)
              (T:=.chan e'.sid e'.role) hDisjShAll hOwnDisj hk'
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
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
            lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=k)
              (T:=.chan e'.sid e'.role) hDisjShAll hOwnDisj hk'
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
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
            lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=k)
              (T:=.chan e'.sid e'.role) hDisjShAll hOwnDisj hk'
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
      | branch hk' hG' hLen hLabels hPreAll hPost hSess hDom =>
          rename_i e' p' bs'
          have hkPre : lookupSEnv (SEnvAll Ssh Sown) k = some (.chan e'.sid e'.role) :=
            lookupSEnv_all_of_visible (Ssh:=Ssh) (Sown:=Sown) (x:=k)
              (T:=.chan e'.sid e'.role) hDisjShAll hOwnDisj hk'
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
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ := ih hStore hDisjShAll hOwnDisj hP
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
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁_step D₁_step S₁_step nS nG
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
      have hDisjShRight : DisjointS Ssh Sown.right := DisjointS_owned_right_pu hDisjShAll
      have hDisjShSplit : DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 :=
        DisjointS_split_from_owned_left_pu (Sown:=Sown) (split:=split) hDisjShAll
      have hDisjShAll_inner :
          DisjointS Ssh ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
        DisjointS_owned_repack_pu hDisjShRight hDisjShSplit.1 hDisjShSplit.2
      have hOwnDisj_inner :
          OwnedDisjoint ({ right := Sown.right ++ split.S2, left := split.S1 } : OwnedEnv) :=
        OwnedDisjoint_sub_left_pu (Sown:=Sown) (split:=split) hOwnDisj hDisjS
      cases hPre with
      | par split' hSlenPre hGlenPre hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hSlen' : split'.S1.length = split.S1.length := by
            calc
              split'.S1.length = nS := hSlenPre
              _ = split.S1.length := hSlen.symm
          have hGlen' : split'.G1.length = split.G1.length := by
            calc
              split'.G1.length = nG := hGlenPre
              _ = split.G1.length := hGlen.symm
          have hEq : split' = split := ParSplit.unique split' split hSlen' hGlen'
          cases hEq
          rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
          subst hS1
          subst hS2
          have hTS' :
              TypedStep (split.G1 ++ split.G2) (D₁ ++ D₂) Ssh
                { right := Sown.right ++ split.S2, left := split.S1 } store bufs P
                (G₁_step ++ split.G2) (D₁_step ++ D₂)
                { right := Sown.right ++ split.S2, left := S₁_step } store' bufs' P' := by
            simpa [split.hG] using hTS
          obtain ⟨W₁', Δ₁', hP', hSubW, hSubΔ⟩ :=
            HasTypeProcPreOut_preserved_sub_left_frame
              (Gstore:=Gstore) hStoreL hDisjShAll_inner hOwnDisj_inner hDisjG rfl rfl hTS' hP
          let splitOut : ParSplit (S₁_step ++ split.S2) (G₁_step ++ split.G2) :=
            { S1 := S₁_step, S2 := split.S2, G1 := G₁_step, G2 := split.G2, hS := rfl, hG := rfl }
          have hSubG_step : SessionsOf G₁_step ⊆ SessionsOf split.G1 :=
            SessionsOf_subset_of_TypedStep_left_frame hDisjG rfl rfl hTS'
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
          · exact HasTypeProcPreOut.par splitOut rfl rfl hSfin hGfin rfl rfl
              hDisjGOut' hDisjS_left' hDisjS_left hDisjS_in_out hDisjS'' hDisjW' hDisjΔ' rfl rfl hP' hQ'
          · simpa [hW] using (FootprintSubset_append_left hSubW)
          · simpa [hΔ] using (SEnvDomSubset_append_left_of_domsubset hSubΔ)
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂_step D₂_step S₂_step nS nG
      have hStoreR : StoreTyped Gstore (SEnvAll Ssh { right := Sown.right ++ split.S1, left := split.S2 }) store := by
        simpa [SEnvAll, split.hS, List.append_assoc] using hStore
      have hDisjShRight : DisjointS Ssh Sown.right := DisjointS_owned_right_pu hDisjShAll
      have hDisjShSplit : DisjointS Ssh split.S1 ∧ DisjointS Ssh split.S2 :=
        DisjointS_split_from_owned_left_pu (Sown:=Sown) (split:=split) hDisjShAll
      have hDisjShAll_inner :
          DisjointS Ssh ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
        DisjointS_owned_repack_pu hDisjShRight hDisjShSplit.2 hDisjShSplit.1
      have hOwnDisj_inner :
          OwnedDisjoint ({ right := Sown.right ++ split.S1, left := split.S2 } : OwnedEnv) :=
        OwnedDisjoint_sub_right_pu (Sown:=Sown) (split:=split) hOwnDisj hDisjS
      cases hPre with
      | par split' hSlenPre hGlenPre hSfin hGfin hW hΔ
            hDisjG' hDisjS' hDisjS_left hDisjS_right hDisjS'' hDisjW hDisjΔ hS1 hS2 hP hQ =>
          have hSlen' : split'.S1.length = split.S1.length := by
            calc
              split'.S1.length = nS := hSlenPre
              _ = split.S1.length := hSlen.symm
          have hGlen' : split'.G1.length = split.G1.length := by
            calc
              split'.G1.length = nG := hGlenPre
              _ = split.G1.length := hGlen.symm
          have hEq : split' = split := ParSplit.unique split' split hSlen' hGlen'
          cases hEq
          rename_i S₁ S₂ S₁_fin S₂_fin G₁_fin G₂_fin W₁ W₂ Δ₁ Δ₂
          subst hS1
          subst hS2
          have hTS' :
              TypedStep (split.G1 ++ split.G2) (D₁ ++ D₂) Ssh
                { right := Sown.right ++ split.S1, left := split.S2 } store bufs Q
                (split.G1 ++ G₂_step) (D₁ ++ D₂_step)
                { right := Sown.right ++ split.S1, left := S₂_step } store' bufs' Q' := by
            simpa [split.hG] using hTS
          obtain ⟨W₂', Δ₂', hQ', hSubW, hSubΔ⟩ :=
            HasTypeProcPreOut_preserved_sub_right_frame
              (Gstore:=Gstore) hStoreR hDisjShAll_inner hOwnDisj_inner hDisjG rfl rfl hTS' hQ
          let splitOut : ParSplit (split.S1 ++ S₂_step) (split.G1 ++ G₂_step) :=
            { S1 := split.S1, S2 := S₂_step, G1 := split.G1, G2 := G₂_step, hS := rfl, hG := rfl }
          have hSubG_step : SessionsOf G₂_step ⊆ SessionsOf split.G2 :=
            SessionsOf_subset_of_TypedStep_right_frame hDisjG rfl rfl hTS'
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
          · exact HasTypeProcPreOut.par splitOut rfl rfl hSfin hGfin rfl rfl
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
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' := by
  intro hStore hDisjShAll hOwnDisj hTS hPre
  obtain ⟨W', Δ', hPre', _, _⟩ := HasTypeProcPreOut_preserved_sub hStore hDisjShAll hOwnDisj hTS hPre
  exact ⟨W', Δ', hPre'⟩


end
