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

/-! ## Pre-Update Typing Preservation -/

private lemma length_updateG_preserved_pu
    {G : GEnv} {e : Endpoint} {L L' : LocalType} :
    lookupG G e = some L →
    (updateG G e L').length = G.length := by
  intro hLookup
  induction G with
  | nil =>
      simp [lookupG] at hLookup
  | cons hd tl ih =>
      cases hd with
      | mk e' L'' =>
          by_cases hEq : e = e'
          · subst hEq
            simp [lookupG] at hLookup
            simp [updateG]
          · have h' : lookupG tl e = some L := by
              have hbeq : (e == e') = false := by
                exact beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hbeq] using hLookup
            simp [updateG, hEq, ih h']

private lemma TypedStep_G_length_pu
    {G G' : GEnv} {D D' : DEnv} {Ssh : SEnv} {Sown Sown' : OwnedEnv}
    {store store' : VarStore} {bufs bufs' : Buffers} {P P' : Process} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    G'.length = G.length := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hLen :
          (updateG G e L).length = G.length :=
        length_updateG_preserved_pu (G:=G) (e:=e) (L:=.send target T L) (L':=L) hG
      simpa [hGout] using hLen
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hLen :
          (updateG G e L).length = G.length :=
        length_updateG_preserved_pu (G:=G) (e:=e) (L:=.recv source T L) (L':=L) hG
      simpa [hGout] using hLen
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hLen :
          (updateG G e L).length = G.length :=
        length_updateG_preserved_pu (G:=G) (e:=e) (L:=.select target bs) (L':=L) hG
      simpa [hGout] using hLen
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hLen :
          (updateG G e L).length = G.length :=
        length_updateG_preserved_pu (G:=G) (e:=e) (L:=.branch source bs) (L':=L) hG
      simpa [hGout] using hLen
  | assign hv hSout hStoreOut =>
      simp
  | seq_step hTS ih =>
      simpa using ih
  | seq_skip =>
      simp
  | par_left split hSlen hTS hDisjG hDisjD hDisjS ih =>
      simpa using ih
  | par_right split hSlen hTS hDisjG hDisjD hDisjS ih =>
      simpa using ih
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
private theorem HasTypeProcPreOut_preserved_sub
    {Gstore G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped Gstore (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' ∧
      FootprintSubset W' W ∧ SEnvDomSubset Δ' Δ := by
  intro hMiddle hStore hDisjShAll hOwnDisj hTS hPre hDisjRightFin
  have hDisjFrame : DisjointG G ([] : GEnv) := DisjointG_right_empty G
  have hEq : G = G ++ ([] : GEnv) := by simp
  have hEq' : G' = G' ++ ([] : GEnv) := by simp
  simpa using
    (HasTypeProcPreOut_preserved_sub_left_frame
      (Gstore:=Gstore) (G₁:=G) (G₂:=[]) (G:=G) (G':=G') (G₁':=G')
      (D:=D) (Ssh:=Ssh) (Sown:=Sown) (store:=store) (bufs:=bufs) (P:=P)
      (D':=D') (Sown':=Sown') (store':=store') (bufs':=bufs') (P':=P')
      (Sfin:=Sfin) (Gfin:=Gfin) (W:=W) (Δ:=Δ)
      hMiddle hStore hDisjShAll hOwnDisj hDisjFrame hEq hEq' hTS hPre hDisjRightFin)

/-- Pre-out typing is preserved by a single TypedStep: the remaining process
    still leads to the same final environments. -/
theorem HasTypeProcPreOut_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Sfin Gfin W Δ} :
    HasTypeProcPreOut_preserved_sub_middle_frame_spec →
    StoreTyped G (SEnvAll Ssh Sown) store →
    DisjointS Ssh (Sown : SEnv) →
    OwnedDisjoint Sown →
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    ∃ W' Δ', HasTypeProcPreOut Ssh Sown' G' P' Sfin Gfin W' Δ' := by
  intro hMiddle hStore hDisjShAll hOwnDisj hTS hPre hDisjRightFin
  obtain ⟨W', Δ', hPre', _, _⟩ :=
    HasTypeProcPreOut_preserved_sub hMiddle hStore hDisjShAll hOwnDisj hTS hPre hDisjRightFin
  exact ⟨W', Δ', hPre'⟩


end
