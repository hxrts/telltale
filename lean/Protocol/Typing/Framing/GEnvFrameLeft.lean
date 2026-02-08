import Protocol.Environments.Core
import Protocol.Typing.StepLemmas
import Protocol.Typing.MergeLemmas
import Protocol.Typing.Framing.Lemmas
import Protocol.Typing.Framing.GEnvFrameHelpers

/-
The Problem. Show that pre-out typing is stable under framing a disjoint GEnv
on the left. This requires a constructive par case using the frame_left_par
lemma and careful re-framing of owned environments.

Solution Structure. Prove a dedicated par helper, then discharge each
constructor case by rewriting lookups and using the IH where needed.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Pre-Out Framing (Left) -/

/-- Helper: reframe the left-par pre-out typing across an empty right frame. -/
private lemma frame_left_par_reframe
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr Gleft Gleft' G₂ G₂' : GEnv} {P Q : Process}
    {S₁ S₂ S₁' S₂' : SEnv} {W₁ W₂ : Footprint} {Δ₁ Δ₂ : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₂, left := S₁ } (Gfr ++ Gleft) P
      { right := Sown.right ++ S₂, left := S₁' } (Gfr ++ Gleft') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₁, left := S₂ } G₂ Q
      { right := Sown.right ++ S₁, left := S₂' } G₂' W₂ Δ₂ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₁ } (Gfr ++ Gleft) P
      { right := (∅ : SEnv), left := S₁' } (Gfr ++ Gleft') W₁ Δ₁ ∧
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₂ } G₂ Q
      { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ := by
  -- Strip the right-owned frame to match frame_left_par.
  intro hP hQ
  have hP0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₂) (R':=(∅ : SEnv)) (L:=S₁) (L':=S₁')
      (G:=Gfr ++ Gleft) (P:=P) hP
  have hQ0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₁) (R':=(∅ : SEnv)) (L:=S₂) (L':=S₂')
      (G:=G₂) (P:=Q) hQ
  exact ⟨hP0, hQ0⟩

/-- Helper: assemble the par case with empty right frame. -/
private lemma frame_left_par_apply
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁ S₂ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
    split.G1.length = nG →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = (G₁' ++ G₂') →
    Wfin = (W₁ ++ W₂) →
    Δfin = (Δ₁ ++ Δ₂) →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    S₁ = split.S1 →
    S₂ = split.S2 →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₁ } (Gfr ++ split.G1) P
      { right := (∅ : SEnv), left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := S₂ } split.G2 Q
      { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr G →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  -- Use frame_left_par with empty right frame to build the par judgment.
  intro hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hS1 hS2 hP hQ hDisjGfrG
  have hDisjEmpty_left : DisjointS (∅ : SEnv) Sown.left := by
    exact DisjointS_left_empty Sown.left
  have hDisjEmpty_fin : DisjointS (∅ : SEnv) (S₁' ++ S₂') := by
    exact DisjointS_left_empty (S₁' ++ S₂')
  have ihP :
      DisjointS (∅ : SEnv) split.S1 →
      DisjointS (∅ : SEnv) S₁' →
      DisjointG Gfr split.G1 →
      HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S1 } (Gfr ++ split.G1) P
        { right := (∅ : SEnv), left := S₁' } (Gfr ++ G₁') W₁ Δ₁ := by
    -- Disjointness is trivial with empty frame, so reuse hP.
    intro _ _ _
    simpa [hS1] using hP
  exact frame_left_par (split:=split)
    (hSfin:=rfl) (hGfin:=hGfin) (hW:=hW) (hΔ:=hΔ)
    hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ
    (by simpa [hS2] using hQ) hDisjEmpty_left hDisjEmpty_fin hDisjGfrG ihP

/-- Helper: restore the right-owned frame after a par step. -/
private lemma frame_left_par_restore
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {S₁' S₂' : SEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv} :
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin →
    HasTypeProcPreOut Ssh { right := Sown.right, left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := Sown.right, left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  -- Reintroduce the right-owned frame via reframe_right.
  intro hPar0
  exact HasTypeProcPreOut_reframe_right
    (R:=(∅ : SEnv)) (R':=Sown.right) (L:=Sown.left) (L':=S₁' ++ S₂')
    (G:=Gfr ++ G) (P:=.par nS nG P Q) hPar0

/-- Frame on the left: par (constructive). -/
private lemma HasTypeProcPreOut_frame_G_left_par
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁ S₂ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
    split.G1.length = nG →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = (G₁' ++ G₂') →
    Wfin = (W₁ ++ W₂) →
    Δfin = (Δ₁ ++ Δ₂) →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    S₁ = split.S1 →
    S₂ = split.S2 →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₂, left := S₁ } (Gfr ++ split.G1) P
      { right := Sown.right ++ S₂, left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ S₁, left := S₂ } split.G2 Q
      { right := Sown.right ++ S₁, left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr split.G1 →
    DisjointG Gfr split.G2 →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.par nS nG P Q) Sfin (Gfr ++ Gfin) Wfin Δfin := by
  -- Strip right frame, use frame_left_par, then restore the right frame.
  intro hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hS1 hS2 hP hQ hDisjGfrG1 hDisjGfrG2
  have hDisjGfrG : DisjointG Gfr G := by
    have hDisjGfrG' : DisjointG Gfr (split.G1 ++ split.G2) :=
      DisjointG_append_right (G₁:=Gfr) (G₂:=split.G1) (G₃:=split.G2) hDisjGfrG1 hDisjGfrG2
    simpa [split.hG] using hDisjGfrG'
  obtain ⟨hP0, hQ0⟩ := frame_left_par_reframe (Sown:=Sown) (Gfr:=Gfr) hP hQ
  have hPar0 :=
    frame_left_par_apply (split:=split)
      hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hS1 hS2 hP0 hQ0 hDisjGfrG
  have hPar1 := frame_left_par_restore (Sown:=Sown) (Gfr:=Gfr) (G:=G) hPar0
  simpa [hSfin] using hPar1

/-- Frame a disjoint GEnv on the left of pre-out typing. -/
lemma HasTypeProcPreOut_frame_G_left
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gfr G →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) P Sfin (Gfr ++ Gfin) W Δ := by
  -- Dispatch by constructor, extending lookups and updates across the frame.
  intro hDisj h
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hG'' : lookupG (Gfr ++ G) e = some (.send q T L) := by
        simpa [hG] using hG'
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG'' hx)
  | recv_new hk hG hNoSh hNoOwnR hNoOwnL =>
      rename_i Sown G k x e p T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hG'' : lookupG (Gfr ++ G) e = some (.recv p T L) := by
        simpa [hG] using hG'
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG'' hNoSh hNoOwnR hNoOwnL)
  | recv_old hk hG hNoSh hNoOwnR hOwn =>
      rename_i Sown G k x e p T L T'
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hG'' : lookupG (Gfr ++ G) e = some (.recv p T L) := by
        simpa [hG] using hG'
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG'' hNoSh hNoOwnR hOwn)
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hG'' : lookupG (Gfr ++ G) e = some (.select q bs) := by
        simpa [hG] using hG'
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      simpa [hUpd] using
        (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G) hk hG'' hbs)
  | branch hk hG hLen hLabels hBodies hOutLbl hDom ihOutLbl =>
      rename_i Sown G k procs e p bs Sfin Gfin W Δ
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hG' := lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone
      have hG'' : lookupG (Gfr ++ G) e = some (.branch p bs) := by
        simpa [hG] using hG'
      have hBodies' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh Sown
              (updateG (Gfr ++ G) e (bs.get ⟨i, hi⟩).2)
              (procs.get ⟨i, hip⟩).2 := by
        -- Reframe each branch body through the left G-frame.
        intro i hi hip
        have hBody := hBodies i hi hip
        have hDisj' : DisjointG Gfr (updateG G e (bs.get ⟨i, hi⟩).2) := by
          -- Use the shared update disjointness lemma and flip sides.
          have hDisj'0 :
              DisjointG (updateG G e (bs.get ⟨i, hi⟩).2) Gfr :=
            disjointG_updateG_left (e:=e) (L:=(bs.get ⟨i, hi⟩).2) (L0:=.branch p bs)
              hG (DisjointG_symm hDisj)
          exact DisjointG_symm hDisj'0
        have hBody' := HasTypeProcPre_frame_G (G₁:=Gfr)
          (G₂:=updateG G e (bs.get ⟨i, hi⟩).2) hDisj' hBody
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e)
          (L:=(bs.get ⟨i, hi⟩).2) hNone
        have hBody'' := hBody'
        rw [hUpd.symm] at hBody''
        exact hBody''
      have hOutLbl' : ∀ lbl P L,
          procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
          bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
          HasTypeProcPreOut Ssh Sown (updateG (Gfr ++ G) e L) P Sfin (Gfr ++ Gfin) W Δ := by
        -- Reframe the branch continuation through the left G-frame.
        intro lbl P L hFindP hFindB
        have hDisj' : DisjointG Gfr (updateG G e L) := by
          -- Use the shared update disjointness lemma and flip sides.
          have hDisj'0 : DisjointG (updateG G e L) Gfr :=
            disjointG_updateG_left (e:=e) (L:=L) (L0:=.branch p bs) hG (DisjointG_symm hDisj)
          exact DisjointG_symm hDisj'0
        have hOut' := ihOutLbl lbl P L hFindP hFindB hDisj'
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
        simpa [hUpd] using hOut'
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
        hk hG'' hLen hLabels hBodies' hOutLbl' hDom
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hP' := ihP hDisj
      have hSubG1 : SessionsOf G₁ ⊆ SessionsOf G :=
        SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG1fr : DisjointG Gfr G₁ := by
        have hDisj' : DisjointG G₁ Gfr := DisjointG_of_subset_left hSubG1 (DisjointG_symm hDisj)
        exact DisjointG_symm hDisj'
      have hQ' := ihQ hDisjG1fr
      exact HasTypeProcPreOut.seq hP' hQ'
  | par split hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hS1 hS2 hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin W Δ S₁ S₂ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      have hDisjG1fr : DisjointG split.G1 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).1
      have hDisjG2fr : DisjointG split.G2 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).2
      have hDisjGfrG1 : DisjointG Gfr split.G1 := DisjointG_symm hDisjG1fr
      have hDisjGfrG2 : DisjointG Gfr split.G2 := DisjointG_symm hDisjG2fr
      have hP' := ihP hDisjGfrG1
      exact HasTypeProcPreOut_frame_G_left_par (Ssh:=Ssh) (Gfr:=Gfr) (split:=split)
        hSlen hGlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
        hDisjW hDisjΔ hS1 hS2 hP' hQ hDisjGfrG1 hDisjGfrG2
  | assign_new hNoSh hNoOwnR hNoOwnL hv =>
      rename_i Sown G x v T
      have hv' := HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnR hNoOwnL hv'
  | assign_old hNoSh hNoOwnR hOwn hv =>
      rename_i Sown G x v T T'
      have hv' := HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv
      exact HasTypeProcPreOut.assign_old hNoSh hNoOwnR hOwn hv'
