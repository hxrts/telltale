import Protocol.Typing.Framing.Lemmas.RightTransportLocal

/-! # Left Parallel Transport

SEnv domain subset lemmas for parallel composition, showing that
typing judgments preserve or shrink the owned environment domain. -/

/-
The Problem. In parallel composition `P₁ ∥ P₂`, each branch may erase
some owned variables. We need to show the output SEnv domain is a
subset of the input domain, enabling safe composition.

Solution Structure. Prove `eraseSEnv_domsubset_local` showing erasure
preserves domain subset. Extend to `HasTypeProcPreOut_right_domsubset_local`
for the full typing judgment.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Erasure Domain Subset

lemma eraseSEnv_domsubset_local {S : SEnv} {x : Var} :
    SEnvDomSubset (eraseSEnv S x) S := by
  intro y T hLookup
  induction S with
  | nil =>
      simp [eraseSEnv, lookupSEnv] at hLookup
  | cons hd tl ih =>
      cases hd with
      | mk z U =>
          by_cases hzx : x = z
          · subst hzx
            simp [eraseSEnv] at hLookup
            obtain ⟨T', hT'⟩ := ih hLookup
            by_cases hyx : y = x
            · subst hyx
              exact ⟨U, by simp [lookupSEnv, List.lookup]⟩
            · have hbeq : (y == x) = false := by
                exact beq_eq_false_iff_ne.mpr hyx
              exact ⟨T', by simpa [lookupSEnv, List.lookup, hbeq] using hT'⟩
          · by_cases hyz : y = z
            · subst hyz
              exact ⟨U, by simp [lookupSEnv, List.lookup]⟩
            · have hbeq : (y == z) = false := by
                exact beq_eq_false_iff_ne.mpr hyz
              simp [eraseSEnv, hzx, lookupSEnv, List.lookup, hbeq] at hLookup
              obtain ⟨T', hT'⟩ := ih hLookup
              exact ⟨T', by simpa [lookupSEnv, List.lookup, hbeq] using hT'⟩

-- Right-Domain Monotonicity

/-- Pre-out typing only preserves or erases right-owned bindings. -/
lemma HasTypeProcPreOut_right_domsubset_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    SEnvDomSubset Sfin.right Sown.right := by
  intro h
  induction h with
  | skip =>
      exact SEnvDomSubset_refl
  | send =>
      exact SEnvDomSubset_refl
  | recv_new _ _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | recv_old _ _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | select =>
      exact SEnvDomSubset_refl
  | branch _ _ _ _ _ _ _ hDom hRight _ =>
      simpa [hRight] using (SEnvDomSubset_refl : SEnvDomSubset _ _)
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihQ ihP
  | par _ _ hSfin _ _ _ _ _ _ _ _ _ _ _ _ =>
      simpa [hSfin] using (SEnvDomSubset_refl : SEnvDomSubset _ _)
  | assign_new _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)
  | assign_old _ _ _ =>
      simpa [OwnedEnv.updateLeft] using
        (eraseSEnv_domsubset_local : SEnvDomSubset (eraseSEnv _ _) _)

-- Left Parallel Reframing Helpers

-- Reframe To Empty Right Ownership

/-- Helper: reframe the left-par pre-out typing across an empty right frame. -/
lemma frame_left_par_reframe_local
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
  intro hP hQ
  have hP0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₂) (R':=(∅ : SEnv)) (L:=S₁) (L':=S₁')
      (G:=Gfr ++ Gleft) (P:=P)
      (DisjointS_left_empty S₁) (DisjointS_left_empty S₁') hP
  have hQ0 :=
    HasTypeProcPreOut_reframe_right
      (R:=Sown.right ++ S₁) (R':=(∅ : SEnv)) (L:=S₂) (L':=S₂')
      (G:=G₂) (P:=Q)
      (DisjointS_left_empty S₂) (DisjointS_left_empty S₂') hQ
  exact ⟨hP0, hQ0⟩

-- Assemble Empty-Right Parallel Step

/-- Helper: assemble the par case with empty right frame. -/
lemma frame_left_par_apply_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
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
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S1 } (Gfr ++ split.G1) P
      { right := (∅ : SEnv), left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S2 } split.G2 Q
      { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr G →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  intro hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hP hQ hDisjGfrG
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
    intro _ _ _
    exact hP
  exact frame_left_par (split:=split)
    (hSlen:=hSlen) (hSfin:=rfl) (hGfin:=hGfin) (hW:=hW) (hΔ:=hΔ)
    hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ
    hQ hDisjEmpty_left hDisjEmpty_fin hDisjGfrG ihP

-- Restore Right Ownership Frame

/-- Helper: restore the right-owned frame after a par step. -/
lemma frame_left_par_restore_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {S₁' S₂' : SEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv} :
    DisjointS Sown.right Sown.left →
    DisjointS Sown.right (S₁' ++ S₂') →
    HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := (∅ : SEnv), left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin →
    HasTypeProcPreOut Ssh { right := Sown.right, left := Sown.left } (Gfr ++ G)
      (.par nS nG P Q) { right := Sown.right, left := S₁' ++ S₂' } (Gfr ++ Gfin) Wfin Δfin := by
  intro hDisjIn hDisjOut hPar0
  exact HasTypeProcPreOut_reframe_right
    (R:=(∅ : SEnv)) (R':=Sown.right) (L:=Sown.left) (L':=S₁' ++ S₂')
    (G:=Gfr ++ G) (P:=.par nS nG P Q) hDisjIn hDisjOut hPar0

-- Constructive Left-Par Framing

/-- Local constructive par case for left-G framing. -/
lemma HasTypeProcPreOut_frame_G_left_par_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin : OwnedEnv} {Gfin : GEnv} {Wfin : Footprint} {Δfin : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit Sown.left G) :
    split.S1.length = nS →
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = (G₁' ++ G₂') →
    Wfin = (W₁ ++ W₂) →
    Δfin = (Δ₁ ++ Δ₂) →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointS Sown.right Sown.left →
    DisjointS Sown.right (S₁' ++ S₂') →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } (Gfr ++ split.G1) P
      { right := Sown.right ++ split.S2, left := S₁' } (Gfr ++ G₁') W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q
      { right := Sown.right ++ split.S1, left := S₂' } G₂' W₂ Δ₂ →
    DisjointG Gfr split.G1 →
    DisjointG Gfr split.G2 →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.par nS nG P Q) Sfin (Gfr ++ Gfin) Wfin Δfin := by
  intro hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjRightIn hDisjRightOut hDisjW hDisjΔ hP hQ hDisjGfrG1 hDisjGfrG2
  have hDisjGfrG : DisjointG Gfr G := by
    have hDisjGfrG' : DisjointG Gfr (split.G1 ++ split.G2) :=
      DisjointG_append_right (G₁:=Gfr) (G₂:=split.G1) (G₃:=split.G2) hDisjGfrG1 hDisjGfrG2
    simpa [split.hG] using hDisjGfrG'
  obtain ⟨hP0, hQ0⟩ := frame_left_par_reframe_local (Sown:=Sown) (Gfr:=Gfr) hP hQ
  have hPar0 :=
    frame_left_par_apply_local (split:=split) (nG:=nG)
      hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP0 hQ0 hDisjGfrG
  have hPar1 := frame_left_par_restore_local (Sown:=Sown) (Gfr:=Gfr) (G:=G)
    hDisjRightIn hDisjRightOut hPar0
  simpa [hSfin] using hPar1

-- Left G-Frame Transport

/-- Local left-frame transport for `HasTypeProcPreOut`. -/
lemma HasTypeProcPreOut_frame_G_left_local
    {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointG Gfr G →
    DisjointS Sown.right Sown.left →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    DisjointS Sown.right Sfin.left →
    HasTypeProcPreOut Ssh Sown (Gfr ++ G) P Sfin (Gfr ++ Gfin) W Δ := by
  intro hDisj hDisjRightIn h hDisjRightOut
  induction h with
  -- Base And Single-Step Cases
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hSend :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.send k x) Sown
            (updateG (Gfr ++ G) e L) [] ∅ :=
        HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone) hx
      rw [hUpd] at hSend
      exact hSend
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hRecv :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.recv k x) (OwnedEnv.updateLeft Sown x T)
            (updateG (Gfr ++ G) e L) [x] (updateSEnv ∅ x T) :=
        HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
          hNoSh hNoOwnL
      rw [hUpd] at hRecv
      exact hRecv
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hRecv :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.recv k x) (OwnedEnv.updateLeft Sown x T)
            (updateG (Gfr ++ G) e L) [x] ∅ :=
        HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
          hNoSh hOwn
      rw [hUpd] at hRecv
      exact hRecv
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
      have hSel :
          HasTypeProcPreOut Ssh Sown (Gfr ++ G) (.select k l) Sown
            (updateG (Gfr ++ G) e L) [] ∅ :=
        HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
          hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone) hbs
      rw [hUpd] at hSel
      exact hSel
  -- Branch Case Transport
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs Sfin Gfin W Δ
      have hNone := lookupG_none_of_disjoint hDisj hG
      have hBodies' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh Sown
              (updateG (Gfr ++ G) e (bs.get ⟨i, hi⟩).2)
              (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        have hBody := hBodies i hi hip
        have hDisj' : DisjointG Gfr (updateG G e (bs.get ⟨i, hi⟩).2) := by
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
        intro lbl P L hFindP hFindB
        have hDisj' : DisjointG Gfr (updateG G e L) := by
          have hDisj'0 : DisjointG (updateG G e L) Gfr :=
            disjointG_updateG_left (e:=e) (L:=L) (L0:=.branch p bs) hG (DisjointG_symm hDisj)
          exact DisjointG_symm hDisj'0
        have hOut' := ihOutLbl lbl P L hFindP hFindB hDisj' hDisjRightIn
          (by simpa [hRight] using hDisjRightOut)
        have hUpd := updateG_append_left (G₁:=Gfr) (G₂:=G) (e:=e) (L:=L) hNone
        simpa [hUpd] using hOut'
      have hSess' : SessionsOf (Gfr ++ Gfin) ⊆ SessionsOf (Gfr ++ G) := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=Gfr) (G₂:=Gfin) hs
        cases hs' with
        | inl hsL =>
            exact SessionsOf_append_left (G₂:=G) hsL
        | inr hsR =>
            exact SessionsOf_append_right (G₁:=Gfr) (hSess hsR)
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=Gfr ++ G)
        hk (by simpa [hG] using lookupG_append_right (G₁:=Gfr) (G₂:=G) (e:=e) hNone)
        hLen hLabels hBodies' hOutLbl' hSess' hDom hRight
  -- Sequential Composition Case
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hDomQ : SEnvDomSubset S₁.left S₂.left := HasTypeProcPreOut_domsubset hQ
      have hDisjRightMid : DisjointS Sown.right S₁.left :=
        DisjointS_of_domsubset_right hDomQ hDisjRightOut
      have hP' := ihP hDisj hDisjRightIn hDisjRightMid
      have hSubRightMid : SEnvDomSubset S₁.right Sown.right :=
        HasTypeProcPreOut_right_domsubset_local hP
      have hDisjMidIn : DisjointS S₁.right S₁.left :=
        DisjointS_of_domsubset_left hSubRightMid hDisjRightMid
      have hDisjMidOut : DisjointS S₁.right S₂.left :=
        DisjointS_of_domsubset_left hSubRightMid hDisjRightOut
      have hSubG1 : SessionsOf G₁ ⊆ SessionsOf G :=
        SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG1fr : DisjointG Gfr G₁ := by
        have hDisj' : DisjointG G₁ Gfr := DisjointG_of_subset_left hSubG1 (DisjointG_symm hDisj)
        exact DisjointG_symm hDisj'
      exact HasTypeProcPreOut.seq hP' (ihQ hDisjG1fr hDisjMidIn hDisjMidOut)
  -- Parallel Composition Case
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin W Δ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      have hDisjG1fr : DisjointG split.G1 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).1
      have hDisjG2fr : DisjointG split.G2 Gfr :=
        (disjointG_split_frame_right (split:=split) (DisjointG_symm hDisj)).2
      have hDisjGfrG1 : DisjointG Gfr split.G1 := DisjointG_symm hDisjG1fr
      have hDisjGfrG2 : DisjointG Gfr split.G2 := DisjointG_symm hDisjG2fr
      have hDisjRightS1 : DisjointS Sown.right split.S1 := by
        have hSubS1 : SEnvDomSubset split.S1 Sown.left := by
          simpa [split.hS] using (SEnvDomSubset_append_left (S₁:=split.S1) (S₂:=split.S2))
        exact DisjointS_of_domsubset_right hSubS1 hDisjRightIn
      have hDisjRightS2 : DisjointS Sown.right split.S2 := by
        have hSubS2 : SEnvDomSubset split.S2 Sown.left := by
          simpa [split.hS] using (SEnvDomSubset_append_right (S₁:=split.S1) (S₂:=split.S2))
        exact DisjointS_of_domsubset_right hSubS2 hDisjRightIn
      have hDisjRightOut' : DisjointS Sown.right (S₁' ++ S₂') := by
        simpa [hSfin] using hDisjRightOut
      have hDisjRightS1' : DisjointS Sown.right S₁' := by
        have hSubS1' : SEnvDomSubset S₁' (S₁' ++ S₂') := by
          simpa using (SEnvDomSubset_append_left (S₁:=S₁') (S₂:=S₂'))
        exact DisjointS_of_domsubset_right hSubS1' hDisjRightOut'
      have hDisjPIn : DisjointS (Sown.right ++ split.S2) split.S1 :=
        DisjointS_append_left hDisjRightS1 (DisjointS_symm hDisjS)
      have hDisjPOut : DisjointS (Sown.right ++ split.S2) S₁' :=
        DisjointS_append_left hDisjRightS1' (DisjointS_symm hDisjS_left)
      have hP' := ihP hDisjGfrG1 hDisjPIn hDisjPOut
      exact HasTypeProcPreOut_frame_G_left_par_local (Ssh:=Ssh) (Gfr:=Gfr) (split:=split)
        hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
        hDisjRightIn hDisjRightOut' hDisjW hDisjΔ hP' hQ hDisjGfrG1 hDisjGfrG2
  -- Assignment Cases
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnL (HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      exact HasTypeProcPreOut.assign_old hNoSh hOwn (HasTypeVal_frame_left (G₁:=Gfr) (G₂:=G) hDisj hv)


  /- Full-G step rule: preserve pre-out typing when stepping in the middle of a G-frame.
  This is kept as an explicit proposition so downstream proofs can thread it
  as a hypothesis while the constructive proof is being migrated.
-/

end
