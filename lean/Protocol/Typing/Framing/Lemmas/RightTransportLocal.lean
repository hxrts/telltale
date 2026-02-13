
import Protocol.Typing.Framing.Lemmas.FrameOutRight

/-! # Right Transport Local Lemmas

Local right-framing transport lemmas for `HasTypeProcPre`, showing
process typing extends when GEnv is appended on the right. -/

/-
The Problem. Right-framing (`G ++ Gfr`) requires showing that pre-typing
in `G` lifts to `G ++ Gfr`. For branch bodies, we also need to show
update operations commute with the append.

Solution Structure. Prove `pre_frame_right_branch_bodies_local` for
branch body transport. Prove `HasTypeProcPre_frame_G_right_local` for
general right-framing by induction on pre-typing.
-/

/- ## Structured Block 1 -/
set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

-- Branch Bodies Right Transport

lemma pre_frame_right_branch_bodies_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
    lookupG G e = some (.branch p bs) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG G e (bs.get ⟨i, hi⟩).2 ++ Gfr)
          (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G ++ Gfr) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) := by
  intro hG ihBodies i hi hip
  have hBody' := ihBodies i hi hip
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
  rw [hUpd]
  exact hBody'

-- Pre-Typing Right-Frame Transport

/-- Local right-frame transport for `HasTypeProcPre`. -/
lemma HasTypeProcPre_frame_G_right_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process} :
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown (G ++ Gfr) P := by
  intro h
  induction h with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPre.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      exact HasTypeProcPre.send hk (lookupG_append_left (G₂:=Gfr) hG) hx
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      exact HasTypeProcPre.recv hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      exact HasTypeProcPre.select hk (lookupG_append_left (G₂:=Gfr) hG) hbs
  | branch hk hG hLen hLabels hBodies ihBodies =>
      rename_i Sown G k procs e p bs
      have hBodies' := pre_frame_right_branch_bodies_local (G:=G) (Gfr:=Gfr) hG ihBodies
      exact HasTypeProcPre.branch hk (lookupG_append_left (G₂:=Gfr) hG) hLen hLabels hBodies'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq ihP ihQ
  | par hDisjS hSsplit hP hQ ihP ihQ =>
      exact HasTypeProcPre.par hDisjS hSsplit ihP ihQ
/- ## Structured Block 2 -/
  | assign hNoSh hv =>
      rename_i Sown G x v T
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)

-- Pre-Out Branch Helpers

/-- Helper: extend branch bodies under a right G-frame (pre-out typing). -/
lemma frame_right_branch_bodies_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)} :
    lookupG G e = some (.branch p bs) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG G e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G ++ Gfr) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2) := by
  intro hG hBodies i hi hip
  have hBody := hBodies i hi hip
  have hBody' := HasTypeProcPre_frame_G_right_local (Gfr:=Gfr) hBody
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
    (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hG
  rw [hUpd]
  exact hBody'

/-- Helper: extend branch continuations under a right G-frame (pre-out typing). -/
lemma frame_right_branch_out_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {e : Endpoint} {p : Role}
    {bs : List (Label × LocalType)} {procs : List (Label × Process)}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    lookupG G e = some (.branch p bs) →
    (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        DisjointG (updateG G e L) Gfr →
        HasTypeProcPreOut Ssh Sown (updateG G e L ++ Gfr) P Sfin (Gfin ++ Gfr) W Δ) →
    DisjointG G Gfr →
    (∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh Sown (updateG (G ++ Gfr) e L) P Sfin (Gfin ++ Gfr) W Δ) := by
  intro hG ihOutLbl hDisj lbl P L hFindP hFindB
  have hDisj' : DisjointG (updateG G e L) Gfr :=
    disjointG_updateG_left (e:=e) (L:=L) (L0:=.branch p bs) hG hDisj
  have hOut' := ihOutLbl lbl P L hFindP hFindB hDisj'
  have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e) (L:=.branch p bs) (L':=L) hG
  simpa [hUpd] using hOut'

-- Parallel Case Helper

/-- Helper: par case for right-frame pre-out transport. -/
lemma frame_pre_out_right_par_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P Q : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv}
    {S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂} {nS nG : Nat}
    (split : ParSplit Sown.left G) :
    DisjointG G Gfr →
    split.S1.length = nS →
/- ## Structured Block 3 -/
    Sfin = { right := Sown.right, left := S₁' ++ S₂' } →
    Gfin = G₁' ++ G₂' →
    W = W₁ ++ W₂ →
    Δ = Δ₁ ++ Δ₂ →
    DisjointG split.G1 split.G2 →
    DisjointS split.S1 split.S2 →
    DisjointS S₁' split.S2 →
    DisjointS split.S1 S₂' →
    DisjointS S₁' S₂' →
    DisjointW W₁ W₂ →
    DisjointS Δ₁ Δ₂ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S2, left := split.S1 } split.G1 P
      { right := Sown.right ++ split.S2, left := S₁' } G₁' W₁ Δ₁ →
    HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } split.G2 Q
      { right := Sown.right ++ split.S1, left := S₂' } G₂' W₂ Δ₂ →
    (DisjointG split.G2 Gfr →
      HasTypeProcPreOut Ssh { right := Sown.right ++ split.S1, left := split.S2 } (split.G2 ++ Gfr) Q
        { right := Sown.right ++ split.S1, left := S₂' } (G₂' ++ Gfr) W₂ Δ₂) →
    HasTypeProcPreOut Ssh Sown (G ++ Gfr) (.par nS nG P Q) Sfin (Gfin ++ Gfr) W Δ := by
  intro hDisj hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
    hDisjW hDisjΔ hP hQ ihQ
  let splitOut : ParSplit Sown.left (G ++ Gfr) :=
    { S1 := split.S1
      S2 := split.S2
      G1 := split.G1
      G2 := split.G2 ++ Gfr
      hS := by simpa using split.hS
      hG := by simpa [split.hG, List.append_assoc] }
  -- Derived Disjointness And Reconstruction
  have hDisjG1fr : DisjointG split.G1 Gfr :=
    (disjointG_split_frame_right (split:=split) hDisj).1
  have hDisjG2fr : DisjointG split.G2 Gfr :=
    (disjointG_split_frame_right (split:=split) hDisj).2
  have hDisjGOut : DisjointG splitOut.G1 splitOut.G2 := by
    have hDisjG' : DisjointG (split.G2 ++ Gfr) split.G1 :=
      DisjointG_append_left (DisjointG_symm hDisjG) (DisjointG_symm hDisjG1fr)
    exact DisjointG_symm (by simpa [splitOut] using hDisjG')
  have hQ' := ihQ hDisjG2fr
  have hGfin' : (G₁' ++ G₂') ++ Gfr = G₁' ++ (G₂' ++ Gfr) := by
    simp [List.append_assoc]
  refine HasTypeProcPreOut.par (G₂':=G₂' ++ Gfr) splitOut ?_ ?_ ?_ ?_ ?_ hDisjGOut hDisjS
    hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP ?_
  · simpa [splitOut] using hSlen
  · simpa [hSfin] using rfl
  · simpa [hGfin, hGfin', splitOut] using rfl
  · simpa [hW] using rfl
  · simpa [hΔ] using rfl
  · simpa [splitOut] using hQ'

-- Pre-Out Right-Frame Transport

/-- Local right-frame transport for `HasTypeProcPreOut`. -/
lemma HasTypeProcPreOut_frame_G_right_local
    {Ssh : SEnv} {Sown : OwnedEnv} {G Gfr : GEnv} {P : Process}
    {Sfin : OwnedEnv} {Gfin : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
/- ## Structured Block 4 -/
    DisjointG G Gfr →
    HasTypeProcPreOut Ssh Sown G P Sfin Gfin W Δ →
    HasTypeProcPreOut Ssh Sown (G ++ Gfr) P Sfin (Gfin ++ Gfr) W Δ := by
  intro hDisj h
  induction h with
  -- Base And Single-Step Cases
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.send q T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hx)
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh hNoOwnL)
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.recv p T L) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hNoSh hOwn)
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hUpd := updateG_append_left_hit (G₁:=G) (G₂:=Gfr) (e:=e)
        (L:=.select q bs) (L':=L) hG
      simpa [hUpd] using
        (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
          hk (lookupG_append_left (G₂:=Gfr) hG) hbs)
  -- Branch Case Transport
  | branch hk hG hLen hLabels hBodies hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs Sfin Gfin W Δ
      have hBodies' := frame_right_branch_bodies_local (G:=G) (Gfr:=Gfr) hG hBodies
      have hOutLbl' := frame_right_branch_out_local (G:=G) (Gfr:=Gfr) hG ihOutLbl hDisj
      have hSess' : SessionsOf (Gfin ++ Gfr) ⊆ SessionsOf (G ++ Gfr) := by
        intro s hs
        have hs' := SessionsOf_append_subset (G₁:=Gfin) (G₂:=Gfr) hs
        cases hs' with
        | inl hsL =>
            exact SessionsOf_append_left (G₂:=Gfr) (hSess hsL)
        | inr hsR =>
            exact SessionsOf_append_right (G₁:=G) hsR
      exact HasTypeProcPreOut.branch (Ssh:=Ssh) (Sown:=Sown) (G:=G ++ Gfr)
        hk (lookupG_append_left (G₂:=Gfr) hG) hLen hLabels hBodies' hOutLbl' hSess' hDom hRight
  -- Sequential And Parallel Cases
/- ## Structured Block 5 -/
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      have hP' := ihP hDisj
      have hSubG1 : SessionsOf G₁ ⊆ SessionsOf G := SessionsOf_subset_of_HasTypeProcPreOut hP
      have hDisjG1fr : DisjointG G₁ Gfr := DisjointG_of_subset_left hSubG1 hDisj
      exact HasTypeProcPreOut.seq hP' (ihQ hDisjG1fr)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin W Δ S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      exact frame_pre_out_right_par_local (split:=split)
        hDisj hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
        hDisjW hDisjΔ hP hQ ihQ
  -- Assignment Cases
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      exact HasTypeProcPreOut.assign_new hNoSh hNoOwnL (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      exact HasTypeProcPreOut.assign_old hNoSh hOwn (HasTypeVal_frame_right (G₁:=G) (G₂:=Gfr) hv)

-- Local G-Frame Transport (Left)

end
