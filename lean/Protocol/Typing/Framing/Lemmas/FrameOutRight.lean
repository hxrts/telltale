import Protocol.Typing.Framing.Lemmas.FrameLeftConstructors

/-! # Output Framing Right

Reframing theorems for `HasTypeProcPreOut`, allowing the right-owned
SEnv portion to be replaced while preserving the typing judgment. -/

/-
The Problem. `HasTypeProcPreOut` tracks both input and output SEnv
states. When composing with parallel processes, we need to replace
the right-owned portion without invalidating the typing derivation.

Solution Structure. Prove `HasTypeProcPreOut_reframe_right_general`
by induction on the output typing. For each constructor, show the
right-owned portion is only used for lookups that don't conflict
with the left-owned portion under disjointness.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Right Reframing -/

theorem HasTypeProcPreOut_reframe_right_general
    {Ssh : SEnv} {Sown : OwnedEnv} {G : GEnv} {P : Process}
    {Sfin : OwnedEnv} {G' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    HasTypeProcPreOut Ssh Sown G P Sfin G' W Δ →
    ∀ {R' : SEnv},
      DisjointS R' Sown.left →
      DisjointS R' Sfin.left →
      HasTypeProcPreOut Ssh { right := R', left := Sown.left } G P
        { right := R', left := Sfin.left } G' W Δ := by
  intro h
  induction h with
  | skip =>
      intro R' hDisjIn hDisjOut
      exact HasTypeProcPreOut.skip
  /-! ## Reframe Right: send case -/
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hx' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) x = some T := by
        simpa [SEnvVisible] using hx
      exact HasTypeProcPreOut.send hk' hG hx'
  /-! ## Reframe Right: recv cases -/
  | recv_new hk hG hNoSh hNoOwnL =>
      rename_i Sown G k x e p T L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hk' hG hNoSh hNoOwnL)
  | recv_old hk hG hNoSh hOwn =>
      rename_i Sown G k x e p T L T'
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hk' hG hNoSh hOwn)
  /-! ## Reframe Right: select and branch cases -/
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      exact HasTypeProcPreOut.select hk' hG hFind
  | branch hk hG hLen hLbl hPre hOutLbl hSess hDom hRight ihOutLbl =>
      rename_i Sown G k procs e p bs S' G' W Δ
      intro R' hDisjIn hDisjOut
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := R', left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible] using hk
      have hOutLbl' :
          ∀ lbl P Lx,
            procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
            bs.find? (fun b => b.1 == lbl) = some (lbl, Lx) →
            HasTypeProcPreOut Ssh { right := R', left := Sown.left } (updateG G e Lx) P
              { right := R', left := S'.left } G' W Δ := by
        intro lbl P Lx hFindP hFindB
        exact ihOutLbl lbl P Lx hFindP hFindB (R':=R') hDisjIn hDisjOut
      have hPre' :
          ∀ j (hj : j < bs.length) (hjp : j < procs.length),
            HasTypeProcPre Ssh { right := R', left := Sown.left }
              (updateG G e (bs.get ⟨j, hj⟩).2)
              (procs.get ⟨j, hjp⟩).2 := by
        intro j hj hjp
        exact HasTypeProcPre_reframe_right
          (Sown:=Sown) (Sown':={ right := R', left := Sown.left }) rfl
          (hPre j hj hjp)
      exact HasTypeProcPreOut.branch hk' hG hLen hLbl hPre' hOutLbl' hSess hDom rfl
  /-! ## Reframe Right: seq/par cases -/
  | seq hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ G₁ S₂ G₂ W₁ W₂ Δ₁ Δ₂
      intro R' hDisjIn hDisjOut
      have hDomQ : SEnvDomSubset S₁.left S₂.left := HasTypeProcPreOut_domsubset hQ
      have hDisjMid : DisjointS R' S₁.left :=
        DisjointS_of_domsubset_right hDomQ hDisjOut
      exact HasTypeProcPreOut.seq
        (ihP (R':=R') hDisjIn hDisjMid)
        (ihQ (R':=R') hDisjMid hDisjOut)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i Sown G P Q Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      intro R' hDisjIn hDisjOut
      have hDisjInSplit : DisjointS R' (split.S1 ++ split.S2) := by
        simpa [split.hS] using hDisjIn
      have hDisjIn1 : DisjointS R' split.S1 := DisjointS_of_append_left hDisjInSplit
      have hDisjIn2 : DisjointS R' split.S2 := DisjointS_of_append_right hDisjInSplit
      have hDisjOutSplit : DisjointS R' (S₁' ++ S₂') := by
        simpa [hSfin] using hDisjOut
      have hDisjOut1 : DisjointS R' S₁' := DisjointS_of_append_left hDisjOutSplit
      have hDisjOut2 : DisjointS R' S₂' := DisjointS_of_append_right hDisjOutSplit
      have hDisjInP : DisjointS (R' ++ split.S2) split.S1 :=
        DisjointS_append_left hDisjIn1 (DisjointS_symm hDisjS)
      have hDisjOutP : DisjointS (R' ++ split.S2) S₁' :=
        DisjointS_append_left hDisjOut1 (DisjointS_symm hDisjS_left)
      have hDisjInQ : DisjointS (R' ++ split.S1) split.S2 :=
        DisjointS_append_left hDisjIn2 hDisjS
      have hDisjOutQ : DisjointS (R' ++ split.S1) S₂' :=
        DisjointS_append_left hDisjOut2 hDisjS_right
      have hP' :
          HasTypeProcPreOut Ssh { right := R' ++ split.S2, left := split.S1 } split.G1 P
            { right := R' ++ split.S2, left := S₁' } G₁' W₁ Δ₁ :=
        ihP (R':=R' ++ split.S2) hDisjInP hDisjOutP
      have hQ' :
          HasTypeProcPreOut Ssh { right := R' ++ split.S1, left := split.S2 } split.G2 Q
            { right := R' ++ split.S1, left := S₂' } G₂' W₂ Δ₂ :=
        ihQ (R':=R' ++ split.S1) hDisjInQ hDisjOutQ
      have hPar' :
          HasTypeProcPreOut Ssh { right := R', left := Sown.left } G (.par nS nG P Q)
            { right := R', left := S₁' ++ S₂' } (G₁' ++ G₂') (W₁ ++ W₂) (Δ₁ ++ Δ₂) :=
        HasTypeProcPreOut.par split hSlen rfl rfl rfl rfl
          hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP' hQ'
      simpa [hSfin, hGfin, hW, hΔ] using hPar'
  /-! ## Reframe Right: assignment cases -/
  | assign_new hNoSh hNoOwnL hv =>
      rename_i Sown G x v T
      intro R' hDisjIn hDisjOut
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      have hNoOwnL' : lookupSEnv ({ right := R', left := Sown.left } : OwnedEnv).left x = none := by
        simpa using hNoOwnL
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hNoSh hNoOwnL' hv)
  | assign_old hNoSh hOwn hv =>
      rename_i Sown G x v T T'
      intro R' hDisjIn hDisjOut
      have hDisjOut' : DisjointS R' (updateSEnv Sown.left x T) := by
        simpa [OwnedEnv.updateLeft] using hDisjOut
      have hxOut : lookupSEnv (updateSEnv Sown.left x T) x = some T := by
        simpa using (lookupSEnv_update_eq (env:=Sown.left) (x:=x) (T:=T))
      have hNoOwnR' : lookupSEnv R' x = none :=
        lookupSEnv_none_of_disjoint_left hDisjOut' hxOut
      have hErase : eraseSEnv R' x = R' := eraseSEnv_of_lookup_none hNoOwnR'
      have hOwn' : lookupSEnv ({ right := R', left := Sown.left } : OwnedEnv).left x = some T' := by
        simpa using hOwn
      simpa [OwnedEnv.updateLeft, hErase] using
        (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:={ right := R', left := Sown.left })
          (G:=G) hNoSh hOwn' hv)

/-! ## Reframe Right Wrapper -/

theorem HasTypeProcPreOut_reframe_right
    {Ssh R R' L : SEnv} {G : GEnv} {P : Process}
    {L' : SEnv} {G' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS R' L →
    DisjointS R' L' →
    HasTypeProcPreOut Ssh { right := R, left := L } G P { right := R, left := L' } G' W Δ →
    HasTypeProcPreOut Ssh { right := R', left := L } G P { right := R', left := L' } G' W Δ := by
  intro hDisjIn hDisjOut h
  simpa using
    (HasTypeProcPreOut_reframe_right_general
      (Ssh:=Ssh) (Sown:={ right := R, left := L }) (G:=G) (P:=P)
      (Sfin:={ right := R, left := L' }) (G':=G') (W:=W) (Δ:=Δ)
      h (R':=R') hDisjIn hDisjOut)

/-! ## Left-Par Framing with Right Reframing -/

/-- Left framing for par: frame only the left component. -/
theorem frame_left_par
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {P Q : Process} {nS nG : Nat}
    {Sfin Gfin Wfin Δfin S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂}
    (split : ParSplit S₂ G₂)
    (hSlen : split.S1.length = nS)
    (hSfin : Sfin = S₁' ++ S₂')
    (hGfin : Gfin = G₁' ++ G₂')
    (hW : Wfin = W₁ ++ W₂)
    (hΔ : Δfin = Δ₁ ++ Δ₂)
    (hDisjG : DisjointG split.G1 split.G2)
    (hDisjS : DisjointS split.S1 split.S2)
    (hDisjS_left : DisjointS S₁' split.S2)
    (hDisjS_right : DisjointS split.S1 S₂')
    (hDisjS' : DisjointS S₁' S₂')
    (hDisjW : DisjointW W₁ W₂)
    (hDisjΔ : DisjointS Δ₁ Δ₂)
    (hQ : HasTypeProcPreOut Ssh split.S2 split.G2 Q S₂' G₂' W₂ Δ₂)
    (hDisjS_frame : DisjointS S₁ S₂)
    (hDisjS_frame' : DisjointS S₁ Sfin)
    (hDisjG_frame : DisjointG G₁ G₂)
    (ihP : DisjointS S₁ split.S1 → DisjointS S₁ S₁' → DisjointG G₁ split.G1 →
      HasTypeProcPreOut Ssh { right := S₁, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁, left := S₁' } (G₁ ++ G₁') W₁ Δ₁) :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.par nS nG P Q)
      { right := S₁, left := Sfin } (G₁ ++ Gfin) Wfin Δfin := by
  /-! ## Left-Par Framing: subset and disjoint setup -/
  have hSubSplit1 : SEnvDomSubset split.S1 S₂ := by
    simpa [split.hS] using (SEnvDomSubset_append_left (S₁:=split.S1) (S₂:=split.S2))
  have hSubSplit2 : SEnvDomSubset split.S2 S₂ := by
    simpa [split.hS] using (SEnvDomSubset_append_right (S₁:=split.S1) (S₂:=split.S2))
  have hSubSfin1 : SEnvDomSubset S₁' Sfin := by
    simpa [hSfin] using (SEnvDomSubset_append_left (S₁:=S₁') (S₂:=S₂'))
  have hSubSfin2 : SEnvDomSubset S₂' Sfin := by
    simpa [hSfin] using (SEnvDomSubset_append_right (S₁:=S₁') (S₂:=S₂'))
  have hDisjS_frame_1 : DisjointS S₁ split.S1 :=
    DisjointS_of_domsubset_right hSubSplit1 hDisjS_frame
  have hDisjS_frame_2 : DisjointS S₁ split.S2 :=
    DisjointS_of_domsubset_right hSubSplit2 hDisjS_frame
  have hDisjS_frame_1' : DisjointS S₁ S₁' :=
    DisjointS_of_domsubset_right hSubSfin1 hDisjS_frame'
  have hDisjS_frame_2' : DisjointS S₁ S₂' :=
    DisjointS_of_domsubset_right hSubSfin2 hDisjS_frame'
  have hSubG1 : SessionsOf split.G1 ⊆ SessionsOf G₂ := by
    simpa [split.hG] using (SessionsOf_append_left (G₁:=split.G1) (G₂:=split.G2))
  have hSubG2 : SessionsOf split.G2 ⊆ SessionsOf G₂ := by
    simpa [split.hG] using (SessionsOf_append_right (G₁:=split.G1) (G₂:=split.G2))
  have hDisjGsym : DisjointG G₂ G₁ := DisjointG_symm hDisjG_frame
  have hDisjG_frame_1 : DisjointG G₁ split.G1 := by
    exact DisjointG_symm (DisjointG_of_subset_left hSubG1 hDisjGsym)
  have hDisjG_frame_2 : DisjointG G₁ split.G2 := by
    exact DisjointG_symm (DisjointG_of_subset_left hSubG2 hDisjGsym)
  /-! ## Left-Par Framing: reframe P/Q subderivations -/
  have hP0 :
      HasTypeProcPreOut Ssh { right := S₁, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁, left := S₁' } (G₁ ++ G₁') W₁ Δ₁ :=
    ihP hDisjS_frame_1 hDisjS_frame_1' hDisjG_frame_1
  have hDisjInP : DisjointS (S₁ ++ split.S2) split.S1 :=
    DisjointS_append_left hDisjS_frame_1 (DisjointS_symm hDisjS)
  have hDisjOutP : DisjointS (S₁ ++ split.S2) S₁' :=
    DisjointS_append_left hDisjS_frame_1' (DisjointS_symm hDisjS_left)
  have hP :
      HasTypeProcPreOut Ssh { right := S₁ ++ split.S2, left := split.S1 } (G₁ ++ split.G1) P
        { right := S₁ ++ split.S2, left := S₁' } (G₁ ++ G₁') W₁ Δ₁ :=
    HasTypeProcPreOut_reframe_right
      (R:=S₁) (R':=S₁ ++ split.S2) (L:=split.S1) (L':=S₁')
      (G:=G₁ ++ split.G1) (P:=P) hDisjInP hDisjOutP hP0
  have hQ0 :
      HasTypeProcPreOut Ssh { right := (∅ : SEnv), left := split.S2 } split.G2 Q
        { right := (∅ : SEnv), left := S₂' } G₂' W₂ Δ₂ := by
    simpa using hQ
  have hDisjInQ : DisjointS (S₁ ++ split.S1) split.S2 :=
    DisjointS_append_left hDisjS_frame_2 hDisjS
  have hDisjOutQ : DisjointS (S₁ ++ split.S1) S₂' :=
    DisjointS_append_left hDisjS_frame_2' hDisjS_right
  have hQ' :
      HasTypeProcPreOut Ssh { right := S₁ ++ split.S1, left := split.S2 } split.G2 Q
        { right := S₁ ++ split.S1, left := S₂' } G₂' W₂ Δ₂ :=
    HasTypeProcPreOut_reframe_right
      (R:=(∅ : SEnv)) (R':=S₁ ++ split.S1) (L:=split.S2) (L':=S₂')
      (G:=split.G2) (P:=Q) hDisjInQ hDisjOutQ hQ0
  /-! ## Left-Par Framing: assemble final par judgment -/
  have hDisjG_out : DisjointG (G₁ ++ split.G1) split.G2 :=
    DisjointG_append_left hDisjG_frame_2 hDisjG
  let splitOut : ParSplit S₂ (G₁ ++ G₂) :=
    { S1 := split.S1
      S2 := split.S2
      G1 := G₁ ++ split.G1
      G2 := split.G2
      hS := split.hS
      hG := by simpa [List.append_assoc, split.hG] }
  have hPar :
      HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.par nS nG P Q)
        { right := S₁, left := S₁' ++ S₂' } ((G₁ ++ G₁') ++ G₂') (W₁ ++ W₂) (Δ₁ ++ Δ₂) :=
    HasTypeProcPreOut.par splitOut hSlen rfl rfl rfl rfl
      hDisjG_out hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ'
  simpa [hSfin, hGfin, hW, hΔ, List.append_assoc] using hPar

/-! ## Local G-Frame Transport (Right) -/

end
