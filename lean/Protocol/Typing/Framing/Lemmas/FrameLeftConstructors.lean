import Protocol.Typing.Framing.Lemmas.FrameLeftCore

/-! # Left Frame Constructor Lemmas

Per-constructor left-framing lemmas for `HasTypeProcPreOut`, showing
each process form preserves typing when GEnv is extended on the left. -/

/-
The Problem. Full left-framing requires showing each process constructor
(skip, send, recv, select, branch, par, seq) lifts through GEnv extension.
Each constructor has different lookup and update patterns.

Solution Structure. Prove `frame_left_skip`, `frame_left_send`, etc.
for each process constructor. Use core lemmas from `FrameLeftCore` to
lift lookups and push updates into the appropriate GEnv portion.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Skip and Send Framing -/

theorem frame_left_skip {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} :
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) .skip
      { right := S₁, left := S₂ } (G₁ ++ G₂) [] ∅ := by
  -- Skip leaves environments unchanged.
  simpa using
    (HasTypeProcPreOut.skip (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂))

/-- Left framing for send. -/
theorem frame_left_send
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {q : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.send q T L) →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) x = some T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.send k x)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hx
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hx' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) x = some T := by
    simpa [SEnvVisible] using hx
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.send (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ }) (G:=G₁ ++ G₂) hk' hG' hx')

/-- Left framing for recv_new. -/
theorem frame_left_recv_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to show x is not in the left frame.
  intro hDisjS hDisjS' hDisjG hk hG hSsh hSown
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := by
    have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by simp [lookupSEnv_update_eq]
    exact lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft, hErase, hUpdG] using
    (HasTypeProcPreOut.recv_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hLeft)

/-- Left framing for recv_old. -/
theorem frame_left_recv_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k x : Var} {e : Endpoint} {p : Role}
    {T : ValType} {L : LocalType} {T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.recv p T L) →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.recv k x)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ updateG G₂ e L) [x] ∅ := by
  -- Old recv: x already in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hk hG hSsh hSown
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpdG := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  have hRight : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft, hErase, hUpdG] using
    (HasTypeProcPreOut.recv_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hSsh hLeft)

/-- Left framing for select. -/
theorem frame_left_select
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {l : Label} {e : Endpoint}
    {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.select q bs) →
    bs.find? (fun b => b.1 == l) = some (l, L) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.select k l)
      { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) [] ∅ := by
  -- Lift lookups and push update into the right GEnv.
  intro hDisjS hDisjG hk hG hFind
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using
    (HasTypeProcPreOut.select (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hk' hG' hFind)

/-- Frame-left helper for branch pre-typing. -/
theorem frame_left_pre_updateG
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {e : Endpoint} {L L0 : LocalType} {P : Process} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L0 →
    HasTypeProcPre Ssh S₂ (updateG G₂ e L) P →
    HasTypeProcPre Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L) P := by
  -- Frame pre-typing and rewrite the update on G.
  intro hDisjS hDisjG hG hPre
  have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
    DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L0) (L':=L) hDisjG hG
  have hDisjR : DisjointS S₁ ([] : SEnv) := by
    simpa using (DisjointS_symm (DisjointS_left_empty S₁))
  have hPre' := HasTypeProcPre_frame_left (Sframe:=S₁) (Sown:=(S₂ : OwnedEnv))
    (G₁:=G₁) (G₂:=updateG G₂ e L) hDisjR hDisjS hDisjG' hPre
  have hDisjSym := DisjointG_symm hDisjG
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
  have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
  simpa [hUpd] using hPre'

/-- Left framing for branch. -/
theorem frame_left_branch
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)}
    {S₂' : SEnv} {G₂' : GEnv} {W : Footprint} {Δ : DeltaSEnv} :
    DisjointS S₁ S₂ →
    DisjointS S₁ S₂' →
    DisjointG G₁ G₂ →
    lookupSEnv (SEnvVisible Ssh (S₂ : OwnedEnv)) k = some (.chan e.sid e.role) →
    lookupG G₂ e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      (procs.get ⟨j, hjp⟩).1 = (bs.get ⟨j, hj⟩).1) →
    (∀ j (hj : j < bs.length) (hjp : j < procs.length),
      HasTypeProcPre Ssh S₂ (updateG G₂ e (bs.get ⟨j, hj⟩).2) (procs.get ⟨j, hjp⟩).2) →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      HasTypeProcPreOut Ssh S₂ (updateG G₂ e L) P S₂' G₂' W Δ) →
    SessionsOf G₂' ⊆ SessionsOf G₂ →
    SEnvDomSubset S₂ S₂' →
    (∀ lbl P L,
      procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
      bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
      DisjointS S₁ S₂ →
      DisjointS S₁ S₂' →
      DisjointG G₁ (updateG G₂ e L) →
      HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ updateG G₂ e L) P
        { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ) →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.branch k procs)
      { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
  -- Frame each branch using the provided IH and rebuild the constructor.
  intro hDisjS hDisjS' hDisjG hk hG hLen hLbl hProcs hOut hSess hDom ih
  have hk' :
      lookupSEnv (SEnvVisible Ssh { right := S₁, left := S₂ }) k = some (.chan e.sid e.role) := by
    simpa [SEnvVisible] using hk
  have hG' := lookupG_frame_left hDisjG hG
  have hProcs' :
      ∀ j (hj : j < bs.length) (hjp : j < procs.length),
        HasTypeProcPre Ssh { right := S₁, left := S₂ }
          (updateG (G₁ ++ G₂) e (bs.get ⟨j, hj⟩).2)
          (procs.get ⟨j, hjp⟩).2 := by
    intro j hj hjp
    exact frame_left_pre_updateG hDisjS hDisjG hG (hProcs j hj hjp)
  have hOut' :
      ∀ lbl P L,
        procs.find? (fun b => b.1 == lbl) = some (lbl, P) →
        bs.find? (fun b => b.1 == lbl) = some (lbl, L) →
        HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (updateG (G₁ ++ G₂) e L)
          P { right := S₁, left := S₂' } (G₁ ++ G₂') W Δ := by
    intro lbl P L hP hB
    have hDisjG' : DisjointG G₁ (updateG G₂ e L) :=
      DisjointG_updateG_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=.branch p bs) (L':=L) hDisjG hG
    have hPre' := ih lbl P L hP hB hDisjS hDisjS' hDisjG'
    have hDisjSym := DisjointG_symm hDisjG
    have hNone : lookupG G₁ e = none :=
      DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hG
    have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hNone
    simpa [hUpd] using hPre'
  have hSess' : SessionsOf (G₁ ++ G₂') ⊆ SessionsOf (G₁ ++ G₂) := by
    intro s hs
    have hs' := SessionsOf_append_subset (G₁:=G₁) (G₂:=G₂') hs
    cases hs' with
    | inl hsL =>
        exact SessionsOf_append_left (G₂:=G₂) hsL
    | inr hsR =>
        exact SessionsOf_append_right (G₁:=G₁) (hSess hsR)
  exact HasTypeProcPreOut.branch hk' hG' hLen hLbl hProcs' hOut' hSess' hDom rfl

/-- Left framing for assign_new. -/
theorem frame_left_assign_new
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T : ValType} :
    DisjointS S₁ (updateSEnv S₂ x T) →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = none →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] (updateSEnv ∅ x T) := by
  -- Use disjointness to keep x absent from the left frame.
  intro hDisjS' hDisjG hSsh hSown hv
  have hx2 : lookupSEnv (updateSEnv S₂ x T) x = some T := by
    simp [lookupSEnv_update_eq]
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS' hx2
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = none := hSown
  simpa [OwnedEnv.updateLeft, hErase] using
    (HasTypeProcPreOut.assign_new (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hLeft hv')

/-- Left framing for assign_old. -/
theorem frame_left_assign_old
    {Ssh S₁ S₂ : SEnv} {G₁ G₂ : GEnv} {x : Var} {v : Value} {T T' : ValType} :
    DisjointS S₁ S₂ →
    DisjointG G₁ G₂ →
    lookupSEnv Ssh x = none →
    lookupSEnv S₂ x = some T' →
    HasTypeVal G₂ v T →
    HasTypeProcPreOut Ssh { right := S₁, left := S₂ } (G₁ ++ G₂) (.assign x v)
      { right := S₁, left := updateSEnv S₂ x T } (G₁ ++ G₂) [x] ∅ := by
  -- Old assignment: x is in S₂, so not in S₁ by disjointness.
  intro hDisjS hDisjG hSsh hSown hv
  have hx1 : lookupSEnv S₁ x = none := lookupSEnv_none_of_disjoint_left hDisjS hSown
  have hv' := HasTypeVal_frame_left (G₁:=G₁) (G₂:=G₂) hDisjG hv
  have hRight : lookupSEnv S₁ x = none := hx1
  have hErase : eraseSEnv S₁ x = S₁ := eraseSEnv_of_lookup_none hRight
  have hLeft : lookupSEnv S₂ x = some T' := hSown
  simpa [OwnedEnv.updateLeft, hErase] using
    (HasTypeProcPreOut.assign_old (Ssh:=Ssh) (Sown:={ right := S₁, left := S₂ })
      (G:=G₁ ++ G₂) hSsh hLeft hv')


end
