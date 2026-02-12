import Protocol.Typing.Framing.Lemmas.FrameGCore

/-! # Left Frame Core Lemmas

Core left-framing theorem for `HasTypeProcPre`, showing process typing
lifts through GEnv and SEnv extension on the left. -/

/-
The Problem. To compose typed configurations, we need `HasTypeProcPre P`
for a sub-environment to lift to `HasTypeProcPre P` for the framed
environment `G₁ ++ G₂` with extended SEnv.

Solution Structure. Prove `HasTypeProcPre_frame_left` by induction on
the typing derivation. For each constructor, lift lookups using
disjointness and reassemble the typing judgment.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Main Left Frame Theorem -/

theorem HasTypeProcPre_frame_left
    {Ssh : SEnv} {Sown : OwnedEnv} {Sframe : SEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointS Sframe Sown.right →
    DisjointS Sframe Sown.left →
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left } (G₁ ++ G₂) P := by
  intro hDisjR hDisjL hDisjG hPre
  induction hPre generalizing G₁ Sframe with
  | skip =>
      rename_i Sown G
      simpa using
        (HasTypeProcPre.skip
          (Ssh:=Ssh)
          (Sown:={ right := Sframe ++ Sown.right, left := Sown.left })
          (G:=G₁ ++ G))
  /-! ## Left Frame: send case -/
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      have hx' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) x = some T := by
        simpa [SEnvVisible, List.append_assoc] using hx
      exact HasTypeProcPre.send hk' hG' hx'
  /-! ## Left Frame: recv/select cases -/
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.recv hk' hG' hNoSh
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      exact HasTypeProcPre.select hk' hG' hFind
  /-! ## Left Frame: branch case -/
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      have hk' :
          lookupSEnv (SEnvVisible Ssh { right := Sframe ++ Sown.right, left := Sown.left }) k =
            some (.chan e.sid e.role) := by
        simpa [SEnvVisible, List.append_assoc] using hk
      have hG' := lookupG_frame_left hDisjG hG
      have hDisjSym := DisjointG_symm hDisjG
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) hDisjSym hG
      have hProcs' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh { right := Sframe ++ Sown.right, left := Sown.left }
              (updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        have hDisj' : DisjointG G₁ (updateG G e (bs.get ⟨i, hi⟩).2) :=
          DisjointG_updateG_left (G₁:=G₁) (G₂:=G) (e:=e)
            (L:=.branch p bs) (L':=(bs.get ⟨i, hi⟩).2) hDisjG hG
        have hBody := ih i hi hip hDisjR hDisjL hDisj'
        have hUpd := updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e)
          (L:=(bs.get ⟨i, hi⟩).2) hNone
        have hBody' := hBody
        rw [← hUpd] at hBody'
        exact hBody'
      exact HasTypeProcPre.branch hk' hG' hLen hLbl hProcs'
  /-! ## Left Frame: seq/par cases -/
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisjR hDisjL hDisjG) (ihQ hDisjR hDisjL hDisjG)
  | par hDisjS hS hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ S₂ nS nG
      have hDisjS1 : DisjointS Sframe S₁ := by
        have hDisjL' : DisjointS Sframe (S₁ ++ S₂) := by simpa [hS] using hDisjL
        exact DisjointS_of_append_left hDisjL'
      have hDisjS2 : DisjointS Sframe S₂ := by
        have hDisjL' : DisjointS Sframe (S₁ ++ S₂) := by simpa [hS] using hDisjL
        exact DisjointS_of_append_right hDisjL'
      have hDisjRP : DisjointS Sframe (Sown.right ++ S₂) :=
        DisjointS_append_right hDisjR hDisjS2
      have hDisjRQ : DisjointS Sframe (Sown.right ++ S₁) :=
        DisjointS_append_right hDisjR hDisjS1
      have hP' := ihP hDisjRP hDisjS1 hDisjG
      have hQ' := ihQ hDisjRQ hDisjS2 hDisjG
      exact HasTypeProcPre.par hDisjS (by simpa [hS] using hS)
        (by simpa [List.append_assoc] using hP')
        (by simpa [List.append_assoc] using hQ')
  /-! ## Left Frame: assign case -/
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_left hDisjG hv)

/-! ## Gauge Reframing of Pre-Typing -/

/-- Pre-typing is invariant under right-gauge reframe of the owned environment. -/
theorem HasTypeProcPre_reframe_right
    {Ssh : SEnv} {Sown Sown' : OwnedEnv} {G : GEnv} {P : Process} :
    Sown'.left = Sown.left →
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown' G P := by
  intro hLeft h
  induction h generalizing Sown' with
  | skip =>
      exact HasTypeProcPre.skip
  /-! ## Reframe Right: channel action cases -/
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      have hx' :
          lookupSEnv (SEnvVisible Ssh Sown') x = some T := by
        simpa [SEnvVisible, hLeft] using hx
      exact HasTypeProcPre.send hk' hG hx'
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      exact HasTypeProcPre.recv hk' hG hNoSh
  | select hk hG hFind =>
      rename_i Sown G k l e q bs L
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      exact HasTypeProcPre.select hk' hG hFind
  /-! ## Reframe Right: branch and composition cases -/
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      have hk' :
          lookupSEnv (SEnvVisible Ssh Sown') k = some (.chan e.sid e.role) := by
        simpa [SEnvVisible, hLeft] using hk
      have hProcs' :
          ∀ i (hi : i < bs.length) (hip : i < procs.length),
            HasTypeProcPre Ssh Sown' (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2 := by
        intro i hi hip
        exact ih i hi hip (Sown':=Sown') hLeft
      exact HasTypeProcPre.branch hk' hG hLen hLbl hProcs'
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP (Sown':=Sown') hLeft) (ihQ (Sown':=Sown') hLeft)
  | par hDisjS hS hP hQ ihP ihQ =>
      rename_i Sown G P Q S₁ S₂ nS nG
      have hS' : Sown'.left = S₁ ++ S₂ := by
        simpa [hS] using hLeft
      have hP' :
          HasTypeProcPre Ssh { right := Sown'.right ++ S₂, left := S₁ } G P := by
        exact ihP (Sown':={ right := Sown'.right ++ S₂, left := S₁ }) rfl
      have hQ' :
          HasTypeProcPre Ssh { right := Sown'.right ++ S₁, left := S₂ } G Q := by
        exact ihQ (Sown':={ right := Sown'.right ++ S₁, left := S₂ }) rfl
      exact HasTypeProcPre.par hDisjS hS' hP' hQ'
  /-! ## Reframe Right: assignment case -/
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh hv

/-! ## Session-Subset Transport Under Updates -/

/-- Sessions only shrink under pre-out typing (no new sessions introduced). -/
theorem SessionsOf_subset_update_send
    {G : GEnv} {e : Endpoint} {q : Role} {T : ValType} {L : LocalType} :
    lookupG G e = some (.send q T L) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send q T L) hG
  simpa [hEq] using hs

theorem SessionsOf_subset_update_recv
    {G : GEnv} {e : Endpoint} {p : Role} {T : ValType} {L : LocalType} :
    lookupG G e = some (.recv p T L) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv p T L) hG
  simpa [hEq] using hs

theorem SessionsOf_subset_update_select
    {G : GEnv} {e : Endpoint} {q : Role} {bs : List (Label × LocalType)} {L : LocalType} :
    lookupG G e = some (.select q bs) →
    SessionsOf (updateG G e L) ⊆ SessionsOf G := by
  intro hG s hs
  have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
    SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select q bs) hG
  simpa [hEq] using hs

/-! ## Session-Subset of Pre-Out Derivations -/

theorem SessionsOf_subset_of_HasTypeProcPreOut
    {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SessionsOf G' ⊆ SessionsOf G := by
  intro h
  induction h with
  | skip =>
      intro s hs
      simpa using hs
  | send hk hG hx =>
      exact SessionsOf_subset_update_send hG
  | recv_new hk hG hNoSh hNoOwnL =>
      exact SessionsOf_subset_update_recv hG
  | recv_old hk hG hNoSh hOwn =>
      exact SessionsOf_subset_update_recv hG
  | select hk hG hFind =>
      exact SessionsOf_subset_update_select hG
  | branch _ _ _ _ _ _ hSess _ =>
      exact hSess
  | seq hP hQ ihP ihQ =>
      intro s hs
      exact ihP (ihQ hs)
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      intro s hs
      cases hGfin
      have hs' := SessionsOf_append_subset hs
      cases hs' with
      | inl hsL =>
          simpa [split.hG] using (SessionsOf_append_left (G₂:=split.G2) (ihP hsL))
      | inr hsR =>
          simpa [split.hG] using (SessionsOf_append_right (G₁:=split.G1) (ihQ hsR))
  | assign_new =>
      intro s hs
      simpa using hs
  | assign_old =>
      intro s hs
      simpa using hs

/-! ## Right-Frame Lookup and Value Transport -/

/-- Lift SEnvAll lookups across a right frame (left-biased). -/
theorem lookupSEnv_all_frame_right
    {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv (SEnvAll Ssh S₁) x = some T →
    lookupSEnv (SEnvAll Ssh (S₁ ++ S₂)) x = some T := by
  -- Appending on the right preserves existing left-biased lookups.
  intro hLookup
  have hLeft :=
    lookupSEnv_append_left (S₁:=Ssh ++ S₁) (S₂:=S₂) (x:=x) (T:=T) (by
      simpa [SEnvAll_ofLeft] using hLookup)
  have hEq := lookupSEnv_append_assoc (S₁:=Ssh) (S₂:=S₁) (S₃:=S₂) (x:=x)
  simpa [SEnvAll_ofLeft, SEnvAll, hEq] using hLeft

/-- Right framing preserves HasTypeVal without extra disjointness. -/
theorem HasTypeVal_frame_right {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    HasTypeVal G₁ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  -- The left environment dominates lookups.
  intro hv
  induction hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ ih₁ ih₂ => exact HasTypeVal.prod ih₁ ih₂
  | chan h =>
      exact HasTypeVal.chan (lookupG_append_left h)

/-! ## Auxiliary Disjointness and Update Helpers -/

/-- If the right frame is disjoint from a lookup on the left, the right lookup is none. -/
theorem lookupSEnv_none_of_disjoint_right {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₂ S₁ →
    lookupSEnv S₁ x = some T →
    lookupSEnv S₂ x = none := by
  -- Disjointness forbids any binding for x on the right.
  intro hDisj hLeft
  by_cases hNone : lookupSEnv S₂ x = none
  · exact hNone
  · cases hRight : lookupSEnv S₂ x with
    | none => exact (hNone hRight).elim
    | some T₂ => exact (hDisj x T₂ T hRight hLeft).elim

/-- Empty SEnv is disjoint from any environment. -/
theorem DisjointS_left_empty (S : SEnv) : DisjointS (∅ : SEnv) S := by
  -- Empty lookup is never `some`, so disjointness is trivial.
  intro x T₁ T₂ hLeft hRight
  cases hLeft

/-- Appending the empty SEnv on the right is a no-op. -/
theorem SEnv_append_empty_right (S : SEnv) : S ++ (∅ : SEnv) = S := by
  simpa using (List.append_nil S)

/-- When x is in S₁, update distributes over append.
    NOTE: This was previously an unsound assumption. The theorem requires x ∈ S₁.
    Uses Core.updateSEnv_append_left_of_mem. -/
theorem updateSEnv_append_left' {S₁ S₂ : SEnv} {x : Var} {T : ValType}
    (h : ∃ T', lookupSEnv S₁ x = some T') :
    updateSEnv (S₁ ++ S₂) x T = updateSEnv S₁ x T ++ S₂ :=
  updateSEnv_append_left_of_mem h

/-- Shorthand for left-framing on pre-out typing. -/
abbrev FrameLeft (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the left framing goal as a reusable predicate.
  ∀ {S₂' G₂' W Δ}, DisjointS S₁ S₂ → DisjointS S₁ S₂' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₂ G₂ P S₂' G₂' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁ ++ S₂') (G₁ ++ G₂') W Δ

/-- Shorthand for right-framing on pre-out typing. -/
abbrev FrameRight (Ssh S₁ S₂ : SEnv) (G₁ G₂ : GEnv) (P : Process) : Prop :=
  -- Expand the right framing goal as a reusable predicate.
  ∀ {S₁' G₁' W Δ}, DisjointS S₂ S₁ → DisjointS S₂ S₁' → DisjointG G₁ G₂ →
    HasTypeProcPreOut Ssh S₁ G₁ P S₁' G₁' W Δ →
    HasTypeProcPreOut Ssh (S₁ ++ S₂) (G₁ ++ G₂) P (S₁' ++ S₂) (G₁' ++ G₂) W Δ

end
