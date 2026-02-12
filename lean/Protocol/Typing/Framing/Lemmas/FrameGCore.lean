import Protocol.Typing.Framing.Lemmas.LookupAndDisjointBasics

/-! # GEnv Framing Core Lemmas

Core framing lemmas for value and process typing under GEnv extension,
showing typing judgments lift through disjoint environment composition. -/

/-
The Problem. When framing a typed configuration with additional GEnv
entries, we need to show value typing (`HasTypeVal`) and process typing
(`HasTypeProcPre`) are preserved. The key challenge is lifting lookups
through the appended environment.

Solution Structure. Prove `HasTypeVal_frame_left` by induction on value
typing. For channel values, use `DisjointG_lookup_left` to show the
original lookup is preserved. Extend to `HasTypeProcPre` for each
process constructor.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Value Typing Under Framing -/

theorem HasTypeVal_frame_left {G₁ G₂ : GEnv} {v : Value} {T : ValType} :
    DisjointG G₁ G₂ →
    HasTypeVal G₂ v T →
    HasTypeVal (G₁ ++ G₂) v T := by
  intro hDisj hv
  cases hv with
  | unit => exact HasTypeVal.unit
  | bool b => exact HasTypeVal.bool b
  | nat n => exact HasTypeVal.nat n
  | string s => exact HasTypeVal.string s
  | prod h₁ h₂ =>
      exact HasTypeVal.prod (HasTypeVal_frame_left hDisj h₁) (HasTypeVal_frame_left hDisj h₂)
  | chan h =>
      rename_i e L
      have hDisjSym := DisjointG_symm hDisj
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym h
      have hLookup : lookupG (G₁ ++ G₂) e = some L := by
        simpa [lookupG_append_right hNone] using h
      exact HasTypeVal.chan hLookup

/-- Pre-update typing is stable under framing on the left of G (no S changes). -/
theorem HasTypeProcPre_frame_G_branch
    {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G : GEnv} {k : Var} {procs : List (Label × Process)}
    {e : Endpoint} {p : Role} {bs : List (Label × LocalType)} :
    DisjointG G₁ G →
    lookupSEnv (SEnvVisible Ssh Sown) k = some (.chan e.sid e.role) →
    lookupG G e = some (.branch p bs) →
    bs.length = procs.length →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        (procs.get ⟨i, hip⟩).1 = (bs.get ⟨i, hi⟩).1) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown (updateG G e (bs.get ⟨i, hi⟩).2) (procs.get ⟨i, hip⟩).2) →
    (∀ i (hi : i < bs.length) (hip : i < procs.length) {G₁' : GEnv},
        DisjointG G₁' (updateG G e (bs.get ⟨i, hi⟩).2) →
          HasTypeProcPre Ssh Sown
            (G₁' ++ updateG G e (bs.get ⟨i, hi⟩).2)
            (procs.get ⟨i, hip⟩).2) →
    HasTypeProcPre Ssh Sown (G₁ ++ G) (.branch k procs) := by
  intro hDisj hk hG hLen hLbl hProcs ih
  have hSid : e.sid ∈ SessionsOf G := ⟨e, .branch p bs, hG, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₁ := by
    intro hIn
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G := ⟨hIn, hSid⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G = (∅ : Set SessionId) := by
      simpa [DisjointG, GEnvDisjoint] using hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact this.elim
  have hNone : lookupG G₁ e = none := lookupG_none_of_not_session (G:=G₁) hNot
  have hG' : lookupG (G₁ ++ G) e = some (.branch p bs) := by
    simpa [lookupG_append_right hNone] using hG
  have hProcs' :
      ∀ i (hi : i < bs.length) (hip : i < procs.length),
        HasTypeProcPre Ssh Sown
          (updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2)
          (procs.get ⟨i, hip⟩).2 := by
    intro i hi hip
    have hSub : SessionsOf (updateG G e (bs.get ⟨i, hi⟩).2) ⊆ SessionsOf G := by
      intro s hs
      rcases hs with ⟨e', L', hLookup, hSid'⟩
      by_cases hEq : e' = e
      · subst hEq
        simpa [hSid'] using hSid
      · have hLookup' : lookupG G e' = some L' := by
          have h :=
            lookupG_update_neq (env:=G) (e:=e) (e':=e') (L:= (bs.get ⟨i, hi⟩).2) (Ne.symm hEq)
          rw [h] at hLookup
          exact hLookup
        exact ⟨e', L', hLookup', hSid'⟩
    have hDisj' : DisjointG G₁ (updateG G e (bs.get ⟨i, hi⟩).2) := by
      have hDisjSym := DisjointG_symm hDisj
      have hDisj'' :=
        DisjointG_of_subset_left (G₁:=G) (G₁':=updateG G e (bs.get ⟨i, hi⟩).2)
          (G₂:=G₁) hSub hDisjSym
      exact DisjointG_symm hDisj''
    have hPre' := ih i hi hip (G₁':=G₁) hDisj'
    have hUpd :
        updateG (G₁ ++ G) e (bs.get ⟨i, hi⟩).2 =
          G₁ ++ updateG G e (bs.get ⟨i, hi⟩).2 :=
      updateG_append_left (G₁:=G₁) (G₂:=G) (e:=e) (L:= (bs.get ⟨i, hi⟩).2) hNone
    rw [hUpd.symm] at hPre'
    exact hPre'
  exact HasTypeProcPre.branch hk hG' hLen hLbl hProcs'

theorem HasTypeProcPre_frame_G {Ssh : SEnv} {Sown : OwnedEnv} {G₁ G₂ : GEnv} {P : Process} :
    DisjointG G₁ G₂ →
    HasTypeProcPre Ssh Sown G₂ P →
    HasTypeProcPre Ssh Sown (G₁ ++ G₂) P := by
  intro hDisj hPre
  induction hPre generalizing G₁ with
  | skip =>
      rename_i Sown G
      simpa using (HasTypeProcPre.skip (Ssh:=Ssh) (Sown:=Sown) (G:=G₁ ++ G))
  | send hk hG hx =>
      rename_i Sown G k x e q T L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.send q T L) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.send hk hG' hx
  | recv hk hG hNoSh =>
      rename_i Sown G k x e p T L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.recv p T L) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.recv hk hG' hNoSh
  | select hk hG hbs =>
      rename_i Sown G k l e q bs L
      have hNone : lookupG G₁ e = none :=
        DisjointG_lookup_left (G₁:=G) (G₂:=G₁) (DisjointG_symm hDisj) hG
      have hG' : lookupG (G₁ ++ G) e = some (.select q bs) := by
        simpa [lookupG_append_right hNone] using hG
      exact HasTypeProcPre.select hk hG' hbs
  | branch hk hG hLen hLbl hProcs ih =>
      rename_i Sown G k procs e p bs
      exact HasTypeProcPre_frame_G_branch (G₁:=G₁) (G:=G) (k:=k) (procs:=procs)
        (e:=e) (p:=p) (bs:=bs)
        hDisj hk hG hLen hLbl hProcs
        (by
          intro i hi hip G₁' hDisj'
          exact ih i hi hip hDisj')
  | seq hP hQ ihP ihQ =>
      exact HasTypeProcPre.seq (ihP hDisj) (ihQ hDisj)
  | par hDisjS hSplit hP hQ ihP ihQ =>
      exact HasTypeProcPre.par hDisjS hSplit (ihP hDisj) (ihQ hDisj)
  | assign hNoSh hv =>
      exact HasTypeProcPre.assign hNoSh (HasTypeVal_frame_left hDisj hv)

/-- Frame a disjoint GEnv on the left of pre-typing. -/
lemma HasTypeProcPre_frame_G_left {Ssh : SEnv} {Sown : OwnedEnv} {Gfr G : GEnv} {P : Process} :
    DisjointG Gfr G →
    HasTypeProcPre Ssh Sown G P →
    HasTypeProcPre Ssh Sown (Gfr ++ G) P :=
  HasTypeProcPre_frame_G

/-- Any SEnv is domain-included in its right-framed extension. -/
theorem SEnvDomSubset_into_right_frame {Sbase Sframe : SEnv} :
    SEnvDomSubset Sbase (Sbase ++ Sframe) := by
  intro x T hLookup
  exact ⟨T, lookupSEnv_append_left (S₁:=Sbase) (S₂:=Sframe) (x:=x) (T:=T) hLookup⟩

/-- Dom-subset transports lookup absence from a right frame back to the source. -/
theorem lookupSEnv_none_of_domsubset_right
    {Sframe Sright : SEnv} {x : Var} :
    SEnvDomSubset Sframe Sright →
    lookupSEnv Sright x = none →
    lookupSEnv Sframe x = none := by
  intro hSub hNo
  by_cases hNone : lookupSEnv Sframe x = none
  · exact hNone
  · cases hL : lookupSEnv Sframe x with
    | none => exact (hNone hL).elim
    | some T =>
        obtain ⟨T', hRight⟩ := hSub hL
        simpa [hNo] using hRight

/-- Disjointness with an appended SEnv implies disjointness with the left side. -/
theorem DisjointS_of_append_left {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₂ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₂ (S₂ ++ S₃) := SEnvDomSubset_append_left (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- Disjointness with an appended SEnv implies disjointness with the right side. -/
theorem DisjointS_of_append_right {S₁ S₂ S₃ : SEnv} :
    DisjointS S₁ (S₂ ++ S₃) → DisjointS S₁ S₃ := by
  -- Shrink the right side using domain subset.
  intro hDisj
  have hDom : SEnvDomSubset S₃ (S₂ ++ S₃) := SEnvDomSubset_append_right (S₁:=S₂) (S₂:=S₃)
  exact DisjointS_of_domsubset_right hDom hDisj

/-- Disjointness distributes over right appends. -/
theorem DisjointS_append_right
    {Ssh S₁ S₂ : SEnv} :
    DisjointS Ssh S₁ →
    DisjointS Ssh S₂ →
    DisjointS Ssh (S₁ ++ S₂) := by
  -- Route the append lookup to the appropriate side.
  intro hDisj1 hDisj2 x T₁ T₂ hLsh hL12
  cases hL1 : lookupSEnv S₁ x with
  | some T₁' =>
      have hEq : T₁' = T₂ := by
        have hLeft := lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) (x:=x) (T:=T₁') hL1
        exact Option.some.inj (by simpa [hLeft] using hL12)
      exact hDisj1 x T₁ T₁' hLsh (by simpa [hEq] using hL1)
  | none =>
      have hRight := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hL1
      have hL2 : lookupSEnv S₂ x = some T₂ := by
        simpa [hRight] using hL12
      exact hDisj2 x T₁ T₂ hLsh hL2

/-- DisjointG distributes over right appends. -/
theorem DisjointG_append_right {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁ G₃ →
    DisjointG G₁ (G₂ ++ G₃) := by
  intro hDisj12 hDisj13
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rcases hs with ⟨h1, h23⟩
  have h23' : s ∈ SessionsOf G₂ ∪ SessionsOf G₃ :=
    SessionsOf_append_subset (G₁:=G₂) (G₂:=G₃) h23
  cases h23' with
  | inl h2 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj12
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨h1, h2⟩
      have : s ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim
  | inr h3 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₃ = (∅ : Set SessionId) := hDisj13
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₃ := ⟨h1, h3⟩
      have : s ∈ (∅ : Set SessionId) := by
        simpa [hEmpty] using hInter
      exact this.elim

lemma SessionsOf_empty : SessionsOf ([] : GEnv) = (∅ : Set SessionId) := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rcases hs with ⟨e, L, hLookup, _⟩
  have : False := by
    simpa [lookupG] using hLookup
  exact this.elim

lemma DisjointG_right_empty (G : GEnv) : DisjointG G ([] : GEnv) := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

/-- DisjointG with an appended GEnv implies disjointness with the left side. -/
theorem DisjointG_of_append_left {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₂ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₂ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_left (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- DisjointG with an appended GEnv implies disjointness with the right side. -/
theorem DisjointG_of_append_right {G₁ G₂ G₃ : GEnv} :
    DisjointG G₁ (G₂ ++ G₃) → DisjointG G₁ G₃ := by
  -- Shrink the right side using session subset.
  intro hDisj
  have hDisjSym := DisjointG_symm hDisj
  have hSub : SessionsOf G₃ ⊆ SessionsOf (G₂ ++ G₃) := SessionsOf_append_right (G₁:=G₂) (G₂:=G₃)
  have hDisj' := DisjointG_of_subset_left hSub hDisjSym
  exact DisjointG_symm hDisj'

/-- Lift a GEnv lookup across a left frame using disjointness. -/
theorem lookupG_frame_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro hDisj hLookup
  have hDisjSym := DisjointG_symm hDisj
  have hNone : lookupG G₁ e = none :=
    DisjointG_lookup_left (G₁:=G₂) (G₂:=G₁) hDisjSym hLookup
  simpa [lookupG_append_right hNone] using hLookup

/-- GEnv disjointness is preserved when updating an existing endpoint on the right. -/
theorem DisjointG_updateG_left
    {G₁ G₂ : GEnv} {e : Endpoint} {L L' : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₂ e = some L →
    DisjointG G₁ (updateG G₂ e L') := by
  -- Updating an existing endpoint does not add new session ids.
  intro hDisj hLookup
  have hSub : SessionsOf (updateG G₂ e L') ⊆ SessionsOf G₂ := by
    intro s hs
    rcases hs with ⟨e', L'', hLookup', hSid⟩
    by_cases hEq : e' = e
    · have hLookup'' : lookupG G₂ e' = some L := by
        simpa [hEq] using hLookup
      exact ⟨e', L, hLookup'', hSid⟩
    · have hLookup'' : lookupG G₂ e' = some L'' := by
        have h := lookupG_update_neq (env:=G₂) (e:=e) (e':=e') (L:=L') (Ne.symm hEq)
        simpa [h] using hLookup'
      exact ⟨e', L'', hLookup'', hSid⟩
  have hDisjSym := DisjointG_symm hDisj
  have hDisj' :=
    DisjointG_of_subset_left (G₁:=G₂) (G₁':=updateG G₂ e L') (G₂:=G₁) hSub hDisjSym
  exact DisjointG_symm hDisj'

lemma lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {e : Endpoint} {L : LocalType} (hLookup : lookupG G₂ e = some L) :
    lookupG G₁ e = none := by
  by_cases hNone : lookupG G₁ e = none
  · exact hNone
  · cases hSome : lookupG G₁ e with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hSid₁ : e.sid ∈ SessionsOf G₁ := ⟨e, L₁, hSome, rfl⟩
        have hSid₂ : e.sid ∈ SessionsOf G₂ := ⟨e, L, hLookup, rfl⟩
        have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid₁, hSid₂⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
        have : e.sid ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact this.elim

-- NOTE: We intentionally avoid general G-framing lemmas here to keep full-G
-- reasoning explicit under the par-step rule.

end
