import Protocol.Typing.Compatibility.DEnvLemmas

/-! # Protocol.Typing.Compatibility.SplitLemmas

Split/append compatibility lemmas used by preservation.
-/

/-
The Problem. Compatibility closure under framing/splitting needs a final group
of append/swap/split lemmas.

Solution Structure. Collects remaining split/append compatibility results.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical
open Batteries

section

-- Session and Disjointness Lemmas

/-- Right sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_right {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  exact SessionsOf_append_right_subset (G₁:=G₁) (G₂:=G₂) hs

/-- Disjointness is preserved when the left sessions shrink. -/
theorem DisjointG_of_subset_left {G₁ G₁' G₂ : GEnv} :
    SessionsOf G₁' ⊆ SessionsOf G₁ →
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ := by
  intro hSub hDisj
  have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := by
    simpa [DisjointG, GEnvDisjoint] using hDisj
  apply Set.eq_empty_iff_forall_notMem.2
  intro s hs
  have hs' : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
    exact ⟨hSub hs.1, hs.2⟩
  have : s ∈ (∅ : Set SessionId) := by
    simpa [hEmpty] using hs'
  exact this.elim

/-- DisjointG is symmetric. -/
theorem DisjointG_symm {G₁ G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₂ G₁ := by
  intro hDisj
  simpa [DisjointG, GEnvDisjoint, Set.inter_comm] using hDisj

theorem DisjointG_append_left {G₁ G₁' G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ →
    DisjointG (G₁ ++ G₁') G₂ := by
  intro hDisj hDisj'
  apply Set.eq_empty_iff_forall_notMem.2
  intro s hs
  have hSub := SessionsOf_append_subset (G₁:=G₁) (G₂:=G₁') hs.1
  cases hSub with
  | inl hIn1 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := by
        simpa [DisjointG, GEnvDisjoint] using hDisj
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn1, hs.2⟩
      have : s ∈ (∅ : Set SessionId) := by simpa [hEmpty] using hInter
      exact this.elim
  | inr hIn2 =>
      have hEmpty : SessionsOf G₁' ∩ SessionsOf G₂ = ∅ := by
        simpa [DisjointG, GEnvDisjoint] using hDisj'
      have hInter : s ∈ SessionsOf G₁' ∩ SessionsOf G₂ := ⟨hIn2, hs.2⟩
      have : s ∈ (∅ : Set SessionId) := by simpa [hEmpty] using hInter
      exact this.elim

-- DEnv Append Lookup Facts

theorem lookupD_append_left {D₁ D₂ : DEnv} {e : Edge} :
    lookupD D₁ e ≠ [] →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e := by
  intro hne
  cases hfind : D₁.find? e with
  | none =>
      have hlookup : lookupD D₁ e = [] := by
        simp [lookupD, hfind]
      exact (hne hlookup).elim
  | some ts =>
      have hleft :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hfind
      have hlookup : lookupD D₁ e = ts := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = ts := by
        simp [lookupD, hleft]
      simpa [hlookup] using hlookup'

theorem lookupD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₂ e := by
  intro hfind
  have h := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hfind
  simp [lookupD, h]

theorem lookupD_append_left_of_right_none {D₁ D₂ : DEnv} {e : Edge} :
    D₂.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e := by
  intro hRight
  cases hfind : D₁.find? e with
  | none =>
      have h := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hfind
      have hlookup : lookupD D₁ e = [] := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = [] := by
        simp [lookupD, h, hRight]
      simpa [hlookup] using hlookup'
  | some ts =>
      have hleft :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hfind
      have hlookup : lookupD D₁ e = ts := by
        simp [lookupD, hfind]
      have hlookup' : lookupD (D₁ ++ D₂) e = ts := by
        simp [lookupD, hleft]
      simpa [hlookup] using hlookup'

-- SEnv Domain Inclusion Under Append

theorem SEnvDomSubset_append_left {S₁ S₂ : SEnv} :
    SEnvDomSubset S₁ (S₁ ++ S₂) := by
  intro x T hLookup
  exact ⟨T, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hLookup⟩

theorem SEnvDomSubset_append_right {S₁ S₂ : SEnv} :
    SEnvDomSubset S₂ (S₁ ++ S₂) := by
  intro x T hLookup
  cases hLeft : lookupSEnv S₁ x with
  | some T₁ =>
      exact ⟨T₁, lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hLeft⟩
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hLeft
      exact ⟨T, by simpa [hEq] using hLookup⟩

-- Framed SEnv Lookup Transport

theorem lookupSEnv_all_frame_left {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (Ssh ++ S₂) x = some T →
    lookupSEnv (Ssh ++ (S₁ ++ S₂)) x = some T := by
  intro hDisj hLookup
  cases hSsh : lookupSEnv Ssh x with
  | some Tsh =>
      have hLeft := lookupSEnv_append_left (S₁:=Ssh) (S₂:=S₂) hSsh
      have hEq : Tsh = T := by
        have : some Tsh = some T := by simpa [hLeft] using hLookup
        cases this
        rfl
      have hLeft' := lookupSEnv_append_left (S₁:=Ssh) (S₂:=S₁ ++ S₂) hSsh
      simpa [hEq] using hLeft'
  | none =>
      have hEq := lookupSEnv_append_right (S₁:=Ssh) (S₂:=S₂) (x:=x) hSsh
      have hS2 : lookupSEnv S₂ x = some T := by
        simpa [hEq] using hLookup
      have hS1 : lookupSEnv S₁ x = none := by
        by_cases hS1 : lookupSEnv S₁ x = none
        · exact hS1
        · cases hS1' : lookupSEnv S₁ x with
          | none => exact (hS1 hS1').elim
          | some T₁ =>
              have hContra := hDisj x T₁ T hS1' hS2
              exact hContra.elim
      have hEq' := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hS1
      have hIn : lookupSEnv (S₁ ++ S₂) x = some T := by
        simpa [hEq'] using hS2
      have hEq'' := lookupSEnv_append_right (S₁:=Ssh) (S₂:=S₁ ++ S₂) (x:=x) hSsh
      simpa [hEq''] using hIn

-- HasTypeProcPreOut Domain Monotonicity

theorem HasTypeProcPreOut_domsubset {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SEnvDomSubset Sown.left Sown'.left := by
  intro h
  induction h with
  | skip =>
      exact SEnvDomSubset_refl
  | send =>
      exact SEnvDomSubset_refl
  | recv_new =>
      exact SEnvDomSubset_update_left
  | recv_old =>
      exact SEnvDomSubset_update_left
  | select =>
      exact SEnvDomSubset_refl
  | branch _ _ _ _ _ _ _ hDom _ =>
      exact hDom
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihP ihQ
  -- HasTypeProcPreOut Domain Monotonicity: parallel case
  | par split hSlen hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS'
      hDisjW hDisjΔ hP hQ ihP ihQ =>
      -- Show dom subset for the left portion of the owned env.
      rename_i S₁' S₂' G₁' G₂' W₁ W₂ Δ₁ Δ₂ nS nG
      intro x T hLookup
      have hLookupS : lookupSEnv (split.S1 ++ split.S2) x = some T := by
        simpa [split.hS] using hLookup
      by_cases hLeftNone : lookupSEnv split.S1 x = none
      · have hRight : lookupSEnv split.S2 x = some T := by
          have hEq := lookupSEnv_append_right (S₁:=split.S1) (S₂:=split.S2) (x:=x) hLeftNone
          simpa [hEq] using hLookupS
        obtain ⟨T', hRight'⟩ := ihQ hRight
        have hLeftNone' : lookupSEnv S₁' x = none := by
          by_cases hSome : lookupSEnv S₁' x = none
          · exact hSome
          · cases hSome' : lookupSEnv S₁' x with
            | none => exact (hSome hSome').elim
            | some T₁ =>
                exact (hDisjS' x T₁ T' hSome' hRight').elim
        have hEq := lookupSEnv_append_right (S₁:=S₁') (S₂:=S₂') (x:=x) hLeftNone'
        have hAppend : lookupSEnv (S₁' ++ S₂') x = some T' := by
          simpa [hEq] using hRight'
        exact ⟨T', by simpa [hSfin] using hAppend⟩
      · cases hLeftSome : lookupSEnv split.S1 x with
        | none => exact (hLeftNone hLeftSome).elim
        | some T₁ =>
            have hLeftAppend :
                lookupSEnv (split.S1 ++ split.S2) x = some T₁ :=
              lookupSEnv_append_left (S₁:=split.S1) (S₂:=split.S2) hLeftSome
            have hEqT : T₁ = T := by
              have : some T₁ = some T := by
                simpa [hLeftAppend] using hLookupS
              exact Option.some.inj this
            have hLeftSome' : lookupSEnv split.S1 x = some T := by
              simpa [hEqT] using hLeftSome
            obtain ⟨T', hLeft'⟩ := ihP hLeftSome'
            have hAppend := lookupSEnv_append_left (S₁:=S₁') (S₂:=S₂') hLeft'
            exact ⟨T', by simpa [hSfin] using hAppend⟩
  -- HasTypeProcPreOut Domain Monotonicity: assignment cases
  | assign_new =>
      exact SEnvDomSubset_update_left
  | assign_old =>
      exact SEnvDomSubset_update_left

-- StoreTyped Split Transport

/-- StoreTyped splits to the left portion of SEnv. -/
theorem StoreTyped_split_left {G : GEnv} {S₁ S₂ : SEnv} {store : VarStore} :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₁ store := by
  intro hST x v T hStore hS
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T :=
    lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hS
  exact hST x v T hStore hS'

/-- StoreTyped splits to the right portion of SEnv (requires disjointness). -/
theorem StoreTyped_split_right {G : GEnv} {S₁ S₂ : SEnv} {store : VarStore}
    (hDisj : DisjointS S₁ S₂) :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₂ store := by
  intro hST x v T hStore hS
  have hNone : lookupSEnv S₁ x = none := by
    by_cases hS1 : lookupSEnv S₁ x = none
    · exact hS1
    · cases hS1' : lookupSEnv S₁ x with
      | none => exact (hS1 hS1').elim
      | some T₁ =>
          exact (hDisj x T₁ T hS1' hS).elim
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T := by
    have h := lookupSEnv_append_right (S₁:=S₁) (S₂:=S₂) (x:=x) hNone
    simpa [hS] using h
  exact hST x v T hStore hS'

-- Coherence Split Transport

/-- Coherence splits to the left portion of G/D. -/
theorem Coherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    Coherent G₁ D₁ := by
  intro hCoh hDisj e hActive Lrecv hGrecv
  let senderEp : Endpoint := { sid := e.sid, role := e.sender }
  let recvEp : Endpoint := { sid := e.sid, role := e.receiver }
  have hGrecv' : lookupG (G₁ ++ G₂) recvEp = some Lrecv := lookupG_append_left hGrecv
  have hActive' : ActiveEdge (G₁ ++ G₂) e := by
    simp only [ActiveEdge]
    constructor
    · -- Sender isSome in G₁ ++ G₂
      have hS := hActive.1
      simp only [Option.isSome_iff_exists] at hS ⊢
      obtain ⟨Ls, hLs⟩ := hS
      exact ⟨Ls, lookupG_append_left hLs⟩
    · -- Receiver isSome in G₁ ++ G₂
      rw [hGrecv']; trivial
  have hCoh' := hCoh e hActive' Lrecv hGrecv'
  rcases hCoh' with ⟨Lsender, hGsenderMerged, hConsume⟩
  -- sender must live in G₁ because sessions are disjoint and receiver is in G₁
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨recvEp, Lrecv, hGrecv, rfl⟩
  have hNot : e.sid ∉ SessionsOf G₂ := by
    intro hIn2
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid, hIn2⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have : e.sid ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact this.elim
  have hG2none_sender : lookupG G₂ senderEp = none := lookupG_none_of_not_session hNot
  have hGsender : lookupG G₁ senderEp = some Lsender := by
    cases lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:=senderEp) hGsenderMerged with
    | inl hLeft => exact hLeft
    | inr hRight =>
        have hRight' : lookupG G₂ senderEp = some Lsender := hRight.2
        have : False := by simpa [hG2none_sender] using hRight'
        exact this.elim
  by_cases hTrace : lookupD D₁ e = []
  · refine ⟨Lsender, hGsender, ?_⟩
    simp [hTrace, Consume]
  · have hTrace' : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
      lookupD_append_left (e := e) hTrace
    refine ⟨Lsender, hGsender, ?_⟩
    simpa [hTrace'] using hConsume

end
