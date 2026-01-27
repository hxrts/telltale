import Effects.Typing.Part2

/-!
# MPST Process Typing

This module defines the typing rules for MPST processes.

## Key Judgments

- `HasTypeProcN n S G D P`: Process P is well-typed under environments S, G, D
  with maximum session ID n
- `WTConfigN n S G D C`: Configuration C is well-typed

## Typing Rules

- **Skip**: `⊢ skip` (always well-typed)
- **Seq**: `⊢ P` and `⊢ Q` implies `⊢ seq P Q`
- **Par**: `⊢ P` and `⊢ Q` with split contexts implies `⊢ par P Q`
- **Send**: If `S[k] = chan (sid, r)` and `G[sid,r] = !q(T).L` and `S[x] = T`,
            then `⊢ send k x` and G[sid,r] ↦ L
- **Recv**: If `S[k] = chan (sid, r)` and `G[sid,r] = ?p(T).L`,
            then `⊢ recv k x` and G[sid,r] ↦ L, S[x] ↦ T
- **Select**: If `S[k] = chan (sid, r)` and `G[sid,r] = ⊕q{ℓᵢ: Lᵢ}`,
              then `⊢ select k ℓⱼ` and G[sid,r] ↦ Lⱼ
- **Branch**: If `S[k] = chan (sid, r)` and `G[sid,r] = &p{ℓᵢ: Lᵢ}`,
              then `⊢ branch k [(ℓᵢ, Pᵢ)]` if each Pᵢ is typed under Lᵢ
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

noncomputable section

/-! ### WellFormed Predicate -/

/-- Well-formed process configuration.

    **Combines all invariants**: A process P with state (G, D, S, store, bufs)
    is well-formed if:
    1. Store is typed by S and G
    2. Buffers are typed by D
    3. G and D are coherent
    4. Process P has pre-update style typing

    This predicate is preserved by TypedStep transitions. -/
def WellFormed (G : GEnv) (D : DEnv) (Ssh Sown : SEnv)
    (store : Store) (bufs : Buffers) (P : Process) : Prop :=
  StoreTypedStrong G (SEnvAll Ssh Sown) store ∧
  BuffersTyped G D bufs ∧
  Coherent G D ∧
  HeadCoherent G D ∧
  ValidLabels G D bufs ∧
  SendReady G D ∧
  SelectReady G D ∧
  DisjointS Ssh Sown ∧
  DConsistent G D ∧
  ∃ S' G' W Δ, HasTypeProcPreOut Ssh Sown G P S' G' W Δ

/-- Complete well-formedness: core invariants plus role-completeness of GEnv. -/
def WellFormedComplete (G : GEnv) (D : DEnv) (Ssh Sown : SEnv)
    (store : Store) (bufs : Buffers) (P : Process) : Prop :=
  WellFormed G D Ssh Sown store bufs P ∧ RoleComplete G

/-- WellFormedComplete implies WellFormed (projection). -/
theorem WellFormedComplete.toWellFormed
    {G : GEnv} {D : DEnv} {Ssh Sown : SEnv}
    {store : Store} {bufs : Buffers} {P : Process} :
    WellFormedComplete G D Ssh Sown store bufs P →
    WellFormed G D Ssh Sown store bufs P := by
  -- Drop the RoleComplete component.
  intro h
  exact h.1

/-! ## Support Lemmas for Preservation -/

/-- DisjointG: left lookup implies right is none. -/
theorem DisjointG_lookup_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    DisjointG G₁ G₂ →
    lookupG G₁ e = some L →
    lookupG G₂ e = none := by
  intro hDisj hLookup
  have hSid : e.sid ∈ SessionsOf G₁ := ⟨e, L, hLookup, rfl⟩
  have hNoSid : e.sid ∉ SessionsOf G₂ := by
    intro hSid2
    have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
      exact ⟨hSid, hSid2⟩
    have hEmpty := hDisj
    have : (SessionsOf G₁ ∩ SessionsOf G₂) = ∅ := hEmpty
    have hContra : e.sid ∈ (∅ : Set SessionId) := by
      simpa [this] using hInter
    exact hContra.elim
  by_contra hSome
  cases hLookup2 : lookupG G₂ e with
  | none => exact (hSome hLookup2)
  | some L2 =>
      have hSid2 : e.sid ∈ SessionsOf G₂ := ⟨e, L2, hLookup2, rfl⟩
      exact (hNoSid hSid2)

/-- If a session ID is not present in G, lookup at any endpoint with that ID is none. -/
theorem lookupG_none_of_not_session {G : GEnv} {e : Endpoint} :
    e.sid ∉ SessionsOf G →
    lookupG G e = none := by
  intro hNot
  cases hLookup : lookupG G e with
  | none => simp
  | some L =>
      have hSid : e.sid ∈ SessionsOf G := ⟨e, L, hLookup, rfl⟩
      exact (hNot hSid).elim

axiom DisjointD_lookup_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₁.find? e = some ts →
    D₂.find? e = none

axiom DisjointD_lookup_right {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    DisjointD D₁ D₂ →
    D₂.find? e = some ts →
    D₁.find? e = none

axiom SessionsOfD_append_subset {D₁ D₂ : DEnv} :
    SessionsOfD (D₁ ++ D₂) ⊆ SessionsOfD D₁ ∪ SessionsOfD D₂

axiom SessionsOfD_append_left {D₁ D₂ : DEnv} :
    SessionsOfD D₁ ⊆ SessionsOfD (D₁ ++ D₂)

axiom SessionsOfD_append_right {D₁ D₂ : DEnv} :
    SessionsOfD D₂ ⊆ SessionsOfD (D₁ ++ D₂)

axiom SessionsOfD_updateD_subset {D : DEnv} {e : Edge} {ts : List ValType} :
    SessionsOfD (updateD D e ts) ⊆ SessionsOfD D ∪ {e.sid}

axiom lookupD_entry_of_nonempty {D : DEnv} {e : Edge} :
    lookupD D e ≠ [] →
    ∃ ts, D.find? e = some ts

/-- Lookup in appended GEnv prefers the left. -/
theorem lookupG_append_left {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG G₁ e = some L →
    lookupG (G₁ ++ G₂) e = some L := by
  intro h
  have hLookup : G₁.lookup e = some L := by
    simpa [lookupG] using h
  calc
    lookupG (G₁ ++ G₂) e = (G₁.lookup e).or (G₂.lookup e) := by
      simp [lookupG, List.lookup_append]
    _ = some L := by
      simp [hLookup]

/-- Lookup in appended GEnv falls back to the right when left is missing. -/
theorem lookupG_append_right {G₁ G₂ : GEnv} {e : Endpoint} :
    lookupG G₁ e = none →
    lookupG (G₁ ++ G₂) e = lookupG G₂ e := by
  intro h
  have hLookup : G₁.lookup e = none := by
    simpa [lookupG] using h
  calc
    lookupG (G₁ ++ G₂) e = (G₁.lookup e).or (G₂.lookup e) := by
      simp [lookupG, List.lookup_append]
    _ = lookupG G₂ e := by
      simp [hLookup, lookupG]

/-- Invert lookup in an appended GEnv. -/
theorem lookupG_append_inv {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType} :
    lookupG (G₁ ++ G₂) e = some L →
    lookupG G₁ e = some L ∨ (lookupG G₁ e = none ∧ lookupG G₂ e = some L) := by
  intro h
  have hLookup : (G₁.lookup e).or (G₂.lookup e) = some L := by
    simpa [lookupG, List.lookup_append] using h
  cases hLeft : G₁.lookup e with
  | none =>
      right
      have hRight : G₂.lookup e = some L := by
        simpa [hLeft] using hLookup
      exact ⟨by simpa [lookupG] using hLeft, by simpa [lookupG] using hRight⟩
  | some L1 =>
      have hEq : L1 = L := by
        simpa [hLeft] using hLookup
      left
      simpa [lookupG, hEq] using hLeft

theorem SessionsOf_append_right_subset {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hMem
  rcases hMem with ⟨e, L, hLookup, hSid⟩
  by_cases hNone : lookupG G₁ e = none
  · have hEq := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hNone
    exact ⟨e, L, by simpa [hEq] using hLookup, hSid⟩
  · cases hSome : lookupG G₁ e with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hLeft : lookupG (G₁ ++ G₂) e = some L₁ :=
          lookupG_append_left (G₁:=G₁) (G₂:=G₂) hSome
        exact ⟨e, L₁, hLeft, hSid⟩

/-- Sessions in an appended GEnv are contained in the union of sessions. -/
theorem SessionsOf_append_subset {G₁ G₂ : GEnv} :
    SessionsOf (G₁ ++ G₂) ⊆ SessionsOf G₁ ∪ SessionsOf G₂ := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  have hLookup' : (G₁.lookup e).or (G₂.lookup e) = some L := by
    simpa [lookupG, List.lookup_append] using hLookup
  cases hLeft : G₁.lookup e with
  | none =>
      have hRight : G₂.lookup e = some L := by
        simpa [hLeft] using hLookup'
      right
      exact ⟨e, L, by simpa [lookupG] using hRight, hSid⟩
  | some L1 =>
      have hEq : L1 = L := by
        simpa [hLeft] using hLookup'
      left
      exact ⟨e, L1, by simpa [lookupG] using hLeft, by simpa [hEq] using hSid⟩

/-- Left sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_left {G₁ G₂ : GEnv} :
    SessionsOf G₁ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  rcases hs with ⟨e, L, hLookup, hSid⟩
  exact ⟨e, L, lookupG_append_left hLookup, hSid⟩

/-- Right sessions embed into appended GEnv sessions. -/
theorem SessionsOf_append_right {G₁ G₂ : GEnv} :
    SessionsOf G₂ ⊆ SessionsOf (G₁ ++ G₂) := by
  intro s hs
  by_cases hIn1 : s ∈ SessionsOf G₁
  · exact SessionsOf_append_left (G₂:=G₂) hIn1
  · rcases hs with ⟨e, L, hLookup, hSid⟩
    have hNone : lookupG G₁ e = none := by
      apply lookupG_none_of_not_session
      intro hMem
      exact hIn1 (by simpa [hSid] using hMem)
    have hLookup' : lookupG (G₁ ++ G₂) e = some L := by
      simpa [lookupG_append_right hNone] using hLookup
    exact ⟨e, L, hLookup', hSid⟩

/-- Disjointness is preserved when the left sessions shrink. -/
theorem DisjointG_of_subset_left {G₁ G₁' G₂ : GEnv} :
    SessionsOf G₁' ⊆ SessionsOf G₁ →
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ := by
  intro hSub hDisj
  -- show SessionsOf G₁' ∩ SessionsOf G₂ = ∅
  ext s; constructor
  · intro hMem
    have hLeft : s ∈ SessionsOf G₁ := hSub hMem.1
    have hRight : s ∈ SessionsOf G₂ := hMem.2
    have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hLeft, hRight⟩
    have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
    have hContra : s ∈ (∅ : Set SessionId) := by
      simpa [hEmpty] using hInter
    exact hContra.elim
  · intro hMem
    exact hMem.elim

/-- DisjointG is symmetric. -/
theorem DisjointG_symm {G₁ G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₂ G₁ := by
  intro hDisj
  unfold DisjointG at *
  unfold GEnvDisjoint at hDisj
  unfold GEnvDisjoint
  simpa [Set.inter_comm] using hDisj

theorem DisjointG_append_left {G₁ G₁' G₂ : GEnv} :
    DisjointG G₁ G₂ →
    DisjointG G₁' G₂ →
    DisjointG (G₁ ++ G₁') G₂ := by
  intro hDisj1 hDisj2
  unfold DisjointG at *
  unfold GEnvDisjoint at *
  ext s; constructor
  · intro hMem
    rcases hMem with ⟨hInLeft, hInRight⟩
    rcases hInLeft with ⟨e, L, hLookup, hSid⟩
    have hInv := lookupG_append_inv (G₁:=G₁) (G₂:=G₁') (e:=e) (L:=L) hLookup
    cases hInv with
    | inl hLeft =>
        have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₂ := by
          exact ⟨⟨e, L, hLeft, hSid⟩, hInRight⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj1
        have hContra : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact hContra.elim
    | inr hRight =>
        rcases hRight with ⟨_, hLookupR⟩
        have hInter : s ∈ SessionsOf G₁' ∩ SessionsOf G₂ := by
          exact ⟨⟨e, L, hLookupR, hSid⟩, hInRight⟩
        have hEmpty : SessionsOf G₁' ∩ SessionsOf G₂ = ∅ := hDisj2
        have hContra : s ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact hContra.elim
  · intro hMem
    exact hMem.elim

axiom lookupD_append_left {D₁ D₂ : DEnv} {e : Edge} :
    lookupD D₁ e ≠ [] →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e

axiom lookupD_append_right {D₁ D₂ : DEnv} {e : Edge} :
    D₁.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₂ e

axiom lookupD_append_left_of_right_none {D₁ D₂ : DEnv} {e : Edge} :
    D₂.find? e = none →
    lookupD (D₁ ++ D₂) e = lookupD D₁ e

axiom lookupSEnv_append_left {S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    lookupSEnv S₁ x = some T →
    lookupSEnv (S₁ ++ S₂) x = some T

/-- Lookup in appended SEnv falls back to the right when left is missing. -/
axiom lookupSEnv_append_right {S₁ S₂ : SEnv} {x : Var} :
    lookupSEnv S₁ x = none →
    lookupSEnv (S₁ ++ S₂) x = lookupSEnv S₂ x

/-- Domain subset: left part embeds into append. -/
axiom SEnvDomSubset_append_left {S₁ S₂ : SEnv} :
    SEnvDomSubset S₁ (S₁ ++ S₂)

/-- Domain subset: right part embeds into append. -/
axiom SEnvDomSubset_append_right {S₁ S₂ : SEnv} :
    SEnvDomSubset S₂ (S₁ ++ S₂)

axiom lookupSEnv_all_frame_left {Ssh S₁ S₂ : SEnv} {x : Var} {T : ValType} :
    DisjointS S₁ S₂ →
    lookupSEnv (Ssh ++ S₂) x = some T →
    lookupSEnv (Ssh ++ (S₁ ++ S₂)) x = some T

/-- Pre-out typing never shrinks the owned variable environment (by domain). -/
theorem HasTypeProcPreOut_domsubset {Ssh Sown G P Sown' G' W Δ} :
    HasTypeProcPreOut Ssh Sown G P Sown' G' W Δ →
    SEnvDomSubset Sown Sown' := by
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
  | branch _ _ _ _ _ _ hDom =>
      exact hDom
  | seq hP hQ ihP ihQ =>
      exact SEnvDomSubset_trans ihP ihQ
  | par split hSfin hGfin hW hΔ hDisjG hDisjS hDisjS_left hDisjS_right hDisjS' hDisjW hDisjΔ hP hQ ihP ihQ =>
      rename_i S₁out S₂out G₁out G₂out W₁ W₂ Δ₁ Δ₂
      intro x T hLookup
      have hLookupS : lookupSEnv (split.S1 ++ split.S2) x = some T := by
        simpa [split.hS] using hLookup
      by_cases hLeftNone : lookupSEnv split.S1 x = none
      · have hRight : lookupSEnv split.S2 x = some T := by
          have hEq := lookupSEnv_append_right (S₁:=split.S1) (S₂:=split.S2) (x:=x) hLeftNone
          simpa [hEq] using hLookupS
        obtain ⟨T', hRight'⟩ := ihQ hRight
        have hLeftNone' : lookupSEnv S₁out x = none := by
          by_cases hSome : lookupSEnv S₁out x = none
          · exact hSome
          · cases hSome' : lookupSEnv S₁out x with
            | none => exact (hSome hSome').elim
            | some T₁ =>
                exact (hDisjS' x T₁ T' hSome' hRight').elim
        have hEq := lookupSEnv_append_right (S₁:=S₁out) (S₂:=S₂out) (x:=x) hLeftNone'
        have hAppend : lookupSEnv (S₁out ++ S₂out) x = some T' := by
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
            obtain ⟨T', hLeft'⟩ := ihP (by simpa [hEqT] using hLeftSome)
            have hAppend := lookupSEnv_append_left (S₁:=S₁out) (S₂:=S₂out) hLeft'
            exact ⟨T', by simpa [hSfin] using hAppend⟩
  | assign_new =>
      exact SEnvDomSubset_update_left
  | assign_old =>
      exact SEnvDomSubset_update_left

/-- StoreTyped splits to the left portion of SEnv. -/
theorem StoreTyped_split_left {G : GEnv} {S₁ S₂ : SEnv} {store : Store} :
    StoreTyped G (S₁ ++ S₂) store →
    StoreTyped G S₁ store := by
  intro hST x v T hStore hS
  have hS' : lookupSEnv (S₁ ++ S₂) x = some T :=
    lookupSEnv_append_left (S₁:=S₁) (S₂:=S₂) hS
  exact hST x v T hStore hS'

/-- StoreTyped splits to the right portion of SEnv (requires disjointness). -/
theorem StoreTyped_split_right {G : GEnv} {S₁ S₂ : SEnv} {store : Store}
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

/-- Coherence splits to the left portion of G/D. -/
theorem Coherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    Coherent (G₁ ++ G₂) (D₁ ++ D₂) →
    Coherent G₁ D₁ := by
  intro hCoh e Lsender Lrecv hGsender hGrecv
  have hGsender' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.sender } = some Lsender :=
    lookupG_append_left hGsender
  have hGrecv' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv :=
    lookupG_append_left hGrecv
  by_cases hTrace : lookupD D₁ e = []
  · -- Empty trace: Consume is trivially some
    simp [hTrace, Consume]
  · -- Non-empty trace: use coherence of the merged env
    have hTrace' : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
      lookupD_append_left (e := e) hTrace
    have hCoh' := hCoh e Lsender Lrecv hGsender' hGrecv'
    simpa [hTrace'] using hCoh'

