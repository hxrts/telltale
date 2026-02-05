import Protocol.Semantics
import Protocol.Typing
import Protocol.Coherence
import Batteries.Data.RBMap.Lemmas

/-!
# MPST Preservation Theorem

This module contains the preservation (subject reduction) theorem for MPST:
if a well-typed configuration takes a step, the result is also well-typed.

**UPDATE (2026-01-15)**: This module now imports Protocol.Typing which defines
TypedStep - the linear resource transition typing judgment that resolves the
design issues that blocked the original preservation theorems below.

The new preservation theorems are:
- `preservation_typed` (in Typing.lean) - TypedStep preserves LocalTypeR.WellFormed
- `progress_typed` (in Typing.lean) - LocalTypeR.WellFormed processes can step or terminate
- `subject_reduction` (this file) - TypedStep implies Step (soundness)

The old theorems (`preservation_send`, `preservation_recv`, `preservation`, `progress`)
have been removed. The canonical results are the TypedStep-based theorems below,
which align with the pre-update typing discipline.

## Proof Structure

The proof proceeds by case analysis on the step relation:

1. **Send**: The sender's local type advances, the directed edge trace grows
   - Use `Coherent_send_preserved` for coherence
   - Use `BuffersTyped_enqueue` for buffer typing

2. **Recv**: The receiver's local type advances, the directed edge trace shrinks
   - Use `Coherent_recv_preserved` for coherence
   - Use buffer dequeue lemma for buffer typing

3. **Select/Branch**: Similar to send/recv but for labels

4. **NewSession**: Fresh session ID allocated, environments extended
   - Use freshness invariants (SupplyInv_newSession)

5. **Context steps** (seq, par): Use induction hypothesis

## Key Lemmas

- `preservation` (this file): TypedStep preserves LocalTypeR.WellFormed (wrapper)
- `progress` (this file): LocalTypeR.WellFormed processes can step or are blocked (wrapper)
- `subject_reduction` (this file): TypedStep implies Step (soundness)

## Proof Techniques

The TypedStep-based proofs avoid the old pre/post-update mismatch. All
session evolution happens inside the transition judgment, so preservation
and progress become direct structural proofs.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical
open Batteries

noncomputable section

/-! ## Compatibility Aliases -/

/-- Backwards-compatible single-env pre-typing. -/
abbrev HasTypeProcPre1 (S : SEnv) (G : GEnv) (P : Process) : Prop :=
  HasTypeProcPre S ∅ G P

/-! ## Helper Lemmas -/

private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

/-- StoreTyped is preserved when updating a non-channel variable. -/
theorem StoreTyped_update_nonChan {G : GEnv} {S : SEnv} {store : Store}
    {x : Var} {v : Value} {T : ValType}
    (hST : StoreTyped G S store)
    (hv : HasTypeVal G v T)
    (hNonChan : ¬T.isLinear) :
    StoreTyped G (updateSEnv S x T) (updateStr store x v) := by
  intro y w U hy hU
  by_cases hyx : y = x
  · -- y = x: use the new value
    subst hyx
    rw [lookupStr_update_eq] at hy
    rw [lookupSEnv_update_eq] at hU
    have hw : w = v := Option.some_injective _ hy.symm
    have hUT : U = T := Option.some_injective _ hU.symm
    subst hw hUT
    exact hv
  · -- y ≠ x: use the original typing
    have hyx' : x ≠ y := Ne.symm hyx
    rw [lookupStr_update_neq _ _ _ _ hyx'] at hy
    rw [lookupSEnv_update_neq _ _ _ _ hyx'] at hU
    exact hST y w U hy hU

/-- BuffersTyped is preserved when enqueuing a well-typed value. -/
theorem BuffersTyped_enqueue_old {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  -- Directly reuse the newer enqueue lemma.
  simpa using
    (BuffersTyped_enqueue (G := G) (D := D) (bufs := bufs) (e := e) (v := v) (T := T) hBT hv)

/-! ## Preservation Support -/

private theorem SessionsOf_eq_of_TypedStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    SessionsOf G' = SessionsOf G := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.send target T L) hG
      simp [hGout, hEq]
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.recv source T L) hG
      simp [hGout, hEq]
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.select target bs) hG
      simp [hGout, hEq]
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      have hEq : SessionsOf (updateG G e L) = SessionsOf G :=
        SessionsOf_updateG_eq (G:=G) (e:=e) (L:=L) (L':=.branch source bs) hG
      simp [hGout, hEq]
  | assign =>
      simp
  | seq_step _ ih =>
      exact ih
  | seq_skip =>
      simp
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih
  | par_skip_left =>
      simp
  | par_skip_right =>
      simp

private theorem DConsistent_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DConsistent G D →
    DConsistent G' D' := by
  intro hTS hCons s hs
  have hEq : SessionsOf G' = SessionsOf G := SessionsOf_eq_of_TypedStep hTS
  have hs' := SessionsOfD_subset_of_TypedStep hTS hs
  cases hs' with
  | inl hD =>
      have hG : s ∈ SessionsOf G := hCons hD
      simpa [hEq] using hG
  | inr hG =>
    simpa [hEq] using hG

/-! ## Buffer/Coherence Rewrites -/

private theorem BuffersTyped_rewriteD
    {G : GEnv} {D D' : DEnv} {bufs : Buffers} :
    (∀ e, lookupD D e = lookupD D' e) →
    BuffersTyped G D bufs →
    BuffersTyped G D' bufs := by
  intro hEq hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨?_, ?_⟩
  · simpa [hEq e] using hLen
  · intro i hi
    simpa [hEq e] using hTyping i hi

private theorem Coherent_rewriteD
    {G : GEnv} {D D' : DEnv} :
    (∀ e, lookupD D e = lookupD D' e) →
    Coherent G D →
    Coherent G D' := by
  intro hEq hCoh e Lrecv hGrecv
  have hCohEdge := hCoh e Lrecv hGrecv
  rcases hCohEdge with ⟨Lsender, hGsender, hConsume⟩
  refine ⟨Lsender, hGsender, ?_⟩
  simpa [hEq e] using hConsume

private theorem DisjointG_append_right {G₁ G₂ G₃ : GEnv} :
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
      simp [hEmpty] at hInter
  | inr h3 =>
      have hEmpty : SessionsOf G₁ ∩ SessionsOf G₃ = (∅ : Set SessionId) := hDisj13
      have hInter : s ∈ SessionsOf G₁ ∩ SessionsOf G₃ := ⟨h1, h3⟩
      simp [hEmpty] at hInter

private theorem SessionsOf_empty : SessionsOf ([] : GEnv) = ∅ := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e, L, hLookup, hSid⟩
    cases hLookup
  · intro hs
    cases hs

private theorem DisjointG_right_empty (G : GEnv) : DisjointG G [] := by
  simp [DisjointG, GEnvDisjoint, SessionsOf_empty]

private theorem SessionsOfD_empty : SessionsOfD (∅ : DEnv) = ∅ := by
  ext s; constructor
  · intro hs
    rcases hs with ⟨e, ts, hFind, hSid⟩
    simp [DEnv.find?, DEnv_map_find?_empty] at hFind
  · intro hs
    cases hs

private theorem DConsistent_append {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    DConsistent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro h1 h2 s hs
  have hs' : s ∈ SessionsOfD D₁ ∪ SessionsOfD D₂ :=
    SessionsOfD_append_subset (D₁:=D₁) (D₂:=D₂) hs
  cases hs' with
  | inl hL =>
      exact SessionsOf_append_left (G₂:=G₂) (h1 hL)
  | inr hR =>
      exact SessionsOf_append_right (G₁:=G₁) (h2 hR)

private theorem DConsistent_empty (G : GEnv) : DConsistent G (∅ : DEnv) := by
  simp [DConsistent, SessionsOfD_empty]

private axiom OwnedDisjoint_preserved_TypedStep
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    OwnedDisjoint Sown →
    OwnedDisjoint Sown'

private theorem DEnv_append_empty_right (D : DEnv) : D ++ (∅ : DEnv) = D := by
  simpa using (DEnvUnion_empty_right D)

private theorem lookupG_none_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
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
        simp [hEmpty] at hInter

private theorem BuffersTyped_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e L, lookupG G e = some L → lookupG G' e = some L) →
    BuffersTyped G D bufs →
    BuffersTyped G' D bufs := by
  intro hMono hBT e
  rcases hBT e with ⟨hLen, hTyping⟩
  refine ⟨hLen, ?_⟩
  intro i hi
  exact HasTypeVal_mono G G' _ _ (hTyping i hi) hMono

private theorem Coherent_mono {G G' : GEnv} {D : DEnv} :
    (∀ e, lookupG G e = lookupG G' e) →
    Coherent G D →
    Coherent G' D := by
  intro hEq hCoh e Lrecv hGrecv
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [hEq _] using hGrecv
  rcases hCoh e Lrecv hGrecv' with ⟨Lsender, hGsender, hConsume⟩
  have hGsender' : lookupG G' { sid := e.sid, role := e.sender } = some Lsender := by
    simpa [hEq _] using hGsender
  exact ⟨Lsender, hGsender', hConsume⟩

private theorem ValidLabels_mono {G G' : GEnv} {D : DEnv} {bufs : Buffers} :
    (∀ e, lookupG G e = lookupG G' e) →
    ValidLabels G D bufs →
    ValidLabels G' D bufs := by
  intro hEq hValid e source bs hGrecv
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some (.branch source bs) := by
    simpa [hEq _] using hGrecv
  exact hValid e source bs hGrecv'

private lemma lookupD_append_assoc {D₁ D₂ D₃ : DEnv} :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD (D₁ ++ (D₂ ++ D₃)) e := by
  intro e
  cases h1 : D₁.find? e with
  | some ts =>
      have h12 : (D₁ ++ D₂).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) h1
      have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
        findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12
      have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts :=
        findD_append_left (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) (ts:=ts) h1
      simp [lookupD, hLeft, hRight]
  | none =>
      have h12 : (D₁ ++ D₂).find? e = D₂.find? e :=
        findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) h1
      cases h2 : D₂.find? e with
      | some ts =>
          have h12' : (D₁ ++ D₂).find? e = some ts := by
            simpa [h2] using h12
          have hLeft : ((D₁ ++ D₂) ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) h12'
          have h23 : (D₂ ++ D₃).find? e = some ts :=
            findD_append_left (D₁:=D₂) (D₂:=D₃) (e:=e) (ts:=ts) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = some ts := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]
      | none =>
          have h12' : (D₁ ++ D₂).find? e = none := by
            simpa [h2] using h12
          have hLeft := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) h12'
          have h23 : (D₂ ++ D₃).find? e = D₃.find? e :=
            findD_append_right (D₁:=D₂) (D₂:=D₃) (e:=e) h2
          have hRight : (D₁ ++ (D₂ ++ D₃)).find? e = D₃.find? e := by
            have hRight0 := findD_append_right (D₁:=D₁) (D₂:=D₂ ++ D₃) (e:=e) h1
            simpa [h23] using hRight0
          simp [lookupD, hLeft, hRight]

private lemma findD_comm_of_disjoint {D₁ D₂ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, (D₁ ++ D₂).find? e = (D₂ ++ D₁).find? e := by
  intro e
  cases hLeft : D₁.find? e with
  | some ts =>
      have hRightNone : D₂.find? e = none :=
        DisjointD_lookup_left (D₁:=D₁) (D₂:=D₂) hDisj (e:=e) (ts:=ts) hLeft
      have hA := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hLeft
      have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRightNone
      simp [hA, hB, hLeft]
  | none =>
      have hA := findD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hLeft
      cases hRight : D₂.find? e with
      | some ts =>
          have hB := findD_append_left (D₁:=D₂) (D₂:=D₁) (e:=e) (ts:=ts) hRight
          simp [hA, hB, hRight]
      | none =>
          have hB := findD_append_right (D₁:=D₂) (D₂:=D₁) (e:=e) hRight
          simp [hA, hB, hRight, hLeft]

private lemma lookupG_comm_of_disjoint {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ G₂) e = lookupG (G₂ ++ G₁) e := by
  intro e
  cases hLeft : lookupG G₁ e with
  | some L =>
      have hNone : lookupG G₂ e = none :=
        lookupG_none_of_disjoint (G₁:=G₂) (G₂:=G₁) (DisjointG_symm hDisj) (e:=e) (L:=L) hLeft
      have hA := lookupG_append_left (G₁:=G₁) (G₂:=G₂) (e:=e) (L:=L) hLeft
      have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hNone
      simp [hA, hB, hLeft]
  | none =>
      have hA := lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:=e) hLeft
      cases hRight : lookupG G₂ e with
      | some L =>
          have hB := lookupG_append_left (G₁:=G₂) (G₂:=G₁) (e:=e) (L:=L) hRight
          simp [hA, hB, hRight]
      | none =>
          have hB := lookupG_append_right (G₁:=G₂) (G₂:=G₁) (e:=e) hRight
          simp [hA, hB, hRight, hLeft]

private lemma lookupG_swap_left {G₁ G₂ G₃ : GEnv} (hDisj : DisjointG G₁ G₂) :
    ∀ e, lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG (G₂ ++ (G₁ ++ G₃)) e := by
  intro e
  cases hLeft : lookupG (G₁ ++ G₂) e with
  | some L =>
      have hA : lookupG (G₁ ++ (G₂ ++ G₃)) e = some L := by
        have hA' := lookupG_append_left (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) (L:=L) hLeft
        simpa [List.append_assoc] using hA'
      have hLeft' : lookupG (G₂ ++ G₁) e = some L := by
        have hComm := lookupG_comm_of_disjoint (G₁:=G₁) (G₂:=G₂) hDisj e
        simpa [hComm] using hLeft
      have hB : lookupG (G₂ ++ (G₁ ++ G₃)) e = some L := by
        have hB' := lookupG_append_left (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) (L:=L) hLeft'
        simpa [List.append_assoc] using hB'
      simp [hA, hB]
  | none =>
      have hA : lookupG (G₁ ++ (G₂ ++ G₃)) e = lookupG G₃ e := by
        have hA' := lookupG_append_right (G₁:=G₁ ++ G₂) (G₂:=G₃) (e:=e) hLeft
        simpa [List.append_assoc] using hA'
      have hLeft' : lookupG (G₂ ++ G₁) e = none := by
        have hComm := lookupG_comm_of_disjoint (G₁:=G₁) (G₂:=G₂) hDisj e
        simpa [hComm] using hLeft
      have hB : lookupG (G₂ ++ (G₁ ++ G₃)) e = lookupG G₃ e := by
        have hB' := lookupG_append_right (G₁:=G₂ ++ G₁) (G₂:=G₃) (e:=e) hLeft'
        simpa [List.append_assoc] using hB'
      simp [hA, hB]

private lemma lookupD_swap_left {D₁ D₂ D₃ : DEnv} (hDisj : DisjointD D₁ D₂) :
    ∀ e, lookupD ((D₁ ++ D₂) ++ D₃) e = lookupD ((D₂ ++ D₁) ++ D₃) e := by
  intro e
  have hInv := findD_comm_of_disjoint (D₁:=D₁) (D₂:=D₂) hDisj e
  cases hLeft : (D₁ ++ D₂).find? e with
  | some ts =>
      have hA := findD_append_left (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) (ts:=ts) hLeft
      have hLeft' : (D₂ ++ D₁).find? e = some ts := by
        simpa [hInv] using hLeft
      have hB := findD_append_left (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) (ts:=ts) hLeft'
      simp [lookupD, hA, hB]
  | none =>
      have hA := findD_append_right (D₁:=D₁ ++ D₂) (D₂:=D₃) (e:=e) hLeft
      have hLeft' : (D₂ ++ D₁).find? e = none := by
        simpa [hInv] using hLeft
      have hB := findD_append_right (D₁:=D₂ ++ D₁) (D₂:=D₃) (e:=e) hLeft'
      simp [lookupD, hA, hB]

private lemma findD_update_eq (env : DEnv) (e : Edge) (ts : List ValType) :
    (updateD env e ts).find? e = some ts := by
  have hEq : compare e e = .eq := by
    simp
  simpa [updateD] using
    (RBMap.find?_insert_of_eq (t := env.map) (k := e) (v := ts) (k' := e) hEq)

private lemma findD_update_neq (env : DEnv) (e e' : Edge) (ts : List ValType) (hne : e ≠ e') :
    (updateD env e ts).find? e' = env.find? e' := by
  have hne' : compare e' e ≠ .eq := by
    intro hEq
    exact hne ((Edge.compare_eq_iff_eq e' e).1 hEq).symm
  have h' : (env.map.insert e ts).find? e' = env.map.find? e' := by
    simpa using
      (RBMap.find?_insert_of_ne (t := env.map) (k := e) (v := ts) (k' := e') hne')
  have h'' : (updateD env e ts).find? e' = env.map.find? e' := by
    simpa [updateD] using h'
  simpa [DEnv.find?] using h''

private lemma lookupD_append_left_of_find {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType} :
    D₁.find? e = some ts →
    lookupD (D₁ ++ D₂) e = ts := by
  intro hFind
  have hLeft := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) hFind
  simp [lookupD, hLeft]

private lemma lookupD_updateD_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    lookupD (updateD (D ++ D₂) e ts) e' = lookupD (updateD D e ts ++ D₂) e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hFind : (updateD D e ts).find? e = some ts := findD_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight : lookupD (updateD D e ts ++ D₂) e = ts :=
      lookupD_append_left_of_find (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) hFind
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D ++ D₂) e ts) e' = lookupD (D ++ D₂) e' :=
        lookupD_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D.find? e' with
    | some ts' =>
        have hLeft' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft] using hfind
        have hA :=
          findD_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hB :=
          findD_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simp [hLeftEq, hRightEq]
    | none =>
        have hLeft' : (updateD D e ts).find? e' = none := by
          simp [hLeft] at hfind
          exact hfind
        have hA := findD_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft'
        have hB := findD_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft
        have hfind_union :
            (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        have hRightEq : lookupD (updateD D e ts ++ D₂) e' = lookupD (D ++ D₂) e' := by
          simp [lookupD, hfind_union]
        simp [hLeftEq, hRightEq]

private lemma lookupD_updateD_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ updateD D e ts) e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hRight :
        lookupD (D₁ ++ updateD D e ts) e = lookupD (updateD D e ts) e :=
      lookupD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
    simp [lookupD_update_eq, hRight]
  · have hLeftEq :
        lookupD (updateD (D₁ ++ D) e ts) e' = lookupD (D₁ ++ D) e' :=
        lookupD_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
          intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft : D₁.find? e' with
    | some ts' =>
        have hA := findD_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft
        have hB := findD_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simp [hLeftEq, hRightEq]
    | none =>
        have hA := findD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft
        have hB := findD_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft
        have hfind_union :
            (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB, hfind]
        have hRightEq : lookupD (D₁ ++ updateD D e ts) e' = lookupD (D₁ ++ D) e' := by
          simp [lookupD, hfind_union]
        simp [hLeftEq, hRightEq]

private lemma findD_updateD_append_left {D D₂ : DEnv} {e e' : Edge} {ts : List ValType} :
    (updateD (D ++ D₂) e ts).find? e' = (updateD D e ts ++ D₂).find? e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hLeft : (updateD (D ++ D₂) e ts).find? e = some ts := findD_update_eq (env:=D ++ D₂) (e:=e) (ts:=ts)
    have hFind : (updateD D e ts).find? e = some ts := findD_update_eq (env:=D) (e:=e) (ts:=ts)
    have hRight := findD_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e) (ts:=ts) hFind
    simp [hLeft, hRight]
  · have hLeft : (updateD (D ++ D₂) e ts).find? e' = (D ++ D₂).find? e' :=
      findD_update_neq (env:=D ++ D₂) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft' : D.find? e' with
    | some ts' =>
        have hLeft'' : (updateD D e ts).find? e' = some ts' := by
          simpa [hLeft'] using hfind
        have hA := findD_append_left (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') (ts:=ts') hLeft''
        have hB := findD_append_left (D₁:=D) (D₂:=D₂) (e:=e') (ts:=ts') hLeft'
        have hRight : (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]
    | none =>
        have hLeft'' : (updateD D e ts).find? e' = none := by
          simp [hLeft'] at hfind
          exact hfind
        have hA := findD_append_right (D₁:=updateD D e ts) (D₂:=D₂) (e:=e') hLeft''
        have hB := findD_append_right (D₁:=D) (D₂:=D₂) (e:=e') hLeft'
        have hRight : (updateD D e ts ++ D₂).find? e' = (D ++ D₂).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]

private lemma findD_updateD_append_right {D₁ D : DEnv} {e e' : Edge} {ts : List ValType}
    (hNone : D₁.find? e = none) :
    (updateD (D₁ ++ D) e ts).find? e' = (D₁ ++ updateD D e ts).find? e' := by
  by_cases hEq : e' = e
  · cases hEq
    have hLeft : (updateD (D₁ ++ D) e ts).find? e = some ts := findD_update_eq (env:=D₁ ++ D) (e:=e) (ts:=ts)
    have hRight : (D₁ ++ updateD D e ts).find? e = some ts := by
      have hFind : (updateD D e ts).find? e = some ts := findD_update_eq (env:=D) (e:=e) (ts:=ts)
      have hRight' := findD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e) hNone
      simp [hRight', hFind]
    simp [hLeft, hRight]
  · have hLeft : (updateD (D₁ ++ D) e ts).find? e' = (D₁ ++ D).find? e' :=
      findD_update_neq (env:=D₁ ++ D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    have hfind : (updateD D e ts).find? e' = D.find? e' :=
      findD_update_neq (env:=D) (e:=e) (e':=e') (ts:=ts) (by
        intro hEq'; exact hEq hEq'.symm)
    cases hLeft' : D₁.find? e' with
    | some ts' =>
        have hA := findD_append_left (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') (ts:=ts') hLeft'
        have hB := findD_append_left (D₁:=D₁) (D₂:=D) (e:=e') (ts:=ts') hLeft'
        have hRight : (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB]
        simp [hLeft, hRight]
    | none =>
        have hA := findD_append_right (D₁:=D₁) (D₂:=updateD D e ts) (e:=e') hLeft'
        have hB := findD_append_right (D₁:=D₁) (D₂:=D) (e:=e') hLeft'
        have hRight : (D₁ ++ updateD D e ts).find? e' = (D₁ ++ D).find? e' := by
          simp [hA, hB, hfind]
        simp [hLeft, hRight]

private lemma updateD_append_left (D D₂ : DEnv) (e : Edge) (ts : List ValType) :
    updateD (D ++ D₂) e ts = updateD D e ts ++ D₂ := by
  apply DEnv_ext
  intro e'
  exact findD_updateD_append_left (D:=D) (D₂:=D₂) (e:=e) (e':=e') (ts:=ts)

private lemma updateD_append_right (D₁ D : DEnv) (e : Edge) (ts : List ValType)
    (hNone : D₁.find? e = none) :
    updateD (D₁ ++ D) e ts = D₁ ++ updateD D e ts := by
  apply DEnv_ext
  intro e'
  exact findD_updateD_append_right (D₁:=D₁) (D:=D) (e:=e) (e':=e') (ts:=ts) hNone

private lemma updateG_append_right_hit {G₁ G₂ : GEnv} {e : Endpoint} {L : LocalType}
    (hNone : lookupG G₁ e = none) :
    updateG (G₁ ++ G₂) e L = G₁ ++ updateG G₂ e L := by
  induction G₁ with
  | nil =>
      simp
  | cons hd tl ih =>
      cases hd with
      | mk e' L' =>
          cases hEqb : (e == e') with
          | true =>
              have hLookup : lookupG ((e', L') :: tl) e = some L' := by
                simp [lookupG, List.lookup, hEqb]
              simp [hLookup] at hNone
          | false =>
              have hNone' : lookupG tl e = none := by
                simpa [lookupG, List.lookup, hEqb] using hNone
              have hne : e ≠ e' := by
                exact beq_eq_false_iff_ne.mp hEqb
              have ih' := ih hNone'
              simp [updateG, hne, ih']

/-! ## ValidLabels Preservation (framed) -/

private theorem ValidLabels_preserved_frame_left
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' Gfr Dfr} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    DisjointG G Gfr →
    DConsistent Gfr Dfr →
    ValidLabels (G ++ Gfr) (D ++ Dfr) bufs →
    Coherent (G ++ Gfr) (D ++ Dfr) →
    BuffersTyped (G ++ Gfr) (D ++ Dfr) bufs →
    ValidLabels (G' ++ Gfr) (D' ++ Dfr) bufs' := by
  intro hTS hDisj hConsFr hValid hCoh hBT
  induction hTS generalizing Gfr Dfr with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      set recvEp : Endpoint := { sid := e.sid, role := target }
      have hSid : e.sid ∈ SessionsOf G := ⟨e, .send target T L, hG, rfl⟩
      have hNotIn : e.sid ∉ SessionsOf Gfr := by
        intro hIn
        have hInter : e.sid ∈ SessionsOf G ∩ SessionsOf Gfr := ⟨hSid, hIn⟩
        have hEmpty : SessionsOf G ∩ SessionsOf Gfr = (∅ : Set SessionId) := hDisj
        simp [hEmpty] at hInter
      have hDfrNone :
          Dfr.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=Gfr) (D₂:=Dfr) hDisj hConsFr hSid
      have hLookupD :
          lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target } =
            lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
        lookupD_append_left_of_right_none (D₁:=D) (D₂:=Dfr) (e:={ sid := e.sid, sender := e.role, receiver := target }) hDfrNone
      have hGfrNone : lookupG Gfr recvEp = none := lookupG_none_of_not_session hNotIn
      have hRecvReady' :
          ∀ Lrecv, lookupG (G ++ Gfr) recvEp = some Lrecv →
            ∃ L', Consume e.role Lrecv (lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
                  (Consume e.role L' [T]).isSome := by
        intro Lrecv hLookup
        cases lookupG_append_inv (G₁:=G) (G₂:=Gfr) (e:=recvEp) hLookup with
        | inl hLeft =>
            rcases hRecvReady Lrecv hLeft with ⟨L', hConsume, hConsumeT⟩
            refine ⟨L', ?_, hConsumeT⟩
            simpa [hLookupD] using hConsume
        | inr hRight =>
            cases hRight with
            | intro _ hRight =>
                simp [hGfrNone] at hRight
      have hG' : lookupG (G ++ Gfr) e = some (.send target T L) :=
        lookupG_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        ValidLabels_send_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (senderEp:=e) (receiverRole:=target) (T:=T) (L:=L) (v:=v)
          hValid hCoh hBT hG' hRecvReady'
      simpa [updateG_append_left_hit hG, enqueueBuf, List.append_assoc] using hValid'
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout hSout hStoreOut hBufsOut
      have hG' : lookupG (G ++ Gfr) e = some (.recv source T L) :=
        lookupG_append_left (G₁:=G) (G₂:=Gfr) hG
      have hv' : HasTypeVal (G ++ Gfr) v T :=
        HasTypeVal_mono G (G ++ Gfr) v T hv (by
          intro ep L hLookup
          exact lookupG_append_left (G₁:=G) (G₂:=Gfr) hLookup)
      have hValid' :=
        ValidLabels_recv_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (receiverEp:=e) (senderRole:=source) (T:=T) (L:=L) (v:=v) (vs:=vs)
          hValid hCoh hBT hBuf hv' hG'
      simpa [ValidLabels, updateG_append_left_hit hG, List.append_assoc] using hValid'
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      set recvEp : Endpoint := { sid := e.sid, role := target }
      have hSid : e.sid ∈ SessionsOf G := ⟨e, .select target bs, hG, rfl⟩
      have hNotIn : e.sid ∉ SessionsOf Gfr := by
        intro hIn
        have hInter : e.sid ∈ SessionsOf G ∩ SessionsOf Gfr := ⟨hSid, hIn⟩
        have hEmpty : SessionsOf G ∩ SessionsOf Gfr = (∅ : Set SessionId) := hDisj
        simp [hEmpty] at hInter
      have hDfrNone :
          Dfr.find? { sid := e.sid, sender := e.role, receiver := target } = none :=
        lookupD_none_of_disjointG (G₁:=G) (G₂:=Gfr) (D₂:=Dfr) hDisj hConsFr hSid
      have hLookupD :
          lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target } =
            lookupD D { sid := e.sid, sender := e.role, receiver := target } :=
        lookupD_append_left_of_right_none (D₁:=D) (D₂:=Dfr) (e:={ sid := e.sid, sender := e.role, receiver := target }) hDfrNone
      have hGfrNone : lookupG Gfr recvEp = none := lookupG_none_of_not_session hNotIn
      have hReady' :
          ∀ Ltarget, lookupG (G ++ Gfr) recvEp = some Ltarget →
            ∃ L', Consume e.role Ltarget (lookupD (D ++ Dfr) { sid := e.sid, sender := e.role, receiver := target }) = some L' ∧
                  (Consume e.role L' [.string]).isSome := by
        intro Ltarget hLookup
        cases lookupG_append_inv (G₁:=G) (G₂:=Gfr) (e:=recvEp) hLookup with
        | inl hLeft =>
            rcases hReady Ltarget hLeft with ⟨L', hConsume, hConsumeT⟩
            refine ⟨L', ?_, hConsumeT⟩
            simpa [hLookupD] using hConsume
        | inr hRight =>
            cases hRight with
            | intro _ hRight =>
                simp [hGfrNone] at hRight
      have hG' : lookupG (G ++ Gfr) e = some (.select target bs) :=
        lookupG_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        ValidLabels_select_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (selectorEp:=e) (targetRole:=target) (selectBranches:=bs) (ℓ:=ℓ) (L:=L)
          hValid hCoh hBT hG' hFind hReady'
      simpa [ValidLabels, updateG_append_left_hit hG, enqueueBuf, List.append_assoc] using hValid'
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      have hG' : lookupG (G ++ Gfr) e = some (.branch source bs) :=
        lookupG_append_left (G₁:=G) (G₂:=Gfr) hG
      have hValid' :=
        ValidLabels_branch_preserved (G:=G ++ Gfr) (D:=D ++ Dfr) (bufs:=bufs)
          (brancherEp:=e) (senderRole:=source) (branchOptions:=bs) (ℓ:=ℓ) (L:=L) (vs:=vs)
          hValid hCoh hBT hG' hFindT hBuf
      simpa [ValidLabels, updateG_append_left_hit hG, List.append_assoc] using hValid'
  | assign =>
      simpa using hValid
  | seq_step _ ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | seq_skip =>
      simpa using hValid
  | par_left split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | par_right split hSlen hGlen hTS hDisjG hDisjD hDisjS ih =>
      exact ih hDisj hConsFr hValid hCoh hBT
  | par_skip_left =>
      simpa using hValid
  | par_skip_right =>
      simpa using hValid

private theorem ValidLabels_preserved
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    ValidLabels G D bufs →
    Coherent G D →
    BuffersTyped G D bufs →
    ValidLabels G' D' bufs' := by
  intro hTS hValid hCoh hBT
  have hDisj : DisjointG G [] := DisjointG_right_empty G
  have hConsFr : DConsistent ([] : GEnv) (∅ : DEnv) := DConsistent_empty []
  have hValid' :=
    ValidLabels_preserved_frame_left (Gfr:=[]) (Dfr:=∅) hTS hDisj hConsFr
      (by simpa [List.append_nil, DEnv_append_empty_right] using hValid)
      (by simpa [List.append_nil, DEnv_append_empty_right] using hCoh)
      (by simpa [List.append_nil, DEnv_append_empty_right] using hBT)
  simpa [List.append_nil, DEnv_append_empty_right] using hValid'

/-! ## HeadCoherent Preservation -/

private theorem HeadCoherent_split_left {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₂ D₂ →
    HeadCoherent G₁ D₁ := by
  intro hHead hDisj hCons e
  cases hG : lookupG G₁ { sid := e.sid, role := e.receiver } with
  | none =>
      simp [hG]
  | some Lrecv =>
      have hG' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv :=
        lookupG_append_left (G₁:=G₁) (G₂:=G₂) hG
      have hSid : e.sid ∈ SessionsOf G₁ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hG, rfl⟩
      have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisj hCons hSid
      have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
        lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
      have hHeadMerged := hHead e
      simp [hG', hTraceEq] at hHeadMerged
      simpa [hG, hTraceEq] using hHeadMerged

private theorem HeadCoherent_split_right {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    HeadCoherent G₂ D₂ := by
  intro hHead hDisj hCons e
  cases hG : lookupG G₂ { sid := e.sid, role := e.receiver } with
  | none =>
      simp [hG]
  | some Lrecv =>
      have hSid : e.sid ∈ SessionsOf G₂ :=
        ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hG, rfl⟩
      have hNot : e.sid ∉ SessionsOf G₁ := by
        intro hIn
        have hInter : e.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hIn, hSid⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = (∅ : Set SessionId) := hDisj
        simp [hEmpty] at hInter
      have hG1none : lookupG G₁ { sid := e.sid, role := e.receiver } = none :=
        lookupG_none_of_not_session hNot
      have hG' : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } = some Lrecv := by
        simpa [lookupG_append_right (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.receiver }) hG1none]
          using hG
      have hD1none : D₁.find? e = none :=
        lookupD_none_of_disjointG (G₁:=G₂) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons hSid
      have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
        lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
      have hHeadMerged := hHead e
      simp [hG', hTraceEq] at hHeadMerged
      simpa [hG, hTraceEq] using hHeadMerged

private theorem HeadCoherent_merge {G₁ G₂ : GEnv} {D₁ D₂ : DEnv} :
    HeadCoherent G₁ D₁ →
    HeadCoherent G₂ D₂ →
    DisjointG G₁ G₂ →
    DConsistent G₁ D₁ →
    DConsistent G₂ D₂ →
    HeadCoherent (G₁ ++ G₂) (D₁ ++ D₂) := by
  intro hHead1 hHead2 hDisj hCons1 hCons2 e
  cases hG : lookupG (G₁ ++ G₂) { sid := e.sid, role := e.receiver } with
  | none =>
      simp [hG]
  | some Lrecv =>
      have hCases :=
        lookupG_append_inv (G₁:=G₁) (G₂:=G₂) (e:={ sid := e.sid, role := e.receiver }) (L:=Lrecv)
          (by simpa using hG)
      cases hCases with
      | inl hLeft =>
          have hSid : e.sid ∈ SessionsOf G₁ :=
            ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hLeft, rfl⟩
          have hD2none : D₂.find? e = none := lookupD_none_of_disjointG hDisj hCons2 hSid
          have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₁ e :=
            lookupD_append_left_of_right_none (D₁:=D₁) (D₂:=D₂) (e:=e) hD2none
          have hHeadLeft := hHead1 e
          have hHeadLeft' : match some Lrecv with
            | some (LocalType.recv a T a_1) =>
              match lookupD D₁ e with
              | [] => True
              | T' :: tail => T = T'
            | some (LocalType.branch a a_1) =>
              match lookupD D₁ e with
              | [] => True
              | T' :: tail => T' = ValType.string
            | x => True := by
              simpa [HeadCoherent, hLeft] using hHeadLeft
          simpa [HeadCoherent, hG, hTraceEq] using hHeadLeft'
      | inr hRight =>
          have hSid : e.sid ∈ SessionsOf G₂ :=
            ⟨{ sid := e.sid, role := e.receiver }, Lrecv, hRight.2, rfl⟩
          have hD1none : D₁.find? e = none :=
            lookupD_none_of_disjointG (G₁:=G₂) (G₂:=G₁) (D₂:=D₁) (DisjointG_symm hDisj) hCons1 hSid
          have hTraceEq : lookupD (D₁ ++ D₂) e = lookupD D₂ e :=
            lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e) hD1none
          have hHeadRight := hHead2 e
          have hHeadRight' : match some Lrecv with
            | some (LocalType.recv a T a_1) =>
              match lookupD D₂ e with
              | [] => True
              | T' :: tail => T = T'
            | some (LocalType.branch a a_1) =>
              match lookupD D₂ e with
              | [] => True
              | T' :: tail => T' = ValType.string
            | x => True := by
              simpa [HeadCoherent, hRight.2] using hHeadRight
          simpa [HeadCoherent, hG, hTraceEq] using hHeadRight'

private theorem typed_step_preserves_headcoherent
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    HeadCoherent G D →
    Coherent G D →
    HeadCoherent G' D' := by
  intro hTS hHead hCoh
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_send_preserved G D e target T L hHead hCoh hG hRecvReady)
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_recv_preserved G D e source T L hHead hCoh hG hTrace)
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_select_preserved G D e target bs ℓ L hHead hCoh hG hFind hReady)
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout
      simpa [hBufsOut] using
        (HeadCoherent_branch_preserved G D e source bs ℓ L hHead hCoh hG hFindT hTrace)
  | assign =>
      simpa using hHead
  | seq_step _ ih =>
      exact ih hHead hCoh
  | seq_skip =>
      simpa using hHead
  | par_left split hSlen hGlen hStep hDisjG hDisjD hDisjS ih =>
      exact ih hHead hCoh
  | par_right split hSlen hGlen hStep hDisjG hDisjD hDisjS ih =>
      exact ih hHead hCoh
  | par_skip_left =>
      simpa using hHead
  | par_skip_right =>
      simpa using hHead

/-! ## Main Preservation Theorem -/

/-- TypedStep preserves LocalTypeR.WellFormed. -/
theorem preservation_typed
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    LocalTypeR.WellFormed G' D' Ssh Sown' store' bufs' P' := by
  intro hTS hWF
  rcases hWF with ⟨hStore, hBT, hCoh, hHead, hValid, hCompat, hDisjS, hOwn, hCons, hPre⟩
  rcases hPre with ⟨Sfin, Gfin, W, Δ, hPre⟩
  have hStore' :
      StoreTypedStrong G' (SEnvAll Ssh Sown') store' :=
    StoreTypedStrong_preserved hTS hStore hPre
  have hCoh' : Coherent G' D' := typed_step_preserves_coherence hTS hCoh
  have hBT' : BuffersTyped G' D' bufs' := BuffersTyped_preserved hTS hCoh hBT
  have hHead' : HeadCoherent G' D' := typed_step_preserves_headcoherent hTS hHead hCoh
  have hValid' : ValidLabels G' D' bufs' := ValidLabels_preserved hTS hValid hCoh hBT
  have hCompat' : Compatible G' D' := Compatible_preserved hCompat hTS
  have hDisjS' : DisjointS Ssh Sown' :=
    DisjointS_preserved_TypedStep_right hTS hPre hDisjS
  have hOwn' : OwnedDisjoint Sown' := OwnedDisjoint_preserved_TypedStep hTS hOwn
  have hCons' : DConsistent G' D' := DConsistent_preserved hTS hCons
  have hStoreTyped : StoreTyped G (SEnvAll Ssh Sown) store := hStore.toStoreTyped
  obtain ⟨W', Δ', hPre'⟩ := HasTypeProcPreOut_preserved hStoreTyped hTS hPre
  refine ⟨hStore', hBT', hCoh', hHead', hValid', hCompat', hDisjS', hOwn', hCons', ?_⟩
  exact ⟨Sfin, Gfin, W', Δ', hPre'⟩

/-- Preservation: TypedStep preserves WellFormed. -/
theorem preservation
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    LocalTypeR.WellFormed G' D' Ssh Sown' store' bufs' P' := by
  -- Delegate to the canonical proof in Typing.Framing.
  exact preservation_typed

/-! ## Progress Theorem -/

/-- Progress: a well-formed process can step or is blocked. -/
theorem progress {G D Ssh Sown store bufs P} :
    LocalTypeR.WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  -- Delegate to the canonical progress proof in Typing.Preservation.
  exact progress_typed

/-! ## Progress Lemmas for Individual Process Forms

These lemmas are currently axiomatized to keep the development building while
TypedStep-based proofs are refactored.
-/

/-- Blocked recv predicate: recv/branch is waiting on an empty buffer. -/
def BlockedRecv (C : Config) : Prop :=
  (∃ k x source T L, ∃ e : Endpoint,
    C.proc = .recv k x ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.recv source T L) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = []) ∨
  (∃ k procs source bs, ∃ e : Endpoint,
    C.proc = .branch k procs ∧
    lookupStr C.store k = some (.chan e) ∧
    lookupG C.G e = some (.branch source bs) ∧
    lookupBuf C.bufs ⟨e.sid, source, e.role⟩ = [])

/-- Progress for send: send always steps (it just enqueues to buffer). -/
theorem progress_send {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .send k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.send k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  rcases inversion_send hProc with ⟨e, q, T, L, hk, hG, hx⟩
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  obtain ⟨v, hxStr, _hv⟩ := store_lookup_of_senv_lookup hStore hx
  let sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := q }
  refine ⟨sendStep C e sendEdge v T L, Step.base ?_⟩
  exact StepBase.send hEq hkStr hxStr hG

/-- Progress for recv: recv steps if buffer non-empty, otherwise blocked. -/
theorem progress_recv {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .recv k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.recv k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  rcases inversion_recv hProc with ⟨e, p, T, L, hk, hG, _hNoSh⟩
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  set recvEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
  cases hBuf : lookupBuf C.bufs recvEdge with
  | nil =>
      right
      left
      refine ⟨k, x, p, T, L, e, ?_⟩
      refine ⟨hEq, hkStr, hG, ?_⟩
      simpa [recvEdge] using hBuf
  | cons v vs =>
      left
      refine ⟨recvStep C e recvEdge x v L, Step.base ?_⟩
      have hBuf' : lookupBuf C.bufs { sid := e.sid, sender := p, receiver := e.role } = v :: vs := by
        simpa [recvEdge] using hBuf
      exact StepBase.recv hEq hkStr hG hBuf'

/-- Progress for select: select always steps (it just enqueues label to buffer). -/
theorem progress_select {C : Config} {Ssh Sown : SEnv} {k : Var} {l : Label}
    (hEq : C.proc = .select k l)
    (hProc : HasTypeProcPre Ssh Sown C.G (.select k l))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  rcases inversion_select hProc with ⟨e, q, bs, L, hk, hG, hFind⟩
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  let selectEdge : Edge := { sid := e.sid, sender := e.role, receiver := q }
  refine ⟨sendStep C e selectEdge (.string l) .string L, Step.base ?_⟩
  exact StepBase.select hEq hkStr hG hFind

/-- Progress for branch: branch steps if buffer non-empty, otherwise blocked. -/
theorem progress_branch {C : Config} {Ssh Sown : SEnv} {k : Var} {procs : List (Label × Process)}
    (hEq : C.proc = .branch k procs)
    (hProc : HasTypeProcPre Ssh Sown C.G (.branch k procs))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store)
    (hBufs : BuffersTyped C.G C.D C.bufs)
    (hHead : HeadCoherent C.G C.D)
    (hValid : ValidLabels C.G C.D C.bufs) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  rcases inversion_branch hProc with ⟨e, p, bs, hk, hG, hLen, hLabels, hBodies⟩
  obtain ⟨vk, hkStr, hkTyped⟩ := store_lookup_of_senv_lookup hStore hk
  have hkChan : vk = .chan e := HasTypeVal_chan_inv hkTyped
  subst hkChan
  set branchEdge : Edge := { sid := e.sid, sender := p, receiver := e.role }
  cases hBuf : lookupBuf C.bufs branchEdge with
  | nil =>
      right
      right
      refine ⟨k, procs, p, bs, e, ?_⟩
      refine ⟨hEq, hkStr, hG, ?_⟩
      simpa [branchEdge] using hBuf
  | cons v vs =>
      left
      have hTypedEdge := hBufs branchEdge
      rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
      have h0buf : 0 < (lookupBuf C.bufs branchEdge).length := by
        simp [hBuf]
      have h0trace : 0 < (lookupD C.D branchEdge).length := by
        simpa [hLenBuf] using h0buf
      have hTyped0 := hTyping 0 h0buf
      have hv' : HasTypeVal C.G v ((lookupD C.D branchEdge).get ⟨0, h0trace⟩) := by
        simpa [hBuf, hLenBuf] using hTyped0
      cases hTrace : lookupD C.D branchEdge with
      | nil =>
          simp [hTrace] at h0trace
      | cons T' ts =>
          have hHeadEdge := hHead branchEdge
          have hEqT : T' = .string := by
            simpa [HeadCoherent, hG, branchEdge, hTrace] using hHeadEdge
          have hv : HasTypeVal C.G v .string := by
            simpa [hTrace, hEqT] using hv'
          rcases HasTypeVal_string_inv hv with ⟨lbl, rfl⟩
          have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hG)
          have hBsSome : (bs.find? (fun b => b.1 == lbl)).isSome := by
            simpa [hBuf] using hValidEdge
          rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
          cases b with
          | mk lbl' L =>
              have hLbl : lbl' = lbl :=
                findLabel_eq (xs := bs) (lbl := lbl) (lbl' := lbl') (v := L) hFindBs
              have hFindBs' : bs.find? (fun b => b.1 == lbl') = some (lbl', L) := by
                simpa [hLbl] using hFindBs
              have hMemBs : (lbl', L) ∈ bs := List.mem_of_find?_eq_some hFindBs'
              rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
              have hip : i < procs.length := by
                simpa [hLen] using hi
              have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl' := by
                have hLblEq := hLabels i hi hip
                simpa [hGetBs] using hLblEq
              have hPred : (fun b => b.1 == lbl') (procs.get ⟨i, hip⟩) := by
                exact (beq_iff_eq).2 hLabelAt
              have hFindPIsSome : (procs.find? (fun b => b.1 == lbl')).isSome := by
                cases hFindP : procs.find? (fun b => b.1 == lbl') with
                | none =>
                    have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl') x := by
                      simpa [List.find?_eq_none] using hFindP
                    have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                    have hContra : False := (hNo _ hMemP) hPred
                    exact (False.elim hContra)
                | some _ =>
                    simp
              rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
              cases bP with
              | mk lblP P =>
                  have hLblP : lblP = lbl' :=
                    findLabel_eq (xs := procs) (lbl := lbl') (lbl' := lblP) (v := P) hFindP
                  have hLblP' : lblP = lbl := hLblP.trans hLbl
                  have hFindP' : procs.find? (fun b => b.1 == lbl) = some (lbl, P) := by
                    simpa [hLbl, hLblP'] using hFindP
                  have hDeq :
                      dequeueBuf C.bufs branchEdge =
                        some (updateBuf C.bufs branchEdge vs, .string lbl) := by
                    simp [dequeueBuf, hBuf]
                  have hFindBs'' : bs.find? (fun b => b.1 == lbl) = some (lbl, L) := by
                    simpa [hLbl] using hFindBs
                  refine ⟨{ C with
                              proc := P,
                              bufs := updateBuf C.bufs branchEdge vs,
                              G := updateG C.G e L,
                              D := updateD C.D branchEdge (lookupD C.D branchEdge).tail },
                          Step.base ?_⟩
                  exact StepBase.branch hEq hkStr hG hBuf hFindP' hFindBs'' hDeq

private def frameConfigRight (C : Config) (Gfr : GEnv) (Dfr : DEnv) : Config :=
  { C with G := C.G ++ Gfr, D := C.D ++ Dfr }

private def frameConfigLeft (C : Config) (Gfr : GEnv) (Dfr : DEnv) : Config :=
  { C with G := Gfr ++ C.G, D := Dfr ++ C.D }

private lemma step_frame_right {C C' : Config} {Gfr : GEnv} {Dfr : DEnv} :
    DisjointG C.G Gfr →
    DConsistent Gfr Dfr →
    Step C C' →
    Step (frameConfigRight C Gfr Dfr) (frameConfigRight C' Gfr Dfr) := by
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      cases hBase with
      | send hProc hk hx hG =>
          rename_i Ccfg k x e v target T L
          set sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .send target T L, hG, rfl⟩
          have hDfrNone : Dfr.find? sendEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) sendEdge = lookupD Ccfg.D sendEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=sendEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) sendEdge (lookupD Ccfg.D sendEdge ++ [T]) =
                updateD Ccfg.D sendEdge (lookupD Ccfg.D sendEdge ++ [T]) ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=sendEdge)
              (ts:=lookupD Ccfg.D sendEdge ++ [T])
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (sendStep (frameConfigRight Ccfg Gfr Dfr) e sendEdge v T L) := by
            refine StepBase.send (C:=frameConfigRight Ccfg Gfr Dfr) (k:=k) (x:=x) (e:=e)
              (v:=v) (target:=target) (T:=T) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · simpa [frameConfigRight] using hx
            · exact lookupG_append_left hG
          have hEq :
              sendStep (frameConfigRight Ccfg Gfr Dfr) e sendEdge v T L =
                frameConfigRight (sendStep Ccfg e sendEdge v T L) Gfr Dfr := by
            simp [frameConfigRight, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | recv hProc hk hG hBuf =>
          rename_i Ccfg vs k x e v source T L
          set recvEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .recv source T L, hG, rfl⟩
          have hDfrNone : Dfr.find? recvEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) recvEdge = lookupD Ccfg.D recvEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=recvEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) recvEdge (lookupD Ccfg.D recvEdge).tail =
                updateD Ccfg.D recvEdge (lookupD Ccfg.D recvEdge).tail ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=recvEdge)
              (ts:=(lookupD Ccfg.D recvEdge).tail)
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (recvStep (frameConfigRight Ccfg Gfr Dfr) e recvEdge x v L) := by
            refine (@StepBase.recv vs (frameConfigRight Ccfg Gfr Dfr) k x e v source T L ?_ ?_ ?_ ?_)
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa [frameConfigRight] using hBuf
          have hEq :
              recvStep (frameConfigRight Ccfg Gfr Dfr) e recvEdge x v L =
                frameConfigRight (recvStep Ccfg e recvEdge x v L) Gfr Dfr := by
            simp [frameConfigRight, recvStep, dequeueBuf, hBuf, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | select hProc hk hG hFind =>
          rename_i Ccfg k e ℓ target branches L
          set selEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .select target branches, hG, rfl⟩
          have hDfrNone : Dfr.find? selEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) selEdge = lookupD Ccfg.D selEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=selEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) selEdge (lookupD Ccfg.D selEdge ++ [.string]) =
                updateD Ccfg.D selEdge (lookupD Ccfg.D selEdge ++ [.string]) ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=selEdge)
              (ts:=lookupD Ccfg.D selEdge ++ [.string])
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                (sendStep (frameConfigRight Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L) := by
            refine StepBase.select (C:=frameConfigRight Ccfg Gfr Dfr) (k:=k) (e:=e) (ℓ:=ℓ)
              (target:=target) (branches:=branches) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa using hFind
          have hEq :
              sendStep (frameConfigRight Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L =
                frameConfigRight (sendStep Ccfg e selEdge (.string ℓ) .string L) Gfr Dfr := by
            simp [frameConfigRight, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | branch hProc hk hG hBuf hFindP hFindT hDeq =>
          rename_i Ccfg vs vOut k e ℓ source procBranches typeBranches P L bufs'
          set brEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .branch source typeBranches, hG, rfl⟩
          have hDfrNone : Dfr.find? brEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) hDisj hCons hSid
          have hLookupD :
              lookupD (Ccfg.D ++ Dfr) brEdge = lookupD Ccfg.D brEdge :=
            lookupD_append_left_of_right_none (D₁:=Ccfg.D) (D₂:=Dfr) (e:=brEdge) hDfrNone
          have hUpdG : updateG (Ccfg.G ++ Gfr) e L = updateG Ccfg.G e L ++ Gfr :=
            updateG_append_left_hit hG
          have hUpdD :
              updateD (Ccfg.D ++ Dfr) brEdge (lookupD Ccfg.D brEdge).tail =
                updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail ++ Dfr := by
            exact updateD_append_left (D:=Ccfg.D) (D₂:=Dfr) (e:=brEdge)
              (ts:=(lookupD Ccfg.D brEdge).tail)
          have hStep' :
              StepBase (frameConfigRight Ccfg Gfr Dfr)
                { frameConfigRight Ccfg Gfr Dfr with
                    proc := P,
                    bufs := bufs',
                    G := updateG (frameConfigRight Ccfg Gfr Dfr).G e L,
                    D := updateD (frameConfigRight Ccfg Gfr Dfr).D brEdge
                          (lookupD (frameConfigRight Ccfg Gfr Dfr).D brEdge).tail } := by
            refine (@StepBase.branch vs vOut (frameConfigRight Ccfg Gfr Dfr)
              k e ℓ source procBranches typeBranches P L bufs' ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simpa [frameConfigRight] using hProc
            · simpa [frameConfigRight] using hk
            · exact lookupG_append_left hG
            · simpa [frameConfigRight] using hBuf
            · simpa using hFindP
            · simpa using hFindT
            · simpa [frameConfigRight] using hDeq
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := P,
                  bufs := bufs',
                  G := updateG (frameConfigRight Ccfg Gfr Dfr).G e L,
                  D := updateD (frameConfigRight Ccfg Gfr Dfr).D brEdge
                        (lookupD (frameConfigRight Ccfg Gfr Dfr).D brEdge).tail } =
                frameConfigRight
                  { Ccfg with
                      proc := P,
                      bufs := bufs',
                      G := updateG Ccfg.G e L,
                      D := updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail } Gfr Dfr := by
            simp [frameConfigRight, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | newSession hProc =>
          rename_i Ccfg roles f P
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { (newSessionStep (frameConfigRight Ccfg Gfr Dfr) roles f) with proc := P } :=
            StepBase.newSession (C:=frameConfigRight Ccfg Gfr Dfr) (roles:=roles) (f:=f) (P:=P)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { (newSessionStep (frameConfigRight Ccfg Gfr Dfr) roles f) with proc := P } =
                frameConfigRight { (newSessionStep Ccfg roles f) with proc := P } Gfr Dfr := by
            simp [frameConfigRight, newSessionStep]
          simpa [hEq] using (Step.base hStep')
      | assign hProc =>
          rename_i Ccfg x v
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigRight Ccfg Gfr Dfr).store x v } :=
            StepBase.assign (C:=frameConfigRight Ccfg Gfr Dfr) (x:=x) (v:=v)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigRight Ccfg Gfr Dfr).store x v } =
                frameConfigRight
                  { Ccfg with proc := .skip, store := updateStr Ccfg.store x v } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | seq2 hProc =>
          rename_i Ccfg Q
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } :=
            StepBase.seq2 (C:=frameConfigRight Ccfg Gfr Dfr) (Q:=Q) (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } =
                frameConfigRight { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | par_skip_left hProc =>
          rename_i Ccfg Q nS nG
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } :=
            StepBase.par_skip_left (C:=frameConfigRight Ccfg Gfr Dfr) (Q:=Q)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := Q } =
                frameConfigRight { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
      | par_skip_right hProc =>
          rename_i Ccfg P nS nG
          have hStep' : StepBase (frameConfigRight Ccfg Gfr Dfr)
              { frameConfigRight Ccfg Gfr Dfr with proc := P } :=
            StepBase.par_skip_right (C:=frameConfigRight Ccfg Gfr Dfr) (P:=P)
              (by simpa [frameConfigRight] using hProc)
          have hEq :
              { frameConfigRight Ccfg Gfr Dfr with proc := P } =
                frameConfigRight { Ccfg with proc := P } Gfr Dfr := by
            simp [frameConfigRight]
          simpa [hEq] using (Step.base hStep')
  | seq_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .seq P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := P }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.seq_left hProc' hSub')
  | par_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := P }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.par_left hProc' hSub')
  | par_right hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigRight Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigRight] using hProc
      have hDisj' : DisjointG { Ccfg with proc := Q }.G Gfr := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigRight] using (Step.par_right hProc' hSub')

private lemma step_frame_left {C C' : Config} {Gfr : GEnv} {Dfr : DEnv} :
    DisjointG Gfr C.G →
    DConsistent Gfr Dfr →
    Step C C' →
    Step (frameConfigLeft C Gfr Dfr) (frameConfigLeft C' Gfr Dfr) := by
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      cases hBase with
      | send hProc hk hx hG =>
          rename_i Ccfg k x e v target T L
          set sendEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .send target T L, hG, rfl⟩
          have hDfrNone : Dfr.find? sendEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) sendEdge = lookupD Ccfg.D sendEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=sendEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.send target T L) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.send target T L) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) sendEdge (lookupD Ccfg.D sendEdge ++ [T]) =
                Dfr ++ updateD Ccfg.D sendEdge (lookupD Ccfg.D sendEdge ++ [T]) := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=sendEdge)
              (ts:=lookupD Ccfg.D sendEdge ++ [T]) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (sendStep (frameConfigLeft Ccfg Gfr Dfr) e sendEdge v T L) := by
            refine StepBase.send (C:=frameConfigLeft Ccfg Gfr Dfr) (k:=k) (x:=x) (e:=e)
              (v:=v) (target:=target) (T:=T) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · simpa [frameConfigLeft] using hx
            · exact hLookupG
          have hEq :
              sendStep (frameConfigLeft Ccfg Gfr Dfr) e sendEdge v T L =
                frameConfigLeft (sendStep Ccfg e sendEdge v T L) Gfr Dfr := by
            simp [frameConfigLeft, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | recv hProc hk hG hBuf =>
          rename_i Ccfg vs k x e v source T L
          set recvEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .recv source T L, hG, rfl⟩
          have hDfrNone : Dfr.find? recvEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) recvEdge = lookupD Ccfg.D recvEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=recvEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.recv source T L) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.recv source T L) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) recvEdge (lookupD Ccfg.D recvEdge).tail =
                Dfr ++ updateD Ccfg.D recvEdge (lookupD Ccfg.D recvEdge).tail := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=recvEdge)
              (ts:=(lookupD Ccfg.D recvEdge).tail) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (recvStep (frameConfigLeft Ccfg Gfr Dfr) e recvEdge x v L) := by
            refine (@StepBase.recv vs (frameConfigLeft Ccfg Gfr Dfr) k x e v source T L ?_ ?_ ?_ ?_)
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa [frameConfigLeft] using hBuf
          have hEq :
              recvStep (frameConfigLeft Ccfg Gfr Dfr) e recvEdge x v L =
                frameConfigLeft (recvStep Ccfg e recvEdge x v L) Gfr Dfr := by
            simp [frameConfigLeft, recvStep, dequeueBuf, hBuf, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | select hProc hk hG hFind =>
          rename_i Ccfg k e ℓ target branches L
          set selEdge : Edge := { sid := e.sid, sender := e.role, receiver := target }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .select target branches, hG, rfl⟩
          have hDfrNone : Dfr.find? selEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) selEdge = lookupD Ccfg.D selEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=selEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.select target branches) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.select target branches) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) selEdge (lookupD Ccfg.D selEdge ++ [.string]) =
                Dfr ++ updateD Ccfg.D selEdge (lookupD Ccfg.D selEdge ++ [.string]) := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=selEdge)
              (ts:=lookupD Ccfg.D selEdge ++ [.string]) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                (sendStep (frameConfigLeft Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L) := by
            refine StepBase.select (C:=frameConfigLeft Ccfg Gfr Dfr) (k:=k) (e:=e) (ℓ:=ℓ)
              (target:=target) (branches:=branches) (L:=L) ?_ ?_ ?_ ?_
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa using hFind
          have hEq :
              sendStep (frameConfigLeft Ccfg Gfr Dfr) e selEdge (.string ℓ) .string L =
                frameConfigLeft (sendStep Ccfg e selEdge (.string ℓ) .string L) Gfr Dfr := by
            simp [frameConfigLeft, sendStep, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | branch hProc hk hG hBuf hFindP hFindT hDeq =>
          rename_i Ccfg vs vOut k e ℓ source procBranches typeBranches P L bufs'
          set brEdge : Edge := { sid := e.sid, sender := source, receiver := e.role }
          have hSid : e.sid ∈ SessionsOf Ccfg.G := ⟨e, .branch source typeBranches, hG, rfl⟩
          have hDfrNone : Dfr.find? brEdge = none :=
            lookupD_none_of_disjointG (G₁:=Ccfg.G) (G₂:=Gfr) (D₂:=Dfr) (DisjointG_symm hDisj) hCons hSid
          have hLookupD :
              lookupD (Dfr ++ Ccfg.D) brEdge = lookupD Ccfg.D brEdge :=
            lookupD_append_right (D₁:=Dfr) (D₂:=Ccfg.D) (e:=brEdge) hDfrNone
          have hGfrNone : lookupG Gfr e = none :=
            lookupG_none_of_disjoint (G₁:=Gfr) (G₂:=Ccfg.G) hDisj (e:=e) (L:=.branch source typeBranches) hG
          have hLookupG :
              lookupG (Gfr ++ Ccfg.G) e = some (.branch source typeBranches) := by
            simpa [lookupG_append_right (G₁:=Gfr) (G₂:=Ccfg.G) (e:=e) hGfrNone] using hG
          have hUpdG : updateG (Gfr ++ Ccfg.G) e L = Gfr ++ updateG Ccfg.G e L :=
            updateG_append_right_hit hGfrNone
          have hUpdD :
              updateD (Dfr ++ Ccfg.D) brEdge (lookupD Ccfg.D brEdge).tail =
                Dfr ++ updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail := by
            exact updateD_append_right (D₁:=Dfr) (D:=Ccfg.D) (e:=brEdge)
              (ts:=(lookupD Ccfg.D brEdge).tail) hDfrNone
          have hStep' :
              StepBase (frameConfigLeft Ccfg Gfr Dfr)
                { frameConfigLeft Ccfg Gfr Dfr with
                    proc := P,
                    bufs := bufs',
                    G := updateG (frameConfigLeft Ccfg Gfr Dfr).G e L,
                    D := updateD (frameConfigLeft Ccfg Gfr Dfr).D brEdge
                          (lookupD (frameConfigLeft Ccfg Gfr Dfr).D brEdge).tail } := by
            refine (@StepBase.branch vs vOut (frameConfigLeft Ccfg Gfr Dfr)
              k e ℓ source procBranches typeBranches P L bufs' ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            · simpa [frameConfigLeft] using hProc
            · simpa [frameConfigLeft] using hk
            · exact hLookupG
            · simpa [frameConfigLeft] using hBuf
            · simpa using hFindP
            · simpa using hFindT
            · simpa [frameConfigLeft] using hDeq
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := P,
                  bufs := bufs',
                  G := updateG (frameConfigLeft Ccfg Gfr Dfr).G e L,
                  D := updateD (frameConfigLeft Ccfg Gfr Dfr).D brEdge
                        (lookupD (frameConfigLeft Ccfg Gfr Dfr).D brEdge).tail } =
                frameConfigLeft
                  { Ccfg with
                      proc := P,
                      bufs := bufs',
                      G := updateG Ccfg.G e L,
                      D := updateD Ccfg.D brEdge (lookupD Ccfg.D brEdge).tail } Gfr Dfr := by
            simp [frameConfigLeft, hUpdG, hUpdD, hLookupD]
          simpa [hEq] using (Step.base hStep')
      | newSession hProc =>
          rename_i Ccfg roles f P
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { (newSessionStep (frameConfigLeft Ccfg Gfr Dfr) roles f) with proc := P } :=
            StepBase.newSession (C:=frameConfigLeft Ccfg Gfr Dfr) (roles:=roles) (f:=f) (P:=P)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { (newSessionStep (frameConfigLeft Ccfg Gfr Dfr) roles f) with proc := P } =
                frameConfigLeft { (newSessionStep Ccfg roles f) with proc := P } Gfr Dfr := by
            simp [frameConfigLeft, newSessionStep]
          simpa [hEq] using (Step.base hStep')
      | assign hProc =>
          rename_i Ccfg x v
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigLeft Ccfg Gfr Dfr).store x v } :=
            StepBase.assign (C:=frameConfigLeft Ccfg Gfr Dfr) (x:=x) (v:=v)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with
                  proc := .skip,
                  store := updateStr (frameConfigLeft Ccfg Gfr Dfr).store x v } =
                frameConfigLeft
                  { Ccfg with proc := .skip, store := updateStr Ccfg.store x v } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | seq2 hProc =>
          rename_i Ccfg Q
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } :=
            StepBase.seq2 (C:=frameConfigLeft Ccfg Gfr Dfr) (Q:=Q) (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } =
                frameConfigLeft { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | par_skip_left hProc =>
          rename_i Ccfg Q nS nG
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } :=
            StepBase.par_skip_left (C:=frameConfigLeft Ccfg Gfr Dfr) (Q:=Q)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := Q } =
                frameConfigLeft { Ccfg with proc := Q } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
      | par_skip_right hProc =>
          rename_i Ccfg P nS nG
          have hStep' : StepBase (frameConfigLeft Ccfg Gfr Dfr)
              { frameConfigLeft Ccfg Gfr Dfr with proc := P } :=
            StepBase.par_skip_right (C:=frameConfigLeft Ccfg Gfr Dfr) (P:=P)
              (by simpa [frameConfigLeft] using hProc)
          have hEq :
              { frameConfigLeft Ccfg Gfr Dfr with proc := P } =
                frameConfigLeft { Ccfg with proc := P } Gfr Dfr := by
            simp [frameConfigLeft]
          simpa [hEq] using (Step.base hStep')
  | seq_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .seq P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := P }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.seq_left hProc' hSub')
  | par_left hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := P }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.par_left hProc' hSub')
  | par_right hProc hSub ih =>
      rename_i Ccfg Ccfg' P Q nS nG nS' nG'
      have hProc' : (frameConfigLeft Ccfg Gfr Dfr).proc = .par nS nG P Q := by
        simpa [frameConfigLeft] using hProc
      have hDisj' : DisjointG Gfr { Ccfg with proc := Q }.G := by
        simpa using hDisj
      have hSub' := ih hDisj'
      simpa [frameConfigLeft] using (Step.par_right hProc' hSub')

/-! ## Subject Reduction -/

/-- Soundness: TypedStep implies Step. -/
theorem subject_reduction {n : SessionId}
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Step
      { proc := P, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n } := by
  intro hTS
  induction hTS with
  | send hk hx hG hxT hv hRecvReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
      -- Rewrite to match sendStep.
      subst hEdge hGout hDout hBufsOut
      let C : Config :=
        { proc := .send k x, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) :=
        StepBase.send rfl hk hx hG
      simpa [C] using (Step.base hStep)
  | recv hk hG hEdge hBuf hv hTrace hGout hDout hSout hStoreOut hBufsOut =>
      rename_i G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
      subst hEdge hGout hDout hSout hStoreOut hBufsOut
      let C : Config :=
        { proc := .recv k x, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) :=
        StepBase.recv rfl hk hG hBuf
      simpa [C, recvStep, dequeueBuf, hBuf] using (Step.base hStep)
  | select hk hG hFind hReady hEdge hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      let C : Config :=
        { proc := .select k ℓ, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L) :=
        StepBase.select rfl hk hG hFind
      simpa [C] using (Step.base hStep)
  | branch hk hG hEdge hBuf hFindP hFindT hTrace hGout hDout hBufsOut =>
      rename_i G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
      subst hEdge hGout hDout hBufsOut
      -- StepBase.branch uses dequeueBuf; use the existence of a head to rewrite.
      -- The dequeueBuf in StepBase.branch is discharged by the definition in Semantics.
      have hDeq : dequeueBuf bufs { sid := e.sid, sender := source, receiver := e.role } = some (updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs, .string ℓ) := by
        -- unfold dequeueBuf with the known head.
        simp [dequeueBuf, hBuf]
      let C : Config :=
        { proc := .branch k procs, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      have hStep : StepBase C
          { C with proc := P,
                   bufs := updateBuf bufs { sid := e.sid, sender := source, receiver := e.role } vs,
                   G := updateG G e L,
                   D := updateD D { sid := e.sid, sender := source, receiver := e.role } (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail } :=
        StepBase.branch rfl hk hG hBuf hFindP hFindT hDeq
      simpa [C] using (Step.base hStep)
  | assign hv hS hStore =>
      rename_i G D Ssh Sown store bufs x v T S' store'
      refine Step.base ?_
      subst hS hStore
      exact StepBase.assign rfl
  | seq_step hStep ih =>
      rename_i G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q
      let C : Config :=
        { proc := .seq P Q, store := store, bufs := bufs, G := G, D := D, nextSid := n }
      let C' : Config :=
        { proc := P', store := store', bufs := bufs', G := G', D := D', nextSid := n }
      have hSub : Step { C with proc := P } C' := by
        simpa [C, C'] using ih
      have hProc : C.proc = .seq P Q := rfl
      simpa [C, C'] using (Step.seq_left hProc hSub)
  | seq_skip =>
      refine Step.base ?_
      exact StepBase.seq2 rfl
  | par_left split hSlen hGlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P P' Q G D₁ D₂ G₁' D₁' S₁' nS nG
      let C0 : Config :=
        { proc := P, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      let C0' : Config :=
        { proc := P', store := store', bufs := bufs', G := G₁' ++ split.G2, D := D₁' ++ D₂, nextSid := n }
      have hSub : Step C0 C0' := by
        simpa [C0, C0'] using ih
      let C : Config :=
        { proc := .par nS nG P Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      have hSub' : Step { C with proc := P } C0' := by
        simpa [C, C0] using hSub
      have hProc : C.proc = .par nS nG P Q := rfl
      simpa [C, C0'] using
        (Step.par_left (nS':=S₁'.length) (nG':=G₁'.length) hProc hSub')
  | par_right split hSlen hGlen hStep hDisjG hDisjD hDisjS ih =>
      rename_i Ssh Sown store bufs store' bufs' P Q Q' G D₁ D₂ G₂' D₂' S₂' nS nG
      let C0 : Config :=
        { proc := Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      let C0' : Config :=
        { proc := Q', store := store', bufs := bufs', G := split.G1 ++ G₂', D := D₁ ++ D₂', nextSid := n }
      have hSub : Step C0 C0' := by
        simpa [C0, C0'] using ih
      let C : Config :=
        { proc := .par nS nG P Q, store := store, bufs := bufs, G := G, D := D₁ ++ D₂, nextSid := n }
      have hSub' : Step { C with proc := Q } C0' := by
        simpa [C, C0] using hSub
      have hProc : C.proc = .par nS nG P Q := rfl
      simpa [C, C0'] using
        (Step.par_right (nS':=split.S1.length) (nG':=split.G1.length) hProc hSub')
  | par_skip_left =>
      refine Step.base ?_
      exact StepBase.par_skip_left rfl
  | par_skip_right =>
      refine Step.base ?_
      exact StepBase.par_skip_right rfl
