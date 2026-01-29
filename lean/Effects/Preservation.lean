import Effects.Semantics
import Effects.Typing

/-!
# MPST Preservation Theorem

This module contains the preservation (subject reduction) theorem for MPST:
if a well-typed configuration takes a step, the result is also well-typed.

**UPDATE (2026-01-15)**: This module now imports Effects.Typing which defines
TypedStep - the linear resource transition typing judgment that resolves the
design issues that blocked the original preservation theorems below.

The new preservation theorems are:
- `preservation_typed` (in Typing.lean) - TypedStep preserves WellFormed
- `progress_typed` (in Typing.lean) - WellFormed processes can step or terminate
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

- `preservation` (this file): TypedStep preserves WellFormed (wrapper)
- `progress` (this file): WellFormed processes can step or are blocked (wrapper)
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

noncomputable section

/-! ## Compatibility Aliases -/

/-- Backwards-compatible single-env pre-typing. -/
abbrev HasTypeProcPre1 (S : SEnv) (G : GEnv) (P : Process) : Prop :=
  HasTypeProcPre S ∅ G P

/-! ## Helper Lemmas -/

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

/-! ## Main Preservation Theorem -/

/-- Preservation: TypedStep preserves WellFormed. -/
theorem preservation
    {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    (hTS : TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P') →
    WellFormed G D Ssh Sown store bufs P →
    WellFormed G' D' Ssh Sown' store' bufs' P' := by
  -- Delegate to the canonical proof in Typing.Part6.
  exact preservation_typed

/-! ## Progress Theorem -/

/-- Progress: a well-formed process can step or is blocked. -/
theorem progress {G D Ssh Sown store bufs P} :
    WellFormed G D Ssh Sown store bufs P →
    (P = .skip) ∨
      (∃ G' D' Sown' store' bufs' P', TypedStep G D Ssh Sown store bufs P
        G' D' Sown' store' bufs' P') ∨
      BlockedProc store bufs P := by
  -- Delegate to the canonical progress proof in Typing.Part7.
  exact progress_typed

/-! ## Progress Lemmas for Individual Process Forms

These lemmas prove progress for specific process forms using pre-update typing.
They form the building blocks for the full progress theorem.
Reference: `work/effects/008.lean:323-376, 487-516` -/

/-- Blocked recv predicate: recv is waiting on an empty buffer.
    Reference: `work/effects/008.lean:259-269` -/
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

/-- Progress for send: send always steps (it just enqueues to buffer).
    Reference: `work/effects/008.lean:323-336` -/
theorem progress_send {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .send k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.send k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  -- 1. Inversion: extract (e, q, T, L) from typing
  obtain ⟨e, q, T, L, hSk, hGe, hSx⟩ := inversion_send hProc
  -- 2. Bridge: get channel value vk from store
  obtain ⟨vk, hvk1, hvk2⟩ := store_lookup_of_senv_lookup hStore hSk
  -- 3. Bridge: get payload value v from store
  obtain ⟨v, hv1, _hv2⟩ := store_lookup_of_senv_lookup hStore hSx
  -- 4. Inversion: channel value must be .chan e
  have hChanEq := HasTypeVal_chan_inv hvk2
  subst hChanEq
  -- 5. Construct step witness
  use sendStep C e ⟨e.sid, e.role, q⟩ v T L
  apply Step.base
  apply StepBase.send hEq hvk1 hv1 hGe

/-- Progress for recv: recv steps if buffer non-empty, otherwise blocked.
    Reference: `work/effects/008.lean:341-357` -/
theorem progress_recv {C : Config} {Ssh Sown : SEnv} {k x : Var}
    (hEq : C.proc = .recv k x)
    (hProc : HasTypeProcPre Ssh Sown C.G (.recv k x))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  -- 1. Inversion: extract (e, p, T, L) from typing
  obtain ⟨e, p, T, L, hSk, hGe, _hxNone⟩ := inversion_recv hProc
  -- 2. Bridge: get channel value vk from store
  obtain ⟨vk, hvk1, hvk2⟩ := store_lookup_of_senv_lookup hStore hSk
  -- 3. Inversion: channel value must be .chan e
  have hChanEq := HasTypeVal_chan_inv hvk2
  subst hChanEq
  -- 4. Case split on buffer contents
  cases hBuf : lookupBuf C.bufs ⟨e.sid, p, e.role⟩ with
  | nil =>
    -- Empty buffer → BlockedRecv
    right
    left
    exact ⟨k, x, p, T, L, e, hEq, hvk1, hGe, hBuf⟩
  | cons v vs =>
    -- Non-empty buffer → Step
    left
    use recvStep C e ⟨e.sid, p, e.role⟩ x v L
    apply Step.base
    apply StepBase.recv hEq hvk1 hGe hBuf

/-- Progress for select: select always steps (it just enqueues label to buffer).
    Reference: `work/effects/008.lean:362-376, 500-516` -/
theorem progress_select {C : Config} {Ssh Sown : SEnv} {k : Var} {l : Label}
    (hEq : C.proc = .select k l)
    (hProc : HasTypeProcPre Ssh Sown C.G (.select k l))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store) :
    ∃ C', Step C C' := by
  -- 1. Inversion: extract (e, q, bs, L) from typing
  obtain ⟨e, q, bs, L, hSk, hGe, hFind⟩ := inversion_select hProc
  -- 2. Bridge: get channel value vk from store
  obtain ⟨vk, hvk1, hvk2⟩ := store_lookup_of_senv_lookup hStore hSk
  -- 3. Inversion: channel value must be .chan e
  have hChanEq := HasTypeVal_chan_inv hvk2
  subst hChanEq
  -- 4. Construct step witness (select uses sendStep with string label)
  use sendStep C e ⟨e.sid, e.role, q⟩ (.string l) .string L
  apply Step.base
  apply StepBase.select hEq hvk1 hGe hFind

/-- Progress for branch: branch steps if buffer non-empty, otherwise blocked.
    This requires ValidLabels to ensure the received label is valid. -/
private theorem findLabel_eq {α : Type} {lbl lbl' : Label} {xs : List (Label × α)} {v : α}
    (h : xs.find? (fun b => b.1 == lbl) = some (lbl', v)) : lbl' = lbl := by
  have hPred : (lbl' == lbl) := (List.find?_eq_some_iff_append (xs := xs)
    (p := fun b => b.1 == lbl) (b := (lbl', v))).1 h |>.1
  have hPred' : (lbl' == lbl) = true := by
    simpa using hPred
  exact (beq_iff_eq).1 hPred'

theorem progress_branch {C : Config} {Ssh Sown : SEnv} {k : Var} {procs : List (Label × Process)}
    (hEq : C.proc = .branch k procs)
    (hProc : HasTypeProcPre Ssh Sown C.G (.branch k procs))
    (hStore : StoreTypedStrong C.G (SEnvAll Ssh Sown) C.store)
    (hBufs : BuffersTyped C.G C.D C.bufs)
    (hHead : HeadCoherent C.G C.D)
    (hValid : ValidLabels C.G C.D C.bufs) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  -- 1. Inversion: extract (e, p, bs) from typing
  obtain ⟨e, p, bs, hSk, hGe, hLen, hLabels, _hBodies⟩ := inversion_branch hProc
  -- 2. Bridge: get channel value vk from store
  obtain ⟨vk, hvk1, hvk2⟩ := store_lookup_of_senv_lookup hStore hSk
  -- 3. Inversion: channel value must be .chan e
  have hChanEq := HasTypeVal_chan_inv hvk2
  subst hChanEq
  -- 4. Case split on buffer contents
  cases hBuf : lookupBuf C.bufs ⟨e.sid, p, e.role⟩ with
  | nil =>
    -- Empty buffer → BlockedRecv
    right
    right
    exact ⟨k, procs, p, bs, e, hEq, hvk1, hGe, hBuf⟩
  | cons v vs =>
    left
    let branchEdge : Edge := ⟨e.sid, p, e.role⟩
    have hTypedEdge := hBufs branchEdge
    rcases hTypedEdge with ⟨hLenBuf, hTyping⟩
    have h0buf : 0 < (lookupBuf C.bufs branchEdge).length := by
      simp [branchEdge, hBuf]
    have h0trace : 0 < (lookupD C.D branchEdge).length := by
      exact (by simpa [hLenBuf] using h0buf)
    have hTyped0 := hTyping 0 h0buf
    have hv' : HasTypeVal C.G v ((lookupD C.D branchEdge).get ⟨0, h0trace⟩) := by
      simpa [branchEdge, hBuf] using hTyped0
    cases hTrace : lookupD C.D branchEdge with
    | nil =>
        simp [hTrace] at h0trace
    | cons T' ts =>
        have hHeadEdge := hHead branchEdge
        have hEqT : T' = .string := by
          simpa [HeadCoherent, hGe, branchEdge, hTrace] using hHeadEdge
        have hv : HasTypeVal C.G v .string := by
          simpa [hTrace, hEqT] using hv'
        cases v with
        | string lbl0 =>
            have hValidEdge := hValid branchEdge p bs (by simpa [branchEdge] using hGe)
            have hBsSome : (bs.find? (fun b => b.1 == lbl0)).isSome := by
              simpa [branchEdge, hBuf] using hValidEdge
            rcases (Option.isSome_iff_exists).1 hBsSome with ⟨b, hFindBs⟩
            cases b with
            | mk lbl' L =>
                have hLbl' : lbl' = lbl0 := findLabel_eq (xs := bs) (lbl := lbl0) (lbl' := lbl') (v := L) hFindBs
                subst lbl'
                have hMemBs : (lbl0, L) ∈ bs := List.mem_of_find?_eq_some hFindBs
                rcases (List.mem_iff_getElem).1 hMemBs with ⟨i, hi, hGetBs⟩
                have hip : i < procs.length := by
                  simpa [hLen] using hi
                have hLabelAt : (procs.get ⟨i, hip⟩).1 = lbl0 := by
                  have hLblEq := hLabels i hi hip
                  simpa [hGetBs] using hLblEq
                have hPred : (fun b => b.1 == lbl0) (procs.get ⟨i, hip⟩) := by
                  simpa using (beq_iff_eq).2 hLabelAt
                have hFindPIsSome : (procs.find? (fun b => b.1 == lbl0)).isSome := by
                  cases hFindP : procs.find? (fun b => b.1 == lbl0) with
                  | none =>
                      have hNo : ∀ x ∈ procs, ¬ (fun b => b.1 == lbl0) x := by
                        simpa [List.find?_eq_none] using hFindP
                      have hMemP : procs.get ⟨i, hip⟩ ∈ procs := List.get_mem procs ⟨i, hip⟩
                      exact ((hNo _ hMemP) hPred).elim
                  | some b =>
                      simp
                rcases (Option.isSome_iff_exists).1 hFindPIsSome with ⟨bP, hFindP⟩
                cases bP with
                | mk lblP P =>
                    have hLblP : lblP = lbl0 := findLabel_eq (xs := procs) (lbl := lbl0) (lbl' := lblP) (v := P) hFindP
                    subst lblP
                    have hDq : dequeueBuf C.bufs branchEdge = some (updateBuf C.bufs branchEdge vs, .string lbl0) := by
                      simp [branchEdge, dequeueBuf, hBuf]
                    let C' : Config :=
                      { C with proc := P, bufs := updateBuf C.bufs branchEdge vs,
                               G := updateG C.G e L, D := updateD C.D branchEdge (lookupD C.D branchEdge).tail }
                    refine ⟨C', ?_⟩
                    apply Step.base
                    have hBuf' : lookupBuf C.bufs branchEdge = .string lbl0 :: vs := by
                      simpa [branchEdge] using hBuf
                    apply StepBase.branch (C:=C) (k:=k) (e:=e) (ℓ:=lbl0)
                      (source:=p) (procBranches:=procs) (typeBranches:=bs)
                      (P:=P) (L:=L) (bufs':=updateBuf C.bufs branchEdge vs) <;> try rfl
                    · exact hEq
                    · exact hvk1
                    · exact hGe
                    · simpa [branchEdge] using hBuf'
                    · exact hFindP
                    · exact hFindBs
                    · simpa [branchEdge] using hDq
        | _ =>
            cases hv

/-! ## Subject Reduction (TypedStep Soundness)

This section proves that TypedStep implies Step - i.e., that the typed
transition judgment is sound with respect to the untyped operational semantics.

This bridges the TypedStep-based preservation theorem (preservation_typed in Typing.lean)
with the untyped Step relation defined in Semantics.lean. -/

/-- Frame extra G/D resources on the right of a configuration. -/
def frameGD (C : Config) (G₂ : GEnv) (D₂ : DEnv) : Config :=
  { C with G := C.G ++ G₂, D := C.D ++ D₂ }

def frameGD_left (C : Config) (G₁ : GEnv) (D₁ : DEnv) : Config :=
  { C with G := G₁ ++ C.G, D := D₁ ++ C.D }

/-! ### DEnv Framing Helpers -/

/-- Updated edge: both sides read the new trace. -/
private theorem updateD_append_left_hit {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (h : D₁.find? e = none) :
    lookupD (updateD (D₁ ++ D₂) e ts) e = lookupD (D₁ ++ updateD D₂ e ts) e := by
  -- Reduce both sides to the update result `ts`.
  have hLeft : lookupD (updateD (D₁ ++ D₂) e ts) e = ts := by
    simpa using (lookupD_update_eq (env:=D₁ ++ D₂) (e:=e) (ts:=ts))
  have hAppend := lookupD_append_right (D₁:=D₁) (D₂:=updateD D₂ e ts) (e:=e) h
  have hRight : lookupD (D₁ ++ updateD D₂ e ts) e = ts := by
    simpa [hAppend] using (lookupD_update_eq (env:=D₂) (e:=e) (ts:=ts))
  simpa [hLeft, hRight]

/-- Non-updated edge present on the left: append preserves the left entry. -/
private theorem updateD_append_left_left
    {D₁ D₂ : DEnv} {e e' : Edge} {ts ts' : List ValType}
    (h : D₁.find? e = none) (hFind : D₁.find? e' = some ts') (hNe : e' ≠ e) :
    lookupD (updateD (D₁ ++ D₂) e ts) e' =
      lookupD (D₁ ++ updateD D₂ e ts) e' := by
  -- Push the left entry through both appends.
  have hLeftFind := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e') (ts:=ts') hFind
  have hRightFind := findD_append_left (D₁:=D₁) (D₂:=updateD D₂ e ts) (e:=e') (ts:=ts') hFind
  have hLeft : lookupD (D₁ ++ D₂) e' = ts' := by
    simp [lookupD, hLeftFind]
  have hRight : lookupD (D₁ ++ updateD D₂ e ts) e' = ts' := by
    simp [lookupD, hRightFind]
  have hUpd := lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=e') (ts:=ts) (Ne.symm hNe)
  simpa [hUpd, hLeft, hRight]

/-- Non-updated edge absent on the left: append reduces to the right map. -/
private theorem updateD_append_left_right
    {D₁ D₂ : DEnv} {e e' : Edge} {ts : List ValType}
    (h : D₁.find? e = none) (hFind : D₁.find? e' = none) (hNe : e' ≠ e) :
    lookupD (updateD (D₁ ++ D₂) e ts) e' =
      lookupD (D₁ ++ updateD D₂ e ts) e' := by
  -- Compare right lookups; update does not affect `e'`.
  have hLeft := lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e') hFind
  have hRight := lookupD_append_right (D₁:=D₁) (D₂:=updateD D₂ e ts) (e:=e') hFind
  have hUpd := lookupD_update_neq (env:=D₂) (e:=e) (e':=e') (ts:=ts) (Ne.symm hNe)
  have hUpd' : lookupD (updateD D₂ e ts) e' = lookupD D₂ e' := by
    simpa using hUpd
  have hLeftUpd : lookupD (updateD (D₁ ++ D₂) e ts) e' = lookupD (D₁ ++ D₂) e' := by
    simpa using (lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=e') (ts:=ts) (Ne.symm hNe))
  simpa [hLeft, hRight, hUpd', hLeftUpd]

/-- Lookup-level framing for updateD across a left-biased append. -/
private theorem updateD_append_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (h : D₁.find? e = none) :
    ∀ e', lookupD (updateD (D₁ ++ D₂) e ts) e' =
      lookupD (D₁ ++ updateD D₂ e ts) e' := by
  intro e'
  -- Split on the updated edge vs other edges.
  by_cases hEq : e' = e
  · subst hEq
    exact updateD_append_left_hit (D₁:=D₁) (D₂:=D₂) (e:=e) (ts:=ts) h
  · cases hFind : D₁.find? e' with
    | some ts' =>
        exact updateD_append_left_left (D₁:=D₁) (D₂:=D₂) (e:=e) (e':=e')
          (ts:=ts) (ts':=ts') h hFind hEq
    | none =>
        exact updateD_append_left_right (D₁:=D₁) (D₂:=D₂) (e:=e) (e':=e')
          (ts:=ts) h hFind hEq

/-- find? is unchanged by update on a different edge. -/
private theorem findD_update_neq {D : DEnv} {e e' : Edge} {ts : List ValType} (hNe : e' ≠ e) :
    (updateD D e ts).find? e' = D.find? e' := by
  simp [updateD, DEnv.find?, hNe]

/-- Updated edge: right map has no entry, so append reads the left update. -/
private theorem updateD_append_left_env_hit {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (hRight : D₂.find? e = none) :
    lookupD (updateD (D₁ ++ D₂) e ts) e =
      lookupD (updateD D₁ e ts ++ D₂) e := by
  -- Both sides reduce to the updated trace.
  have hLeft : lookupD (updateD (D₁ ++ D₂) e ts) e = ts := by
    simpa using (lookupD_update_eq (env:=D₁ ++ D₂) (e:=e) (ts:=ts))
  have hUpd : lookupD (updateD D₁ e ts) e = ts := by
    simpa using (lookupD_update_eq (env:=D₁) (e:=e) (ts:=ts))
  have hRight : lookupD (updateD D₁ e ts ++ D₂) e = ts := by
    have hApp :=
      lookupD_append_left_of_right_none (D₁:=updateD D₁ e ts) (D₂:=D₂) (e:=e) hRight
    simpa [hUpd] using hApp
  simpa [hLeft, hRight]

/-- Other edge present on the left: append preserves the left entry. -/
private theorem updateD_append_left_env_left
    {D₁ D₂ : DEnv} {e e' : Edge} {ts ts' : List ValType}
    (hNe : e' ≠ e) (hFind : D₁.find? e' = some ts') :
    lookupD (updateD (D₁ ++ D₂) e ts) e' =
      lookupD (updateD D₁ e ts ++ D₂) e' := by
  -- Keep the left entry on both sides; update touches only e.
  have hLeftUpd : lookupD (updateD (D₁ ++ D₂) e ts) e' = lookupD (D₁ ++ D₂) e' := by
    simpa using (lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=e') (ts:=ts) (Ne.symm hNe))
  have hLeft : lookupD (D₁ ++ D₂) e' = ts' := by
    have hFind' := findD_append_left (D₁:=D₁) (D₂:=D₂) (e:=e') (ts:=ts') hFind
    simp [lookupD, hFind']
  have hFindUpd : (updateD D₁ e ts).find? e' = some ts' := by
    simpa [findD_update_neq (D:=D₁) (e:=e) (e':=e') (ts:=ts) hNe] using hFind
  have hRight : lookupD (updateD D₁ e ts ++ D₂) e' = ts' := by
    have hFind' :=
      findD_append_left (D₁:=updateD D₁ e ts) (D₂:=D₂) (e:=e') (ts:=ts') hFindUpd
    simp [lookupD, hFind']
  simpa [hLeftUpd, hLeft, hRight]

/-- Other edge absent on the left: append reduces to the right map. -/
private theorem updateD_append_left_env_right
    {D₁ D₂ : DEnv} {e e' : Edge} {ts : List ValType}
    (hNe : e' ≠ e) (hFind : D₁.find? e' = none) :
    lookupD (updateD (D₁ ++ D₂) e ts) e' =
      lookupD (updateD D₁ e ts ++ D₂) e' := by
  -- Reduce both sides to the right lookup.
  have hLeftUpd : lookupD (updateD (D₁ ++ D₂) e ts) e' = lookupD (D₁ ++ D₂) e' := by
    simpa using (lookupD_update_neq (env:=D₁ ++ D₂) (e:=e) (e':=e') (ts:=ts) (Ne.symm hNe))
  have hLeft : lookupD (D₁ ++ D₂) e' = lookupD D₂ e' :=
    lookupD_append_right (D₁:=D₁) (D₂:=D₂) (e:=e') hFind
  have hFindUpd : (updateD D₁ e ts).find? e' = none := by
    simpa [findD_update_neq (D:=D₁) (e:=e) (e':=e') (ts:=ts) hNe] using hFind
  have hRight : lookupD (updateD D₁ e ts ++ D₂) e' = lookupD D₂ e' :=
    lookupD_append_right (D₁:=updateD D₁ e ts) (D₂:=D₂) (e:=e') hFindUpd
  simpa [hLeftUpd, hLeft, hRight]

/-- DEnv update commutes with append when the right map has no entry for the key. -/
private theorem updateD_append_left_env {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (hRight : D₂.find? e = none) :
    updateD (D₁ ++ D₂) e ts = updateD D₁ e ts ++ D₂ := by
  apply DEnv_ext
  intro e'
  by_cases hEq : e' = e
  · subst hEq
    simp [updateD, DEnvUnion, DEnv.find?, hRight]
  · cases hFind : D₁.find? e' with
    | some ts' =>
        simp [updateD, DEnvUnion, DEnv.find?, hEq, hFind]
    | none =>
        simp [updateD, DEnvUnion, DEnv.find?, hEq, hFind]

/-- DEnv update commutes with append when the left map has no entry for the key. -/
private theorem updateD_append_right_env {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (hLeft : D₁.find? e = none) :
    updateD (D₁ ++ D₂) e ts = D₁ ++ updateD D₂ e ts := by
  apply DEnv_ext
  intro e'
  by_cases hEq : e' = e
  · subst hEq
    simp [updateD, DEnvUnion, DEnv.find?, hLeft]
  · cases hFind : D₁.find? e' with
    | some ts' =>
        simp [updateD, DEnvUnion, DEnv.find?, hEq, hFind]
    | none =>
        simp [updateD, DEnvUnion, DEnv.find?, hEq, hFind]

/-- Framing commutes with sendStep when the right DEnv has no entry for the edge. -/
private theorem frameGD_sendStep {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {ep : Endpoint} {edge : Edge} {v : Value} {T : ValType} {L Lold : LocalType}
    (hLookup : lookupG C.G ep = some Lold) (hRight : D₂.find? edge = none) :
    frameGD (sendStep C ep edge v T L) G₂ D₂ =
      sendStep (frameGD C G₂ D₂) ep edge v T L := by
  -- Push G/D updates through the frame.
  ext <;> simp [frameGD, sendStep, updateG_append_left_hit hLookup,
    updateD_append_left_env hRight, lookupD_append_left_of_right_none hRight]

/-- Framing commutes with recvStep when the right DEnv has no entry for the edge. -/
private theorem frameGD_recvStep {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {ep : Endpoint} {edge : Edge} {x : Var} {v : Value} {L Lold : LocalType}
    (hLookup : lookupG C.G ep = some Lold) (hRight : D₂.find? edge = none) :
    frameGD (recvStep C ep edge x v L) G₂ D₂ =
      recvStep (frameGD C G₂ D₂) ep edge x v L := by
  -- Split on dequeueBuf to keep both recvStep branches aligned.
  cases hDeq : dequeueBuf C.bufs edge <;>
    ext <;> simp [frameGD, recvStep, hDeq, updateG_append_left_hit hLookup,
      updateD_append_left_env hRight, lookupD_append_left_of_right_none hRight]

/-- Framing on the left commutes with sendStep when the left env has no entry. -/
private theorem frameGD_left_sendStep {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {ep : Endpoint} {edge : Edge} {v : Value} {T : ValType} {L Lold : LocalType}
    (hLookup : lookupG C.G ep = some Lold) (hNone : lookupG G₁ ep = none)
    (hLeft : D₁.find? edge = none) :
    frameGD_left (sendStep C ep edge v T L) G₁ D₁ =
      sendStep (frameGD_left C G₁ D₁) ep edge v T L := by
  -- Move the updates into the right component of the append.
  ext <;> simp [frameGD_left, sendStep, updateG_append_left hNone,
    updateD_append_right_env hLeft, lookupD_append_right hLeft]

/-- Framing on the left commutes with recvStep when the left env has no entry. -/
private theorem frameGD_left_recvStep {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {ep : Endpoint} {edge : Edge} {x : Var} {v : Value} {L Lold : LocalType}
    (hLookup : lookupG C.G ep = some Lold) (hNone : lookupG G₁ ep = none)
    (hLeft : D₁.find? edge = none) :
    frameGD_left (recvStep C ep edge x v L) G₁ D₁ =
      recvStep (frameGD_left C G₁ D₁) ep edge x v L := by
  -- Split on dequeueBuf to align both recvStep branches.
  cases hDeq : dequeueBuf C.bufs edge <;>
    ext <;> simp [frameGD_left, recvStep, hDeq, updateG_append_left hNone,
      updateD_append_right_env hLeft, lookupD_append_right hLeft]

/-- Disjointness yields no right D entry for a left-typed session. -/
private theorem DEnv_find_none_of_left_lookup
    {G₁ G₂ : GEnv} {D₂ : DEnv} {ep : Endpoint} {edge : Edge} {L : LocalType}
    (hDisj : DisjointG G₁ G₂) (hCons : DConsistent G₂ D₂)
    (hLookup : lookupG G₁ ep = some L) (hSid : edge.sid = ep.sid) :
    D₂.find? edge = none := by
  -- Use disjoint session IDs to rule out right entries.
  have hIn : edge.sid ∈ SessionsOf G₁ := by
    subst hSid
    exact ⟨ep, L, hLookup, rfl⟩
  exact lookupD_none_of_disjointG (G₁:=G₁) (G₂:=G₂) (D₂:=D₂) hDisj hCons hIn

/-- DisjointG: endpoints from the right are absent on the left. -/
private theorem lookupG_none_of_disjoint_left {G₁ G₂ : GEnv} (hDisj : DisjointG G₁ G₂)
    {ep : Endpoint} {L : LocalType} (hLookup : lookupG G₂ ep = some L) :
    lookupG G₁ ep = none := by
  -- Use session-id disjointness to rule out a left lookup.
  by_cases hNone : lookupG G₁ ep = none
  · exact hNone
  · cases hSome : lookupG G₁ ep with
    | none => exact (hNone hSome).elim
    | some L₁ =>
        have hSid₁ : ep.sid ∈ SessionsOf G₁ := ⟨ep, L₁, hSome, rfl⟩
        have hSid₂ : ep.sid ∈ SessionsOf G₂ := ⟨ep, L, hLookup, rfl⟩
        have hInter : ep.sid ∈ SessionsOf G₁ ∩ SessionsOf G₂ := ⟨hSid₁, hSid₂⟩
        have hEmpty : SessionsOf G₁ ∩ SessionsOf G₂ = ∅ := hDisj
        have : ep.sid ∈ (∅ : Set SessionId) := by
          simpa [hEmpty] using hInter
        exact this.elim

/-- Send base step under right framing. -/
private theorem StepBase_frame_right_send {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {k x : Var} {e : Endpoint} {v : Value} {target : Role} {T : ValType} {L : LocalType}
    (hDisj : DisjointG C.G G₂) (hCons : DConsistent G₂ D₂)
    (hProc : C.proc = .send k x) (hK : lookupStr C.store k = some (.chan e))
    (hX : lookupStr C.store x = some v) (hG : lookupG C.G e = some (.send target T L)) :
    StepBase (frameGD C G₂ D₂)
      (frameGD (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) G₂ D₂) := by
  -- Build the framed send step and rewrite the result.
  let edge : Edge := { sid := e.sid, sender := e.role, receiver := target }
  have hD2 : D₂.find? edge = none :=
    DEnv_find_none_of_left_lookup (G₁:=C.G) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (L:=.send target T L) hDisj hCons hG rfl
  have hStep : StepBase (frameGD C G₂ D₂) (sendStep (frameGD C G₂ D₂) e edge v T L) := by
    apply StepBase.send <;> try simpa [frameGD] using hProc
    · simpa [frameGD] using hK
    · simpa [frameGD] using hX
    · simpa [frameGD] using (lookupG_append_left (G₁:=C.G) (G₂:=G₂) (e:=e) (L:=.send target T L) hG)
  have hFrame : sendStep (frameGD C G₂ D₂) e edge v T L =
      frameGD (sendStep C e edge v T L) G₂ D₂ := by
    simpa [edge] using (frameGD_sendStep (C:=C) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (v:=v) (T:=T) (L:=L) (Lold:=.send target T L) hG hD2).symm
  simpa [edge, hFrame] using hStep

/-- Recv base step under right framing. -/
private theorem StepBase_frame_right_recv {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {k x : Var} {e : Endpoint} {v : Value} {vs : List Value}
    {source : Role} {T : ValType} {L : LocalType}
    (hDisj : DisjointG C.G G₂) (hCons : DConsistent G₂ D₂)
    (hProc : C.proc = .recv k x) (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.recv source T L))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs) :
    StepBase (frameGD C G₂ D₂)
      (frameGD (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) G₂ D₂) := by
  -- Build the framed recv step and rewrite the result.
  let edge : Edge := { sid := e.sid, sender := source, receiver := e.role }
  have hD2 : D₂.find? edge = none :=
    DEnv_find_none_of_left_lookup (G₁:=C.G) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (L:=.recv source T L) hDisj hCons hG rfl
  have hStep : StepBase (frameGD C G₂ D₂) (recvStep (frameGD C G₂ D₂) e edge x v L) := by
    apply StepBase.recv <;> try simpa [frameGD] using hProc
    · simpa [frameGD] using hK
    · simpa [frameGD] using (lookupG_append_left (G₁:=C.G) (G₂:=G₂) (e:=e) (L:=.recv source T L) hG)
    · simpa [frameGD, edge] using hBuf
  have hFrame : recvStep (frameGD C G₂ D₂) e edge x v L =
      frameGD (recvStep C e edge x v L) G₂ D₂ := by
    simpa [edge] using (frameGD_recvStep (C:=C) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (x:=x) (v:=v) (L:=L) (Lold:=.recv source T L) hG hD2).symm
  simpa [edge, hFrame] using hStep

/-- Select base step under right framing. -/
private theorem StepBase_frame_right_select {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {k : Var} {e : Endpoint} {ℓ : String} {target : Role} {branches : List (String × LocalType)}
    {L : LocalType} (hDisj : DisjointG C.G G₂) (hCons : DConsistent G₂ D₂)
    (hProc : C.proc = .select k ℓ) (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.select target branches))
    (hFind : branches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    StepBase (frameGD C G₂ D₂)
      (frameGD (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L) G₂ D₂) := by
  -- Build the framed select step via sendStep.
  let edge : Edge := { sid := e.sid, sender := e.role, receiver := target }
  have hD2 : D₂.find? edge = none :=
    DEnv_find_none_of_left_lookup (G₁:=C.G) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (L:=.select target branches) hDisj hCons hG rfl
  have hStep : StepBase (frameGD C G₂ D₂)
      (sendStep (frameGD C G₂ D₂) e edge (.string ℓ) .string L) := by
    apply StepBase.select <;> try simpa [frameGD] using hProc
    · simpa [frameGD] using hK
    · simpa [frameGD] using (lookupG_append_left (G₁:=C.G) (G₂:=G₂) (e:=e) (L:=.select target branches) hG)
    · exact hFind
  have hFrame : sendStep (frameGD C G₂ D₂) e edge (.string ℓ) .string L =
      frameGD (sendStep C e edge (.string ℓ) .string L) G₂ D₂ := by
    simpa [edge] using (frameGD_sendStep (C:=C) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:=edge) (v:=.string ℓ) (T:=.string) (L:=L)
      (Lold:=.select target branches) hG hD2).symm
  simpa [edge, hFrame] using hStep

/-- Helper: construct the framed branch step on the right. -/
private theorem StepBase_frame_right_branch_step {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {k : Var} {e : Endpoint} {source : Role}
    {procBranches : List (String × Process)} {typeBranches : List (String × LocalType)}
    {ℓ : String} {P : Process} {L : LocalType} {vs : List Value} {bufs' : Buffers}
    (hProc : C.proc = .branch k procBranches)
    (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: vs)
    (hFindP : procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P))
    (hFindT : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', .string ℓ)) :
    StepBase (frameGD C G₂ D₂)
      { frameGD C G₂ D₂ with proc := P, bufs := bufs', G := updateG (C.G ++ G₂) e L,
        D := updateD (C.D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (C.D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail } := by
  -- Apply the branch rule to the framed configuration.
  apply StepBase.branch <;> try simpa [frameGD] using hProc
  · simpa [frameGD] using hK
  · simpa [frameGD] using (lookupG_append_left (G₁:=C.G) (G₂:=G₂) (e:=e) (L:=.branch source typeBranches) hG)
  · simpa [frameGD] using hBuf
  · exact hFindP
  · exact hFindT
  · simpa [frameGD] using hDeq

/-- Helper: rewrite the framed branch result on the right. -/
private theorem frameGD_branch_right_eq {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {e : Endpoint} {source : Role} {P : Process} {L : LocalType} {bufs' : Buffers}
    {typeBranches : List (String × LocalType)}
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hD2 : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none) :
    { frameGD C G₂ D₂ with proc := P, bufs := bufs', G := updateG (C.G ++ G₂) e L,
      D := updateD (C.D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }
        (lookupD (C.D ++ D₂) { sid := e.sid, sender := source, receiver := e.role }).tail } =
    frameGD { C with proc := P, bufs := bufs', G := updateG C.G e L,
      D := updateD C.D { sid := e.sid, sender := source, receiver := e.role }
        (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail } G₂ D₂ := by
  -- Push updateG/updateD through the frame.
  ext <;> simp [frameGD, updateG_append_left_hit hG,
    updateD_append_left_env hD2, lookupD_append_left_of_right_none hD2]

/-- Branch base step under right framing. -/
private theorem StepBase_frame_right_branch {C : Config} {G₂ : GEnv} {D₂ : DEnv}
    {k : Var} {e : Endpoint} {source : Role}
    {procBranches : List (String × Process)} {typeBranches : List (String × LocalType)}
    {ℓ : String} {P : Process} {L : LocalType} {vs : List Value} {bufs' : Buffers}
    (hDisj : DisjointG C.G G₂) (hCons : DConsistent G₂ D₂)
    (hProc : C.proc = .branch k procBranches)
    (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: vs)
    (hFindP : procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P))
    (hFindT : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', .string ℓ)) :
    StepBase (frameGD C G₂ D₂)
      (frameGD { C with proc := P, bufs := bufs', G := updateG C.G e L,
        D := updateD C.D { sid := e.sid, sender := source, receiver := e.role }
          (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail } G₂ D₂) := by
  -- Combine the framed branch step with the frame rewrite.
  have hD2 : D₂.find? { sid := e.sid, sender := source, receiver := e.role } = none :=
    DEnv_find_none_of_left_lookup (G₁:=C.G) (G₂:=G₂) (D₂:=D₂)
      (ep:=e) (edge:={ sid := e.sid, sender := source, receiver := e.role })
      (L:=.branch source typeBranches) hDisj hCons hG rfl
  have hStep := StepBase_frame_right_branch_step (C:=C) (G₂:=G₂) (D₂:=D₂)
    hProc hK hG hBuf hFindP hFindT hDeq
  have hFrame := frameGD_branch_right_eq (C:=C) (G₂:=G₂) (D₂:=D₂)
    (e:=e) (source:=source) (P:=P) (L:=L) (bufs':=bufs')
    (typeBranches:=typeBranches) hG hD2
  simpa [hFrame] using hStep

/-- Base steps are preserved under right framing with disjoint G/D. -/
private theorem StepBase_frame_append_right {C C' : Config} {G₂ : GEnv} {D₂ : DEnv}
    (hDisj : DisjointG C.G G₂) (hCons : DConsistent G₂ D₂) :
    StepBase C C' → StepBase (frameGD C G₂ D₂) (frameGD C' G₂ D₂) := by
  -- Dispatch to constructor-specific lemmas.
  intro hBase
  cases hBase with
  | send hProc hK hX hG =>
      exact StepBase_frame_right_send (C:=C) (G₂:=G₂) (D₂:=D₂) hDisj hCons hProc hK hX hG
  | recv hProc hK hG hBuf =>
      exact StepBase_frame_right_recv (C:=C) (G₂:=G₂) (D₂:=D₂) hDisj hCons hProc hK hG hBuf
  | select hProc hK hG hFind =>
      exact StepBase_frame_right_select (C:=C) (G₂:=G₂) (D₂:=D₂) hDisj hCons hProc hK hG hFind
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      exact StepBase_frame_right_branch (C:=C) (G₂:=G₂) (D₂:=D₂)
        hDisj hCons hProc hK hG hBuf hFindP hFindT hDeq
  | newSession hProc =>
      simpa [frameGD, newSessionStep] using (StepBase.newSession (C:=frameGD C G₂ D₂) hProc)
  | assign hProc =>
      simpa [frameGD] using (StepBase.assign (C:=frameGD C G₂ D₂) hProc)
  | seq2 hProc =>
      simpa [frameGD] using (StepBase.seq2 (C:=frameGD C G₂ D₂) hProc)
  | par_skip_left hProc =>
      simpa [frameGD] using (StepBase.par_skip_left (C:=frameGD C G₂ D₂) hProc)
  | par_skip_right hProc =>
      simpa [frameGD] using (StepBase.par_skip_right (C:=frameGD C G₂ D₂) hProc)

/-- Send base step under left framing. -/
private theorem StepBase_frame_left_send {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {k x : Var} {e : Endpoint} {v : Value} {target : Role} {T : ValType} {L : LocalType}
    (hDisj : DisjointG G₁ C.G) (hCons : DConsistent G₁ D₁)
    (hProc : C.proc = .send k x) (hK : lookupStr C.store k = some (.chan e))
    (hX : lookupStr C.store x = some v) (hG : lookupG C.G e = some (.send target T L)) :
    StepBase (frameGD_left C G₁ D₁)
      (frameGD_left (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) G₁ D₁) := by
  -- Build the framed send step and rewrite the result.
  let edge : Edge := { sid := e.sid, sender := e.role, receiver := target }
  have hNoneG : lookupG G₁ e = none := lookupG_none_of_disjoint_left hDisj hG
  have hD1 : D₁.find? edge = none := by
    have hDisj' : DisjointG C.G G₁ := DisjointG_symm hDisj
    exact lookupD_none_of_disjointG (G₁:=C.G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons
      (by simpa [edge] using (⟨e, .send target T L, hG, rfl⟩ : e.sid ∈ SessionsOf C.G))
  have hStep : StepBase (frameGD_left C G₁ D₁) (sendStep (frameGD_left C G₁ D₁) e edge v T L) := by
    apply StepBase.send <;> try simpa [frameGD_left] using hProc
    · simpa [frameGD_left] using hK
    · simpa [frameGD_left] using hX
    · simpa [frameGD_left, hG] using (lookupG_append_right (G₁:=G₁) (G₂:=C.G) (e:=e) hNoneG)
  have hFrame : sendStep (frameGD_left C G₁ D₁) e edge v T L =
      frameGD_left (sendStep C e edge v T L) G₁ D₁ := by
    simpa [edge] using (frameGD_left_sendStep (C:=C) (G₁:=G₁) (D₁:=D₁)
      (ep:=e) (edge:=edge) (v:=v) (T:=T) (L:=L) (Lold:=.send target T L)
      hG hNoneG hD1).symm
  simpa [edge, hFrame] using hStep

/-- Recv base step under left framing. -/
private theorem StepBase_frame_left_recv {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {k x : Var} {e : Endpoint} {v : Value} {vs : List Value}
    {source : Role} {T : ValType} {L : LocalType}
    (hDisj : DisjointG G₁ C.G) (hCons : DConsistent G₁ D₁)
    (hProc : C.proc = .recv k x) (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.recv source T L))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs) :
    StepBase (frameGD_left C G₁ D₁)
      (frameGD_left (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) G₁ D₁) := by
  -- Build the framed recv step and rewrite the result.
  let edge : Edge := { sid := e.sid, sender := source, receiver := e.role }
  have hNoneG : lookupG G₁ e = none := lookupG_none_of_disjoint_left hDisj hG
  have hD1 : D₁.find? edge = none := by
    have hDisj' : DisjointG C.G G₁ := DisjointG_symm hDisj
    exact lookupD_none_of_disjointG (G₁:=C.G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons
      (by simpa [edge] using (⟨e, .recv source T L, hG, rfl⟩ : e.sid ∈ SessionsOf C.G))
  have hStep : StepBase (frameGD_left C G₁ D₁) (recvStep (frameGD_left C G₁ D₁) e edge x v L) := by
    apply StepBase.recv <;> try simpa [frameGD_left] using hProc
    · simpa [frameGD_left] using hK
    · simpa [frameGD_left, hG] using (lookupG_append_right (G₁:=G₁) (G₂:=C.G) (e:=e) hNoneG)
    · simpa [frameGD_left, edge] using hBuf
  have hFrame : recvStep (frameGD_left C G₁ D₁) e edge x v L =
      frameGD_left (recvStep C e edge x v L) G₁ D₁ := by
    simpa [edge] using (frameGD_left_recvStep (C:=C) (G₁:=G₁) (D₁:=D₁)
      (ep:=e) (edge:=edge) (x:=x) (v:=v) (L:=L) (Lold:=.recv source T L)
      hG hNoneG hD1).symm
  simpa [edge, hFrame] using hStep

/-- Select base step under left framing. -/
private theorem StepBase_frame_left_select {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {k : Var} {e : Endpoint} {ℓ : String} {target : Role} {branches : List (String × LocalType)}
    {L : LocalType} (hDisj : DisjointG G₁ C.G) (hCons : DConsistent G₁ D₁)
    (hProc : C.proc = .select k ℓ) (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.select target branches))
    (hFind : branches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    StepBase (frameGD_left C G₁ D₁)
      (frameGD_left (sendStep C e { sid := e.sid, sender := e.role, receiver := target } (.string ℓ) .string L) G₁ D₁) := by
  -- Build the framed select step via sendStep.
  let edge : Edge := { sid := e.sid, sender := e.role, receiver := target }
  have hNoneG : lookupG G₁ e = none := lookupG_none_of_disjoint_left hDisj hG
  have hD1 : D₁.find? edge = none := by
    have hDisj' : DisjointG C.G G₁ := DisjointG_symm hDisj
    exact lookupD_none_of_disjointG (G₁:=C.G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons
      (by simpa [edge] using (⟨e, .select target branches, hG, rfl⟩ : e.sid ∈ SessionsOf C.G))
  have hStep : StepBase (frameGD_left C G₁ D₁)
      (sendStep (frameGD_left C G₁ D₁) e edge (.string ℓ) .string L) := by
    apply StepBase.select <;> try simpa [frameGD_left] using hProc
    · simpa [frameGD_left] using hK
    · simpa [frameGD_left, hG] using (lookupG_append_right (G₁:=G₁) (G₂:=C.G) (e:=e) hNoneG)
    · exact hFind
  have hFrame : sendStep (frameGD_left C G₁ D₁) e edge (.string ℓ) .string L =
      frameGD_left (sendStep C e edge (.string ℓ) .string L) G₁ D₁ := by
    simpa [edge] using (frameGD_left_sendStep (C:=C) (G₁:=G₁) (D₁:=D₁)
      (ep:=e) (edge:=edge) (v:=.string ℓ) (T:=.string) (L:=L)
      (Lold:=.select target branches) hG hNoneG hD1).symm
  simpa [edge, hFrame] using hStep

/-- Helper: construct the framed branch step on the left. -/
private theorem StepBase_frame_left_branch_step {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {k : Var} {e : Endpoint} {source : Role}
    {procBranches : List (String × Process)} {typeBranches : List (String × LocalType)}
    {ℓ : String} {P : Process} {L : LocalType} {vs : List Value} {bufs' : Buffers}
    (hProc : C.proc = .branch k procBranches)
    (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hNoneG : lookupG G₁ e = none)
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: vs)
    (hFindP : procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P))
    (hFindT : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', .string ℓ)) :
    StepBase (frameGD_left C G₁ D₁)
      { frameGD_left C G₁ D₁ with proc := P, bufs := bufs', G := updateG (G₁ ++ C.G) e L,
        D := updateD (D₁ ++ C.D) { sid := e.sid, sender := source, receiver := e.role }
          (lookupD (D₁ ++ C.D) { sid := e.sid, sender := source, receiver := e.role }).tail } := by
  -- Apply the branch rule to the framed configuration.
  apply StepBase.branch <;> try simpa [frameGD_left] using hProc
  · simpa [frameGD_left] using hK
  · simpa [frameGD_left, hG] using (lookupG_append_right (G₁:=G₁) (G₂:=C.G) (e:=e) hNoneG)
  · simpa [frameGD_left] using hBuf
  · exact hFindP
  · exact hFindT
  · simpa [frameGD_left] using hDeq

/-- Helper: rewrite the framed branch result on the left. -/
private theorem frameGD_branch_left_eq {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {e : Endpoint} {source : Role} {P : Process} {L : LocalType} {bufs' : Buffers}
    (hNoneG : lookupG G₁ e = none)
    (hD1 : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none) :
    { frameGD_left C G₁ D₁ with proc := P, bufs := bufs', G := updateG (G₁ ++ C.G) e L,
      D := updateD (D₁ ++ C.D) { sid := e.sid, sender := source, receiver := e.role }
        (lookupD (D₁ ++ C.D) { sid := e.sid, sender := source, receiver := e.role }).tail } =
    frameGD_left { C with proc := P, bufs := bufs', G := updateG C.G e L,
      D := updateD C.D { sid := e.sid, sender := source, receiver := e.role }
        (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail } G₁ D₁ := by
  -- Push updateG/updateD through the left frame.
  ext <;> simp [frameGD_left, updateG_append_left hNoneG,
    updateD_append_right_env hD1, lookupD_append_right hD1]

/-- Branch base step under left framing. -/
private theorem StepBase_frame_left_branch {C : Config} {G₁ : GEnv} {D₁ : DEnv}
    {k : Var} {e : Endpoint} {source : Role}
    {procBranches : List (String × Process)} {typeBranches : List (String × LocalType)}
    {ℓ : String} {P : Process} {L : LocalType} {vs : List Value} {bufs' : Buffers}
    (hDisj : DisjointG G₁ C.G) (hCons : DConsistent G₁ D₁)
    (hProc : C.proc = .branch k procBranches)
    (hK : lookupStr C.store k = some (.chan e))
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = .string ℓ :: vs)
    (hFindP : procBranches.find? (fun b => b.1 == ℓ) = some (ℓ, P))
    (hFindT : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L))
    (hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = some (bufs', .string ℓ)) :
    StepBase (frameGD_left C G₁ D₁)
      (frameGD_left { C with proc := P, bufs := bufs', G := updateG C.G e L,
        D := updateD C.D { sid := e.sid, sender := source, receiver := e.role }
          (lookupD C.D { sid := e.sid, sender := source, receiver := e.role }).tail } G₁ D₁) := by
  -- Combine the framed branch step with the frame rewrite.
  have hNoneG : lookupG G₁ e = none := lookupG_none_of_disjoint_left hDisj hG
  have hD1 : D₁.find? { sid := e.sid, sender := source, receiver := e.role } = none := by
    have hDisj' : DisjointG C.G G₁ := DisjointG_symm hDisj
    exact lookupD_none_of_disjointG (G₁:=C.G) (G₂:=G₁) (D₂:=D₁) hDisj' hCons
      (by simpa using (⟨e, .branch source typeBranches, hG, rfl⟩ : e.sid ∈ SessionsOf C.G))
  have hStep := StepBase_frame_left_branch_step (C:=C) (G₁:=G₁) (D₁:=D₁)
    hProc hK hG hNoneG hBuf hFindP hFindT hDeq
  have hFrame := frameGD_branch_left_eq (C:=C) (G₁:=G₁) (D₁:=D₁)
    (e:=e) (source:=source) (P:=P) (L:=L) (bufs':=bufs') hNoneG hD1
  simpa [hFrame] using hStep

/-- Base steps are preserved under left framing with disjoint G/D. -/
private theorem StepBase_frame_append_left {C C' : Config} {G₁ : GEnv} {D₁ : DEnv}
    (hDisj : DisjointG G₁ C.G) (hCons : DConsistent G₁ D₁) :
    StepBase C C' → StepBase (frameGD_left C G₁ D₁) (frameGD_left C' G₁ D₁) := by
  -- Dispatch to constructor-specific lemmas.
  intro hBase
  cases hBase with
  | send hProc hK hX hG =>
      exact StepBase_frame_left_send (C:=C) (G₁:=G₁) (D₁:=D₁) hDisj hCons hProc hK hX hG
  | recv hProc hK hG hBuf =>
      exact StepBase_frame_left_recv (C:=C) (G₁:=G₁) (D₁:=D₁) hDisj hCons hProc hK hG hBuf
  | select hProc hK hG hFind =>
      exact StepBase_frame_left_select (C:=C) (G₁:=G₁) (D₁:=D₁) hDisj hCons hProc hK hG hFind
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      exact StepBase_frame_left_branch (C:=C) (G₁:=G₁) (D₁:=D₁)
        hDisj hCons hProc hK hG hBuf hFindP hFindT hDeq
  | newSession hProc =>
      simpa [frameGD_left, newSessionStep] using (StepBase.newSession (C:=frameGD_left C G₁ D₁) hProc)
  | assign hProc =>
      simpa [frameGD_left] using (StepBase.assign (C:=frameGD_left C G₁ D₁) hProc)
  | seq2 hProc =>
      simpa [frameGD_left] using (StepBase.seq2 (C:=frameGD_left C G₁ D₁) hProc)
  | par_skip_left hProc =>
      simpa [frameGD_left] using (StepBase.par_skip_left (C:=frameGD_left C G₁ D₁) hProc)
  | par_skip_right hProc =>
      simpa [frameGD_left] using (StepBase.par_skip_right (C:=frameGD_left C G₁ D₁) hProc)

/-- Lift a Step under extra disjoint G/D resources on the right. -/
theorem Step_frame_append_right {C C' : Config} {G₂ : GEnv} {D₂ : DEnv} :
    DisjointG C.G G₂ →
    DConsistent G₂ D₂ →
    Step C C' →
    Step (frameGD C G₂ D₂) (frameGD C' G₂ D₂) := by
  -- Induct over the step and frame base steps using the helper lemma.
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      exact Step.base (StepBase_frame_append_right (C:=C) (C':=C') (G₂:=G₂) (D₂:=D₂) hDisj hCons hBase)
  | seq_left hProc hStep ih =>
      refine Step.seq_left (C:=frameGD C G₂ D₂) (C':=frameGD C' G₂ D₂) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD] using hProc
      · simpa [frameGD] using ih
  | par_left hProc hStep ih =>
      refine Step.par_left (C:=frameGD C G₂ D₂) (C':=frameGD C' G₂ D₂) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD] using hProc
      · simpa [frameGD] using ih
  | par_right hProc hStep ih =>
      refine Step.par_right (C:=frameGD C G₂ D₂) (C':=frameGD C' G₂ D₂) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD] using hProc
      · simpa [frameGD] using ih

/-- Lift a Step under extra disjoint G/D resources on the left. -/
theorem Step_frame_append_left {C C' : Config} {G₁ : GEnv} {D₁ : DEnv} :
    DisjointG G₁ C.G →
    DConsistent G₁ D₁ →
    Step C C' →
    Step (frameGD_left C G₁ D₁) (frameGD_left C' G₁ D₁) := by
  -- Induct over the step and frame base steps using the helper lemma.
  intro hDisj hCons hStep
  induction hStep with
  | base hBase =>
      exact Step.base (StepBase_frame_append_left (C:=C) (C':=C') (G₁:=G₁) (D₁:=D₁) hDisj hCons hBase)
  | seq_left hProc hStep ih =>
      refine Step.seq_left (C:=frameGD_left C G₁ D₁) (C':=frameGD_left C' G₁ D₁) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD_left] using hProc
      · simpa [frameGD_left] using ih
  | par_left hProc hStep ih =>
      refine Step.par_left (C:=frameGD_left C G₁ D₁) (C':=frameGD_left C' G₁ D₁) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD_left] using hProc
      · simpa [frameGD_left] using ih
  | par_right hProc hStep ih =>
      refine Step.par_right (C:=frameGD_left C G₁ D₁) (C':=frameGD_left C' G₁ D₁) (P:=P) (Q:=Q) ?_ ?_
      · simpa [frameGD_left] using hProc
      · simpa [frameGD_left] using ih

/-- Subject reduction: TypedStep implies Step.

    If a configuration can take a typed step from (G, D, S) to (G', D', S'),
    then it can also take an untyped step in the operational semantics.

    This theorem proves soundness of TypedStep with respect to Step.
    Combined with preservation_typed, this gives us full type safety:
    - preservation_typed: TypedStep preserves WellFormed
    - subject_reduction: TypedStep implies Step
    - Together: well-typed programs satisfy operational semantics

    **Proof strategy**: Case analysis on TypedStep, construct corresponding Step.
    Each TypedStep constructor corresponds to a Step rule (or sequence of rules). -/
theorem subject_reduction {n : SessionId} {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩ := by
  intro hTyped
  refine TypedStep.rec (motive := fun G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' _ =>
      Step ⟨P, store, bufs, G, D, n⟩ ⟨P', store', bufs', G', D', n⟩)
    ?send ?recv ?select ?branch ?assign ?seq_step ?seq_skip ?par_left ?par_right
    ?par_skip_left ?par_skip_right hTyped
  · intro G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hSk hSx hG hSenv hVal hRecv hEdge hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    have h := Step.base (StepBase.send (C := ⟨.send k x, store, bufs, G, D, n⟩) rfl hSk hSx hG)
    simpa [sendStep, appendD] using h
  · intro G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hSk hG hEdge hBuf hVal hHead hG' hD' hSown' hStore' hBufs'
    subst hEdge hG' hD' hSown' hStore' hBufs'
    have h := Step.base (StepBase.recv (C := ⟨.recv k x, store, bufs, G, D, n⟩) rfl hSk hG hBuf)
    simpa [recvStep, dequeueBuf, hBuf] using h
  · intro G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hSk hG hFind hRecv hEdge hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    have h := Step.base (StepBase.select (C := ⟨.select k ℓ, store, bufs, G, D, n⟩) rfl hSk hG hFind)
    simpa [sendStep, appendD] using h
  · intro G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hSk hG hEdge hBuf hFindP hFindBs hHead hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    let edge : Edge := { sid := e.sid, sender := source, receiver := e.role }
    have hBuf' : lookupBuf bufs edge = .string ℓ :: vs := by
      simpa [edge] using hBuf
    have hDeq : dequeueBuf bufs edge = some (updateBuf bufs edge vs, .string ℓ) := by
      simp [dequeueBuf, hBuf', edge]
    have h := Step.base (StepBase.branch (C := ⟨.branch k procs, store, bufs, G, D, n⟩)
      rfl hSk hG hBuf' hFindP hFindBs (by simpa [edge] using hDeq))
    simpa using h
  · intro G D Ssh Sown store bufs x v T S' store' hVal hS' hStore'
    subst hS' hStore'
    apply Step.base
    apply StepBase.assign rfl
  · intro G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q hTS ih
    refine Step.seq_left (C := ⟨.seq P Q, store, bufs, G, D, n⟩)
      (C' := ⟨P', store', bufs', G', D', n⟩) (P := P) (Q := Q) ?_ ?_
    · rfl
    · exact ih
  · intro G D Ssh Sown store bufs Q
    apply Step.base
    apply StepBase.seq2 rfl
  · intro Ssh store bufs store' bufs' P P' Q S G D₁ D₂ G₁' D₁' S₁' split
        hTS hDisjG hDisjD hDisjS hConsL hConsR ih
    have hStep := Step_frame_append_right (G₂ := split.G2) (D₂ := D₂)
      (C := ⟨P, store, bufs, split.G1, D₁, n⟩)
      (C' := ⟨P', store', bufs', G₁', D₁', n⟩) hDisjG hConsR ih
    have hStep' : Step ⟨P, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩
        ⟨P', store', bufs', G₁' ++ split.G2, D₁' ++ D₂, n⟩ := by
      simpa [frameGD] using hStep
    have hPar : Step ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩
        ⟨.par P' Q, store', bufs', G₁' ++ split.G2, D₁' ++ D₂, n⟩ := by
      refine Step.par_left (C := ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩)
        (C' := ⟨P', store', bufs', G₁' ++ split.G2, D₁' ++ D₂, n⟩) (P := P) (Q := Q) ?_ ?_
      · rfl
      · exact hStep'
    simpa [split.hG] using hPar
  · intro Ssh store bufs store' bufs' P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
        hTS hDisjG hDisjD hDisjS hConsL hConsR ih
    have hStep := Step_frame_append_left (G₁ := split.G1) (D₁ := D₁)
      (C := ⟨Q, store, bufs, split.G2, D₂, n⟩)
      (C' := ⟨Q', store', bufs', G₂', D₂', n⟩) hDisjG hConsL ih
    have hStep' : Step ⟨Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩
        ⟨Q', store', bufs', split.G1 ++ G₂', D₁ ++ D₂', n⟩ := by
      simpa [frameGD_left] using hStep
    have hPar : Step ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩
        ⟨.par P Q', store', bufs', split.G1 ++ G₂', D₁ ++ D₂', n⟩ := by
      refine Step.par_right (C := ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, n⟩)
        (C' := ⟨Q', store', bufs', split.G1 ++ G₂', D₁ ++ D₂', n⟩) (P := P) (Q := Q) ?_ ?_
      · rfl
      · exact hStep'
    simpa [split.hG] using hPar
  · intro G D Ssh Sown store bufs Q
    apply Step.base
    apply StepBase.par_skip_left rfl
  · intro G D Ssh Sown store bufs P
    apply Step.base
    apply StepBase.par_skip_right rfl

end
