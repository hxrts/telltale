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
remain below with their original sorries documenting the design issue. They are now
deprecated in favor of the TypedStep-based approach.

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

- `preservation_send`: Well-typedness preserved by send
- `preservation_recv`: Well-typedness preserved by recv
- `preservation`: Main theorem

## Proof Techniques

### Inversion on Typing

The send/recv preservation proofs require inverting the process typing judgment
to extract the concrete types involved. For example, if `proc = send k x` and
we know `HasTypeProcN ... proc`, we can extract:
- `lookupSEnv S k = some (chan sid role)` (channel variable)
- `lookupSEnv S x = some T` (payload has the expected type)
- `lookupG G e = some (send target T L)` (endpoint at send state)

### Channel Aliasing

A subtle issue arises when multiple variables might refer to the same endpoint.
In a full development, `StoreNoAlias` would ensure each endpoint is held by
exactly one variable (linearity). Without this, when we update G[e], we must
consider whether other variables in S also reference e.

For now, this aliasing case is marked `sorry` and would be resolved by adding
a linearity invariant to WTConfigN.

### HasTypeVal Stability

HasTypeVal is stable under G updates for non-channel values (unit, bool, nat, string).
For channel values, we need to track whether the channel is the one being updated:
- If `e' = e` (the endpoint being updated): type changes to new type
- If `e' ≠ e`: lookup unchanged, HasTypeVal preserved

Use `lookupG_update_neq` to show the lookup is unchanged for unrelated endpoints.
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
  simpa using (BuffersTyped_enqueue (G := G) (D := D) (bufs := bufs) (e := e) (v := v) (T := T) hBT hv)

/-! ## Preservation for Individual Steps -/

/-- Preservation for send step.

    **Proof outline**:

    1. Unpack WTConfigN into (hN, hStore, hBufs, hCoh, hProcTy)
    2. Invert process typing: must be HasTypeProcN.send rule
       This gives us T, L such that:
       - `lookupSEnv S k = some (chan sid role)` for the endpoint
       - `lookupSEnv S x = some T` for the payload type
       - `lookupG G e = some (send target T L)` for the session type
    3. Build WTConfigN for post-configuration:
       - nextId: unchanged by send
       - StoreTyped: Store unchanged; by_cases on each variable
         - If y = k (channel): show e now has type L in G'
         - If y ≠ k: use lookupG_update_neq for stability
       - BuffersTyped: use `BuffersTyped_enqueue` with HasTypeVal for v
       - Coherent: use `Coherent_send_preserved`
       - Process typing: skip is well-typed

    **NOTE**: There's a design tension in the typing rules:
    - `HasTypeProcN.send` produces a judgment with post-update G (G[e] := L)
    - This theorem assumes G has the send type at e (pre-update)
    - Resolution options:
      1. Change typing to use pre-update environments (standard approach)
      2. Change preservation theorem to match current typing discipline
      3. Use an auxiliary "expected type" function
    This sorry marks the need to resolve this design issue. -/
theorem preservation_send
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config)
    (k x : Var) (e : Endpoint) (target : Role) (v : Value)
    (hWT : WTConfigN n S G D C)
    (hProc : C.proc = .send k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hx : lookupStr C.store x = some v) :
    ∃ T L,
      lookupG G e = some (.send target T L) ∧
      lookupSEnv S x = some T ∧
      WTConfigN n S
        (updateG G e L)
        (updateD D { sid := e.sid, sender := e.role, receiver := target } (lookupD D { sid := e.sid, sender := e.role, receiver := target } ++ [T]))
        (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) := by
  sorry  -- Proof requires inversion on typing as outlined above

/-- Preservation for recv step.

    **Proof outline**:

    1. Unpack WTConfigN into (hN, hStore, hBufs, hCoh, hProcTy)
    2. Invert process typing: must be HasTypeProcN.recv rule
       This gives us T, L such that:
       - `lookupSEnv S k = some (chan sid role)` for the endpoint
       - `lookupG G e = some (recv source T L)` for the session type
    3. From BuffersTyped, get that v has type T (the head of the trace)
    4. Build WTConfigN for post-configuration:
       - nextId: unchanged by recv
       - StoreTyped: Store updated with (x, v); use HasTypeVal from step 3
       - BuffersTyped: buffer at edge dequeued, trace at edge tailed
       - Coherent: use `Coherent_recv_preserved`
       - Process typing: skip is well-typed

    **NOTE**: Same design tension as preservation_send - the recv typing
    rule uses post-update S and G, but this theorem assumes pre-update. -/
theorem preservation_recv
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config)
    (k x : Var) (e : Endpoint) (source : Role) (v : Value) (vs : List Value)
    (hWT : WTConfigN n S G D C)
    (hProc : C.proc = .recv k x)
    (hk : lookupStr C.store k = some (.chan e))
    (hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs) :
    ∃ T L,
      lookupG G e = some (.recv source T L) ∧
      WTConfigN n (updateSEnv S x T)
        (updateG G e L)
        (updateD D { sid := e.sid, sender := source, receiver := e.role } (lookupD D { sid := e.sid, sender := source, receiver := e.role }).tail)
        (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) := by
  sorry  -- Proof requires inversion on typing as outlined above

/-! ## Main Preservation Theorem -/

/-- Preservation: if C is well-typed and steps to C', then C' is well-typed.
    This is the subject reduction theorem for MPST.

    **Proof by induction on Step**:

    **Base cases** (BaseStep):
    - `seq2`: seq skip Q → Q
      Invert seq typing to extract Q's typing; environments unchanged
    - `par_skip_left/right`: par skip Q → Q, par P skip → P
      Similar to seq2
    - `assign`: assign x v → skip
      Update S with type of v, store with v; use HasTypeVal
    - `newSession`: Allocate fresh session ID
      Use SupplyInv_newSession for freshness preservation
      Extend G with new endpoints, D with empty traces
    - `send`: Use `preservation_send` lemma
    - `recv`: Use `preservation_recv` lemma

    **Inductive cases** (context rules):
    - `seq_left P P' Q`: P → P' implies seq P Q → seq P' Q
      Apply IH to get (n', S', G', D', hWT') for P'
      Rebuild seq typing with Q (note: Q's typing may need weakening)
    - `par_left P P' Q`, `par_right P Q Q'`: Similar
      For par, both branches may need separate session resources

    **Key insight**: Each case either:
    1. Doesn't touch protocol state (seq2, par_skip_*) → environments unchanged
    2. Advances exactly one endpoint's type (send, recv) → use coherence lemmas
    3. Creates fresh state (newSession) → extend environments consistently
    4. Passes to subterm (context rules) → use induction hypothesis -/
theorem preservation
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (C C' : Config)
    (hWT : WTConfigN n S G D C)
    (hStep : Step C C') :
    ∃ n' S' G' D', WTConfigN n' S' G' D' C' := by
  sorry  -- Full proof by case analysis on step as outlined above

/-! ## Progress Theorem -/

/-- Progress: a well-typed configuration either terminates, can step, or is blocked on recv. -/
theorem progress
    (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv) (C : Config)
    (hWT : WTConfigN n S G D C) :
    Step.Terminates C ∨ (∃ C', Step C C') ∨
    (∃ k x e source, C.proc = .recv k x ∧
      lookupStr C.store k = some (.chan e) ∧
      lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = []) := by
  sorry  -- Full proof requires case analysis on process typing

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
      simpa [branchEdge, hBuf] using (Nat.succ_pos vs.length)
    have h0trace : 0 < (lookupD C.D branchEdge).length := by
      simpa [hLenBuf] using h0buf
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
                      have hContra : False := (hNo _ hMemP) hPred
                      simpa [hFindP] using hContra
                  | some b =>
                      simp [hFindP]
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

private axiom updateD_append_left {D₁ D₂ : DEnv} {e : Edge} {ts : List ValType}
    (h : D₁.find? e = none) :
    updateD (D₁ ++ D₂) e ts = D₁ ++ updateD D₂ e ts

/-- TODO: Prove this lemma once DEnv framing is settled (list order vs map semantics).
    Currently used to lift a Step under extra disjoint G/D resources. -/
axiom Step_frame_append_right {C C' : Config} {G₂ : GEnv} {D₂ : DEnv} :
    Step C C' →
    Step (frameGD C G₂ D₂) (frameGD C' G₂ D₂)

axiom Step_frame_append_left {C C' : Config} {G₁ : GEnv} {D₁ : DEnv} :
    Step C C' →
    Step (frameGD_left C G₁ D₁) (frameGD_left C' G₁ D₁)

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
theorem subject_reduction {G D Ssh Sown store bufs P G' D' Sown' store' bufs' P'} :
    TypedStep G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' →
    Step ⟨P, store, bufs, G, D, 0⟩ ⟨P', store', bufs', G', D', 0⟩ := by
  intro hTyped
  refine TypedStep.rec (motive := fun G D Ssh Sown store bufs P G' D' Sown' store' bufs' P' _ =>
      Step ⟨P, store, bufs, G, D, 0⟩ ⟨P', store', bufs', G', D', 0⟩)
    ?send ?recv ?select ?branch ?assign ?seq_step ?seq_skip ?par_left ?par_right
    ?par_skip_left ?par_skip_right hTyped
  · intro G D Ssh Sown store bufs k x e target T L v sendEdge G' D' bufs'
        hSk hSx hG hSenv hVal hRecv hEdge hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    have h := Step.base (StepBase.send (C := ⟨.send k x, store, bufs, G, D, 0⟩) rfl hSk hSx hG)
    simpa [sendStep, appendD] using h
  · intro G D Ssh Sown store bufs k x e source T L v vs recvEdge G' D' Sown' store' bufs'
        hSk hG hEdge hBuf hVal hHead hG' hD' hSown' hStore' hBufs'
    subst hEdge hG' hD' hSown' hStore' hBufs'
    have h := Step.base (StepBase.recv (C := ⟨.recv k x, store, bufs, G, D, 0⟩) rfl hSk hG hBuf)
    simpa [recvStep, dequeueBuf, hBuf] using h
  · intro G D Ssh Sown store bufs k ℓ e target bs L selectEdge G' D' bufs'
        hSk hG hFind hRecv hEdge hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    have h := Step.base (StepBase.select (C := ⟨.select k ℓ, store, bufs, G, D, 0⟩) rfl hSk hG hFind)
    simpa [sendStep, appendD] using h
  · intro G D Ssh Sown store bufs k procs e source bs ℓ P L vs branchEdge G' D' bufs'
        hSk hG hEdge hBuf hFindP hFindBs hHead hG' hD' hBufs'
    subst hEdge hG' hD' hBufs'
    let edge : Edge := { sid := e.sid, sender := source, receiver := e.role }
    have hBuf' : lookupBuf bufs edge = .string ℓ :: vs := by
      simpa [edge] using hBuf
    have hDeq : dequeueBuf bufs edge = some (updateBuf bufs edge vs, .string ℓ) := by
      simp [dequeueBuf, hBuf', edge]
    have h := Step.base (StepBase.branch (C := ⟨.branch k procs, store, bufs, G, D, 0⟩)
      rfl hSk hG hBuf' hFindP hFindBs (by simpa [edge] using hDeq))
    simpa using h
  · intro G D Ssh Sown store bufs x v T S' store' hVal hS' hStore'
    subst hS' hStore'
    apply Step.base
    apply StepBase.assign rfl
  · intro G D Ssh Sown G' D' Sown' store bufs store' bufs' P P' Q hTS ih
    refine Step.seq_left (C := ⟨.seq P Q, store, bufs, G, D, 0⟩)
      (C' := ⟨P', store', bufs', G', D', 0⟩) (P := P) (Q := Q) ?_ ?_
    · rfl
    · exact ih
  · intro G D Ssh Sown store bufs Q
    apply Step.base
    apply StepBase.seq2 rfl
  · intro Ssh store bufs P P' Q S G D₁ D₂ G₁' D₁' S₁' split
        hTS hDisjG hDisjD hDisjS hConsL hConsR ih
    have hStep := Step_frame_append_right (G₂ := split.G2) (D₂ := D₂)
      (C := ⟨P, store, bufs, split.G1, D₁, 0⟩)
      (C' := ⟨P', store, bufs, G₁', D₁', 0⟩) ih
    have hStep' : Step ⟨P, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩
        ⟨P', store, bufs, G₁' ++ split.G2, D₁' ++ D₂, 0⟩ := by
      simpa [frameGD] using hStep
    have hPar : Step ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩
        ⟨.par P' Q, store, bufs, G₁' ++ split.G2, D₁' ++ D₂, 0⟩ := by
      refine Step.par_left (C := ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩)
        (C' := ⟨P', store, bufs, G₁' ++ split.G2, D₁' ++ D₂, 0⟩) (P := P) (Q := Q) ?_ ?_
      · rfl
      · exact hStep'
    simpa [split.hG] using hPar
  · intro Ssh store bufs P Q Q' S G D₁ D₂ G₂' D₂' S₂' split
        hTS hDisjG hDisjD hDisjS hConsL hConsR ih
    have hStep := Step_frame_append_left (G₁ := split.G1) (D₁ := D₁)
      (C := ⟨Q, store, bufs, split.G2, D₂, 0⟩)
      (C' := ⟨Q', store, bufs, G₂', D₂', 0⟩) ih
    have hStep' : Step ⟨Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩
        ⟨Q', store, bufs, split.G1 ++ G₂', D₁ ++ D₂', 0⟩ := by
      simpa [frameGD_left] using hStep
    have hPar : Step ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩
        ⟨.par P Q', store, bufs, split.G1 ++ G₂', D₁ ++ D₂', 0⟩ := by
      refine Step.par_right (C := ⟨.par P Q, store, bufs, split.G1 ++ split.G2, D₁ ++ D₂, 0⟩)
        (C' := ⟨Q', store, bufs, split.G1 ++ G₂', D₁ ++ D₂', 0⟩) (P := P) (Q := Q) ?_ ?_
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
