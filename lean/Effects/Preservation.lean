import Effects.Semantics

/-!
# MPST Preservation Theorem

This module contains the preservation (subject reduction) theorem for MPST:
if a well-typed configuration takes a step, the result is also well-typed.

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
theorem BuffersTyped_enqueue {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  intro a
  unfold BufferTyped
  by_cases ha : a = e
  · -- a = e: the edge we're enqueuing on
    subst ha
    -- The proof requires showing that appending v to buffer and T to trace
    -- preserves the element-wise typing relationship
    -- Using sorry for now - this requires List.get lemmas for append
    sorry
  · -- a ≠ e: unaffected edge
    -- The buffers and trace at edge a are unchanged.
    -- Proof requires dependent type rewriting which is complex in Lean 4.
    -- Key facts:
    --   lookupBuf (enqueueBuf bufs e v) a = lookupBuf bufs a  (by lookupBuf_update_neq)
    --   lookupD (updateD D e _) a = lookupD D a  (by lookupD_update_neq)
    sorry

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
theorem progress_send {C : Config} {S : SEnv} {k x : Var}
    (hEq : C.proc = .send k x)
    (hProc : HasTypeProcPre S C.G (.send k x))
    (hStore : StoreTypedStrong C.G S C.store) :
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
theorem progress_recv {C : Config} {S : SEnv} {k x : Var}
    (hEq : C.proc = .recv k x)
    (hProc : HasTypeProcPre S C.G (.recv k x))
    (hStore : StoreTypedStrong C.G S C.store) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  -- 1. Inversion: extract (e, p, T, L) from typing
  obtain ⟨e, p, T, L, hSk, hGe⟩ := inversion_recv hProc
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
theorem progress_select {C : Config} {S : SEnv} {k : Var} {l : Label}
    (hEq : C.proc = .select k l)
    (hProc : HasTypeProcPre S C.G (.select k l))
    (hStore : StoreTypedStrong C.G S C.store) :
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
theorem progress_branch {C : Config} {S : SEnv} {k : Var} {procs : List (Label × Process)}
    (hEq : C.proc = .branch k procs)
    (hProc : HasTypeProcPre S C.G (.branch k procs))
    (hStore : StoreTypedStrong C.G S C.store)
    (hValidLabels : ∀ (ep : Endpoint) bs l vs,
      lookupG C.G ep = some (.branch ep.role bs) →
      lookupBuf C.bufs ⟨ep.sid, ep.role, ep.role⟩ = (.string l) :: vs →
      (bs.find? (fun b => b.1 == l)).isSome) :
    (∃ C', Step C C') ∨ BlockedRecv C := by
  -- 1. Inversion: extract (e, p, bs) from typing
  obtain ⟨e, p, bs, hSk, hGe, hLen, hLabels⟩ := inversion_branch hProc
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
    -- Non-empty buffer - need to handle string label
    -- For now, we prove the step exists when buffer is non-empty
    -- Full proof requires ValidLabels + HeadCoherent hypothesis
    left
    -- The buffer head should be a string label
    -- This is guaranteed by BufferTyping + HeadCoherent
    sorry  -- Requires HeadCoherent to know v is a string label

end
