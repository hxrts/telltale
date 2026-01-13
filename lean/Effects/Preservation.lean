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
  sorry  -- Proof requires careful case analysis

/-- BuffersTyped is preserved when enqueuing a well-typed value. -/
theorem BuffersTyped_enqueue {G : GEnv} {D : DEnv} {bufs : Buffers}
    {e : Edge} {v : Value} {T : ValType}
    (hBT : BuffersTyped G D bufs)
    (hv : HasTypeVal G v T) :
    BuffersTyped G (updateD D e (lookupD D e ++ [T])) (enqueueBuf bufs e v) := by
  sorry  -- Proof requires index manipulation

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
       - Process typing: skip is well-typed -/
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
        (sendStep C { sid := e.sid, sender := e.role, receiver := target } v) := by
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
       - Process typing: skip is well-typed -/
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
        (recvStep C { sid := e.sid, sender := source, receiver := e.role } x v) := by
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

end
