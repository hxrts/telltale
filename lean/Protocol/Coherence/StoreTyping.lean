import Protocol.Coherence.EdgeCoherence

/-!
# MPST Coherence

This module defines the coherence invariant for multiparty session types.

In binary session types, coherence states that after consuming in-flight messages,
dual endpoints have dual types. In MPST, this generalizes to:

**For each directed edge (p → q) in session s:**
1. The sender's local type G[s,p] is consistent with what was sent on D[s,p,q]
2. The receiver's local type G[s,q] is consistent with what must be received on D[s,p,q]
3. The communication patterns match: sends to q align with branches from p

## Consume Function

The `Consume` function models how a local type evolves as buffered messages arrive.
For role p's view:
- `Consume L [] = some L` (no messages → unchanged)
- `Consume (recv q T L) (T :: ts) = Consume L ts` (receive consumes a message)
- `Consume (branch q bs) _ = ...` (branch must handle incoming label)

## Coherence Invariant

`Coherent G D` states that for every session and every directed edge:
- Sender's continuation after sending matches what's in the queue
- Receiver's continuation after consuming matches sender's intent

## Proof Technique: Edge Case Analysis

The key preservation proofs (`Coherent_send_preserved`, `Coherent_recv_preserved`)
proceed by case analysis on which edge we're checking coherence for:

1. **e = updated edge**: The sender's/receiver's local type changed, trace changed
2. **e involves modified endpoint**: The other endpoint of e was modified
3. **e unrelated**: Neither endpoint was modified, environments unchanged at e

This 3-way case split is the core proof technique for coherence preservation.
Adapted from binary session types where the split is: a = e, a = e.dual, a unrelated.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Store Typing -/

/-- Store is typed by SEnv: every variable has its declared type. -/
def StoreTyped (G : GEnv) (S : SEnv) (store : VarStore) : Prop :=
  ∀ x v T,
    lookupStr store x = some v →
    lookupSEnv S x = some T →
    HasTypeVal G v T

/-- Strong store typing: same-domain property + type correspondence.
    This strengthening is needed for the progress theorem.
    Reference: `work/effects/008.lean:114-116` -/
structure StoreTypedStrong (G : GEnv) (S : SEnv) (store : VarStore) : Prop where
  /-- Same-domain: S and store have the same variables. -/
  sameDomain : ∀ x, (lookupSEnv S x).isSome ↔ (lookupStr store x).isSome
  /-- Type correspondence: values have their declared types. -/
  typeCorr : StoreTyped G S store

/-- StoreTypedStrong implies StoreTyped. -/
theorem StoreTypedStrong.toStoreTyped {G : GEnv} {S : SEnv} {store : VarStore}
    (h : StoreTypedStrong G S store) : StoreTyped G S store :=
  h.typeCorr

/-! ### Store Bridge Lemma

The key lemma connecting static typing to runtime values.
Reference: `work/effects/008.lean:304-308` -/

/-- If a variable has a type in the static environment and the store is strongly typed,
    then the variable exists in the store and its value has the corresponding type.
    Reference: `work/effects/008.lean:304-308` -/
theorem store_lookup_of_senv_lookup {G : GEnv} {S : SEnv} {store : VarStore} {x : Var} {T : ValType}
    (hStore : StoreTypedStrong G S store) (hS : lookupSEnv S x = some T) :
    ∃ v, lookupStr store x = some v ∧ HasTypeVal G v T := by
  -- From sameDomain: if x is in S, then x is in store
  have hDom := hStore.sameDomain x
  rw [hS, Option.isSome_some] at hDom
  have hInStore : (lookupStr store x).isSome := hDom.mp rfl
  -- Get the value from store
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hInStore
  -- Use type correspondence
  have hTyped := hStore.typeCorr x v T hv hS
  exact ⟨v, hv, hTyped⟩

/-- Weaker version when we only have StoreTyped but know the variable is in store.
    This is useful when the step relation already provides the store lookup. -/
theorem store_value_typed {G : GEnv} {S : SEnv} {store : VarStore} {x : Var} {v : Value} {T : ValType}
    (hStore : StoreTyped G S store) (hStr : lookupStr store x = some v) (hS : lookupSEnv S x = some T) :
    HasTypeVal G v T :=
  hStore x v T hStr hS

/-! ## EdgeCoherent Irrelevance Lemmas -/

/-- Updating G at an endpoint not involved in edge e doesn't affect EdgeCoherent at e.
    Reference: `work/effects/004.lean` EdgeCoherent_updateG_irrelevant -/
theorem EdgeCoherent_updateG_irrelevant (G : GEnv) (D : DEnv) (e : Edge)
    (ep : Endpoint) (L : LocalType)
    (hNeSender : ep ≠ { sid := e.sid, role := e.sender })
    (hNeRecv : ep ≠ { sid := e.sid, role := e.receiver })
    (hCoh : EdgeCoherent G D e) :
    EdgeCoherent (updateG G ep L) D e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lrecv hGrecv
  -- Use lookupG_update_neq since ep is different from both endpoints
  have hGrecv' : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv := by
    simpa [lookupG_update_neq _ _ _ _ hNeRecv] using hGrecv
  obtain ⟨Lsender, hGsender, hConsume⟩ := hCoh Lrecv hGrecv'
  refine ⟨Lsender, ?_, hConsume⟩
  simpa [lookupG_update_neq _ _ _ _ hNeSender] using hGsender

/-- Updating D at edge e' ≠ e doesn't affect EdgeCoherent at e.
    Reference: `work/effects/004.lean` EdgeCoherent_updateD_irrelevant -/
theorem EdgeCoherent_updateD_irrelevant (G : GEnv) (D : DEnv) (e e' : Edge)
    (ts : List ValType)
    (hNe : e' ≠ e)
    (hCoh : EdgeCoherent G D e) :
    EdgeCoherent G (updateD D e' ts) e := by
  simp only [EdgeCoherent] at hCoh ⊢
  intro Lrecv hGrecv
  -- Use lookupD_update_neq since e' ≠ e
  simp only [lookupD_update_neq _ _ _ _ hNe]
  exact hCoh Lrecv hGrecv


end
