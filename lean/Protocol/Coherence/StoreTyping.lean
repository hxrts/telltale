import Protocol.Coherence.EdgeCoherence

/-! # Protocol.Coherence.StoreTyping

Coherence lemmas and invariants for session-environment evolution.
-/

/-! # MPST Coherence: Store Typing

This module defines typing for the global store (GEnv) and trace store (DEnv).
-/

/-
The Problem. The typing judgment for configurations involves both the GEnv (local
types per endpoint) and DEnv (traces per edge). We need well-definedness criteria
for these stores that connect to coherence.

Solution Structure. We define:
1. Store well-formedness predicates for GEnv and DEnv
2. Connection between store typing and EdgeCoherent
3. Helper lemmas for store updates preserving well-formedness
-/

/- Coherence intuition.
For each directed edge p -> q in a session:
1. Sender-side local state is consistent with queued output.
2. Receiver-side local state is consistent with queued input.
3. Queue shape agrees with the communication structure.

The preservation proofs use a standard three-way edge split:
1. Current edge is the updated edge.
2. Current edge touches an updated endpoint.
3. Current edge is unrelated to the update.
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

/-! ## Store Bridge Lemma

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
