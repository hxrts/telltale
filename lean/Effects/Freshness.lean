/-
Copyright (c) 2025 Rumpsteak Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Effects.Values
import Effects.Environments
import Effects.Process

/-!
# Freshness / Name Supply Invariant

This module defines the `SupplyInv` invariant that ensures all channel IDs
in the runtime state are less than the name supply counter. This enables
safe allocation of fresh channels: allocating at nextId is guaranteed to
produce a channel ID not already in use.

Key components:
- `StoreIdsLt`: all channel IDs in the store are < n
- `BufferIdsLt`: all channel IDs in buffers (keys and values) are < n
- `GIdsLt`: all endpoint IDs in G are < n
- `DIdsLt`: all endpoint IDs in D are < n
- `SupplyInv`: conjunction of all the above

Preservation lemmas show that SupplyInv is maintained by all operations:
- Store update with a value whose IDs are < n
- Buffer update with an endpoint < n and values whose IDs are < n
- G/D updates with endpoints < n
- newChan which bumps n to n+1
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## ID Bound Predicates -/

/-- All channel IDs in store values are < n. -/
def StoreIdsLt (n : Nat) (st : Store) : Prop :=
  ∀ x v, (x, v) ∈ st → v.idLt n

/-- All channel IDs in buffers (both keys and values) are < n. -/
def BufferIdsLt (n : Nat) (B : Buffers) : Prop :=
  (∀ e q, (e, q) ∈ B → e.1 < n) ∧
  (∀ e q v, (e, q) ∈ B → v ∈ q → v.idLt n)

/-- All endpoint IDs in G are < n. -/
def GIdsLt (n : Nat) (G : GEnv) : Prop :=
  ∀ e S, (e, S) ∈ G → e.1 < n

/-- All endpoint IDs in D are < n. -/
def DIdsLt (n : Nat) (D : DEnv) : Prop :=
  ∀ e ts, (e, ts) ∈ D → e.1 < n

/-- The name supply invariant: all channel IDs in the runtime state are < n. -/
def SupplyInv (n : Nat) (st : Store) (B : Buffers) (G : GEnv) (D : DEnv) : Prop :=
  StoreIdsLt n st ∧ BufferIdsLt n B ∧ GIdsLt n G ∧ DIdsLt n D

/-! ## Monotonicity -/

theorem StoreIdsLt_mono {m n : Nat} {st : Store} (hmn : m ≤ n)
    (h : StoreIdsLt m st) : StoreIdsLt n st := by
  intro x v hmem
  exact Value.idLt_mono v hmn (h x v hmem)

theorem BufferIdsLt_mono {m n : Nat} {B : Buffers} (hmn : m ≤ n)
    (h : BufferIdsLt m B) : BufferIdsLt n B := by
  refine ⟨?_, ?_⟩
  · intro e q hmem
    exact Nat.lt_of_lt_of_le (h.1 e q hmem) hmn
  · intro e q v hmemB hmemV
    exact Value.idLt_mono v hmn (h.2 e q v hmemB hmemV)

theorem GIdsLt_mono {m n : Nat} {G : GEnv} (hmn : m ≤ n)
    (h : GIdsLt m G) : GIdsLt n G := by
  intro e S hmem
  exact Nat.lt_of_lt_of_le (h e S hmem) hmn

theorem DIdsLt_mono {m n : Nat} {D : DEnv} (hmn : m ≤ n)
    (h : DIdsLt m D) : DIdsLt n D := by
  intro e ts hmem
  exact Nat.lt_of_lt_of_le (h e ts hmem) hmn

theorem SupplyInv_mono {m n : Nat} {st B G D} (hmn : m ≤ n)
    (h : SupplyInv m st B G D) : SupplyInv n st B G D := by
  rcases h with ⟨hSt, hB, hG, hD⟩
  exact ⟨StoreIdsLt_mono hmn hSt, BufferIdsLt_mono hmn hB,
         GIdsLt_mono hmn hG, DIdsLt_mono hmn hD⟩

/-! ## Preservation under Updates -/

/-- Membership in erased list implies membership in original. -/
theorem mem_erase_implies_mem {κ α : Type} [DecidableEq κ] (m : List (κ × α)) (q : κ) (k : κ) (v : α) :
    (k, v) ∈ Assoc.erase m q → (k, v) ∈ m := by
  induction m with
  | nil => intro h; cases h
  | cons hd tl ih =>
    cases hd with
    | mk k' a =>
      unfold Assoc.erase
      by_cases hk : k' = q
      · simp [hk]
        exact ih
      · simp [hk]
        intro h
        cases h with
        | inl h1 => exact List.mem_cons.mpr (Or.inl h1)
        | inr h2 => exact List.mem_cons.mpr (Or.inr (ih h2))

theorem StoreIdsLt_update {n : Nat} {st : Store} {x : Var} {v : Value}
    (hSt : StoreIdsLt n st) (hv : v.idLt n) : StoreIdsLt n (updateStr st x v) := by
  intro y w hmem
  unfold updateStr at hmem
  simp [Assoc.update] at hmem
  cases hmem with
  | inl h =>
    cases h
    exact hv
  | inr h =>
    exact hSt y w (mem_erase_implies_mem st x y w h)

theorem BufferIdsLt_update_key {n : Nat} {B : Buffers} {e : Endpoint} {q : Buffer}
    (hB : BufferIdsLt n B) (he : e.1 < n) (hq : ∀ v, v ∈ q → v.idLt n) :
    BufferIdsLt n (updateBuf B e q) := by
  refine ⟨?_, ?_⟩
  · intro e' q' hmem
    unfold updateBuf at hmem
    simp [Assoc.update] at hmem
    cases hmem with
    | inl h =>
      cases h
      exact he
    | inr h =>
      exact hB.1 e' q' (mem_erase_implies_mem B e e' q' h)
  · intro e' q' v hmemB hmemV
    unfold updateBuf at hmemB
    simp [Assoc.update] at hmemB
    cases hmemB with
    | inl h =>
      cases h
      exact hq v hmemV
    | inr h =>
      exact hB.2 e' q' v (mem_erase_implies_mem B e e' q' h) hmemV

theorem GIdsLt_update {n : Nat} {G : GEnv} {e : Endpoint} {S : SType}
    (hG : GIdsLt n G) (he : e.1 < n) : GIdsLt n (updateG G e S) := by
  intro e' S' hmem
  unfold updateG at hmem
  simp [Assoc.update] at hmem
  cases hmem with
  | inl h =>
    cases h
    exact he
  | inr h =>
    exact hG e' S' (mem_erase_implies_mem G e e' S' h)

theorem DIdsLt_update {n : Nat} {D : DEnv} {e : Endpoint} {ts : List ValType}
    (hD : DIdsLt n D) (he : e.1 < n) : DIdsLt n (updateD D e ts) := by
  intro e' ts' hmem
  unfold updateD at hmem
  simp [Assoc.update] at hmem
  cases hmem with
  | inl h =>
    cases h
    exact he
  | inr h =>
    exact hD e' ts' (mem_erase_implies_mem D e e' ts' h)

/-! ## newChan Preservation -/

/-- SupplyInv is preserved by newChan, which allocates at n and bumps to n+1. -/
theorem SupplyInv_newChan
    (n : Nat) (st : Store) (B : Buffers) (G : GEnv) (D : DEnv)
    (kL kR : Var) (T : SType)
    (hInv : SupplyInv n st B G D) :
    SupplyInv (n + 1)
      (updateStr (updateStr st kL (Value.chan (n, Polarity.L))) kR (Value.chan (n, Polarity.R)))
      (updateBuf (updateBuf B (n, Polarity.L) []) (n, Polarity.R) [])
      (updateG (updateG G (n, Polarity.L) T) (n, Polarity.R) T.dual)
      (updateD (updateD D (n, Polarity.L) []) (n, Polarity.R) []) := by
  rcases hInv with ⟨hSt, hB, hG, hD⟩

  -- Lift all predicates from n to n+1
  have hSt' : StoreIdsLt (n + 1) st := StoreIdsLt_mono (Nat.le_succ n) hSt
  have hB' : BufferIdsLt (n + 1) B := BufferIdsLt_mono (Nat.le_succ n) hB
  have hG' : GIdsLt (n + 1) G := GIdsLt_mono (Nat.le_succ n) hG
  have hD' : DIdsLt (n + 1) D := DIdsLt_mono (Nat.le_succ n) hD

  -- New values have IDs < n+1
  have hvL : Value.idLt (n + 1) (Value.chan (n, Polarity.L)) := by simp [Value.idLt]
  have hvR : Value.idLt (n + 1) (Value.chan (n, Polarity.R)) := by simp [Value.idLt]

  -- New endpoints have IDs < n+1
  have heL : (n, Polarity.L).1 < n + 1 := Nat.lt_succ_self n
  have heR : (n, Polarity.R).1 < n + 1 := Nat.lt_succ_self n

  -- Empty buffers trivially satisfy value ID bound
  have hEmpty : ∀ v, v ∈ ([] : Buffer) → Value.idLt (n + 1) v := by
    intro v hv; cases hv

  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Store
    exact StoreIdsLt_update (StoreIdsLt_update hSt' hvL) hvR
  · -- Buffers
    exact BufferIdsLt_update_key (BufferIdsLt_update_key hB' heL hEmpty) heR hEmpty
  · -- G
    exact GIdsLt_update (GIdsLt_update hG' heL) heR
  · -- D
    exact DIdsLt_update (DIdsLt_update hD' heL) heR

/-! ## Safe Assignment -/

/-- An assignment is safe if the value's channel IDs are < nextId. -/
def AssignSafe (C : Config) (v : Value) : Prop :=
  v.idLt C.nextId

end
