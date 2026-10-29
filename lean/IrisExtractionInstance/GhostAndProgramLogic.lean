import IrisExtractionInstance.Core

/-! # Iris Extraction: Ghost State and Program Logic

Saved propositions and ghost variables for Iris-based program logic,
with runtime erasure semantics extracting proof-only ghost state. -/

/-
The Problem. Iris separation logic uses ghost state (saved propositions,
ghost variables) for verification. These are proof-only: at runtime, ghost
names have no content. We need extraction-friendly definitions that preserve
logical behavior while erasing to trivial runtime representations.

Solution Structure. Define `saved_prop_own` and `ghost_var` with explicit
runtime implementations via `implemented_by`. Saved propositions erase to
their content; ghost variables erase to `emp`. Provide allocation and
agreement theorems forwarding to the upstream Iris API. Program-logic
reasoning (weakest preconditions, adequacy) uses upstream
`Iris.ProgramLogic` directly; see `Runtime.ProgramLogic.LanguageInstance`.
-/

variable [ti : Telltale.TelltaleIris]

open Iris Iris.BI Iris.Std

/-- Turn an upstream `⊢ P -∗ Q -∗ R` lemma into `P ∗ Q ⊢ R`. -/
private theorem wand2_entails' {P Q R : iProp} (h : ⊢ P -∗ Q -∗ R) :
    iProp.entails (iProp.sep P Q) R :=
  BI.wand_elim (wand_entails h)

/-! ## Saved Propositions

`saved_prop_own γ P` stores `P` under ghost name `γ`; agreement ensures
consistent retrieval. At runtime only the content matters:
`saved_prop_own γ P ↝ P`.
-/

/-- Runtime implementation: saved prop erases to its content `P`. -/
def saved_prop_ownImpl [SavedPropSlot] (_γ : GhostName) (P : iProp) : iProp := P

/-- Saved proposition ownership (upstream `saved_prop_own` with full fraction). -/
@[implemented_by saved_prop_ownImpl]
def saved_prop_own [SavedPropSlot] (γ : GhostName) (P : iProp) : iProp :=
  Iris.saved_prop_own γ (DFrac.own 1) P

theorem saved_prop_alloc [SavedPropSlot] (P : iProp) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => saved_prop_own γ P)) :=
  Iris.saved_prop_alloc P (DFrac.own 1) DFrac.valid_own_one

/-! ## Ghost Variables

`ghost_var γ a` is exclusive ownership of ghost name `γ` with value `a`;
two owners of the same name agree. Ghost state is proof-only, so
`ghost_var γ a ↝ emp` at runtime.
-/

/-- Runtime implementation: ghost variable erases to `emp`. -/
def ghost_varImpl {α : Type} [GhostVarSlot α]
    (_γ : GhostName) (_a : α) : iProp := iProp.emp

/-- Ghost variable ownership (upstream `ghost_var` with full fraction). -/
@[implemented_by ghost_varImpl]
def ghost_var {α : Type} [GhostVarSlot α] (γ : GhostName) (a : α) : iProp :=
  Iris.ghost_var γ (DFrac.own 1) a

theorem ghost_var_alloc {α : Type} [GhostVarSlot α] (a : α) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => ghost_var γ a)) :=
  Iris.ghost_var_alloc a

theorem ghost_var_agree {α : Type} [GhostVarSlot α] (γ : GhostName) (a b : α) :
    iProp.entails (iProp.sep (ghost_var γ a) (ghost_var γ b)) (iProp.pure (a = b)) :=
  wand2_entails' (Iris.ghost_var_agree γ a (DFrac.own 1) b (DFrac.own 1))

theorem ghost_var_update {α : Type} [GhostVarSlot α] (γ : GhostName) (a b : α) :
    iProp.entails (ghost_var γ a) (_root_.bupd (ghost_var γ b)) :=
  wand_entails (Iris.ghost_var_update b γ a)

/-! ## Ghost Maps

`ghost_map_auth γ m` owns the whole map; `ghost_map_elem γ k v` owns one
entry. Both are proof-only and erase to `emp` at runtime.
-/

/-- Ghost maps keyed by positives (upstream `ExtTreeMap` carrier). -/
abbrev GhostMap (V : Type) := Telltale.GhostMapCarrier V

/-- Runtime implementation: ghost map auth erases to `emp`. -/
def ghost_map_authImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_m : GhostMap V) : iProp := iProp.emp

/-- Authoritative ownership of ghost map `m` at name `γ`. -/
@[implemented_by ghost_map_authImpl]
def ghost_map_auth {V : Type} [GhostMapSlot V] (γ : GhostName) (m : GhostMap V) : iProp :=
  Iris.ghost_map_auth (K := Positive) γ (DFrac.own 1) m

/-- Runtime implementation: ghost map elem erases to `emp`. -/
def ghost_map_elemImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_k : Positive) (_v : V) : iProp := iProp.emp

/-- Fragment ownership of entry `(k ↦ v)` in the ghost map at name `γ`. -/
@[implemented_by ghost_map_elemImpl]
def ghost_map_elem {V : Type} [GhostMapSlot V] (γ : GhostName) (k : Positive) (v : V) :
    iProp :=
  Iris.ghost_map_elem (H := Telltale.GhostMapCarrier) γ (DFrac.own 1) k v

/-! ## Ghost Map Laws -/

/-- Lookup: auth + elem implies the key maps to the value. -/
theorem ghost_map_lookup {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Positive) (v : V) (m : GhostMap V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (iProp.pure (get? m k = some v)) :=
  wand2_entails' Iris.ghost_map_lookup

/-- Update: change the value at an existing key. -/
theorem ghost_map_update {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Positive) (v v' : V) (m : GhostMap V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (iProp.sep (ghost_map_auth γ (insert m k v')) (ghost_map_elem γ k v'))) :=
  wand2_entails' (Iris.ghost_map_update v')

/-- Insert: add a new key-value pair (key must not exist). -/
theorem ghost_map_insert {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Positive) (v : V) (m : GhostMap V) (hFresh : get? m k = none) :
    iProp.entails (ghost_map_auth γ m)
      (_root_.bupd (iProp.sep (ghost_map_auth γ (insert m k v)) (ghost_map_elem γ k v))) :=
  wand_entails (Iris.ghost_map_insert k v hFresh)

/-- Delete: remove a key-value pair. -/
theorem ghost_map_delete {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Positive) (v : V) (m : GhostMap V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (ghost_map_auth γ (delete m k))) :=
  wand2_entails' (Iris.ghost_map_delete k v)
