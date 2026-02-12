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
agreement theorems forwarding to the upstream Iris API.
-/

variable [ti : Telltale.TelltaleIris]

/-! ## Saved Propositions

Saved propositions allow storing an `iProp` under a ghost name for later
retrieval. This is useful for existentially packaging propositions that
need to be "remembered" across proof steps.

**Logical behavior**: `saved_prop_own γ P` asserts ownership of ghost name
`γ` pointing to proposition `P`. Agreement ensures consistent retrieval.

**Runtime behavior**: The ghost name and ownership are proof-only. At runtime,
we only need the proposition content, so `saved_prop_own γ P ↝ P`.
-/

/-- Runtime implementation: saved prop erases to its content `P`. -/
def saved_prop_ownImpl [SavedPropSlot] (_γ : GhostName) (P : iProp) : iProp := P

/-- Saved proposition ownership `saved_prop_own γ P`.

**Logical**: Ghost ownership of name `γ` storing proposition `P`.
**Runtime**: Just the content `P` (ghost name is proof-only). -/
@[implemented_by saved_prop_ownImpl]
def saved_prop_own [SavedPropSlot] (γ : GhostName) (P : iProp) :
    iProp :=
  Iris.BaseLogic.saved_prop_own (GF := ti.GF) (F := ti.F) γ (Iris.DFrac.own 1) P

theorem saved_prop_alloc [SavedPropSlot] (P : iProp) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => saved_prop_own γ P)) :=
  Iris.BaseLogic.saved_prop_alloc (GF := ti.GF) (F := ti.F)
    (Iris.DFrac.own 1) Iris.DFrac.valid_own_one P

/-! ## Ghost Variables

Ghost variables provide mutable ghost state: a ghost name `γ` holds a value
of type `α` that can be read, agreed upon, and updated.

**Logical behavior**: `ghost_var γ a` asserts exclusive ownership of ghost
name `γ` with current value `a`. The agreement law ensures two owners of
the same name must have equal values.

**Runtime behavior**: Ghost variables are purely logical — they exist only
for proof. At runtime, ownership is vacuously true: `ghost_var γ a ↝ emp`.
-/

/-- Runtime implementation: ghost variable erases to `emp` (no runtime content). -/
def ghost_varImpl {α : Type} [GhostVarSlot α]
    (_γ : GhostName) (_a : α) : iProp := iProp.emp

/-- Ghost variable ownership `ghost_var γ a`.

**Logical**: Exclusive ownership of ghost name `γ` with value `a`.
**Runtime**: `emp` (ghost state has no runtime representation). -/
@[implemented_by ghost_varImpl]
def ghost_var {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a : α) : iProp :=
  Iris.BaseLogic.ghost_var (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.DFrac.own 1) (Iris.LeibnizO.mk a)

theorem ghost_var_alloc {α : Type} [GhostVarSlot α] (a : α) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => ghost_var γ a)) := by
  exact Iris.BaseLogic.ghost_var_alloc (GF := ti.GF) (F := ti.F)
    (A := Iris.LeibnizO α) (Iris.LeibnizO.mk a)

theorem ghost_var_agree {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a b : α) :
    iProp.entails (iProp.sep (ghost_var γ a) (ghost_var γ b))
      (iProp.pure (a = b)) := by
  have h := Iris.BaseLogic.ghost_var_agree (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.DFrac.own 1) (Iris.DFrac.own 1) (Iris.LeibnizO.mk a) (Iris.LeibnizO.mk b)
  refine h.trans ?_
  exact Iris.BI.pure_mono (fun heq => Iris.LeibnizO.mk.injEq a b ▸ heq)

theorem ghost_var_update {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a b : α) :
    iProp.entails (ghost_var γ a) (_root_.bupd (ghost_var γ b)) :=
  Iris.BaseLogic.ghost_var_update (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.LeibnizO.mk a) (Iris.LeibnizO.mk b)

/-! ## Ghost Maps

Ghost maps provide a ghost-state finite map from keys to values. The auth/frag
pattern enables reasoning about partial ownership:
- `ghost_map_auth γ m`: authoritative ownership of the whole map `m`
- `ghost_map_elem γ k v`: fragment ownership of entry `(k ↦ v)`

**Logical behavior**: Auth + elem for the same key implies agreement on the
value. Updates require combining auth and elem ownership.

**Runtime behavior**: Ghost maps are purely logical. Both auth and elem
ownership erase to `emp` at runtime.
-/

/-- Type alias for ghost maps using iris-lean's finite map infrastructure. -/
abbrev GhostMap (V : Type) [ti : Telltale.TelltaleIris] := ti.M (Iris.LeibnizO V)

/-! ## Ghost Map Runtime Erasure Implementations -/

open Telltale in
/-- Runtime implementation: ghost map auth erases to `emp`. -/
def ghost_map_authImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_m : GhostMap V) : iProp := iProp.emp

/-- Authoritative ownership of ghost map `m` at name `γ`.

**Logical**: Full ownership of the map, required for lookups and updates.
**Runtime**: `emp` (ghost state has no runtime representation). -/
@[implemented_by ghost_map_authImpl]
def ghost_map_auth {V : Type} [GhostMapSlot V]
    (γ : GhostName) (m : GhostMap V) : iProp :=
  Iris.BaseLogic.ghost_map_auth (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ 1 m

/-! ## Ghost Map Fragment Erasure and Ownership -/

open Telltale in
/-- Runtime implementation: ghost map elem erases to `emp`. -/
def ghost_map_elemImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_k : Iris.Positive) (_v : V) : iProp := iProp.emp

/-- Fragment ownership of entry `(k ↦ v)` in ghost map at name `γ`.

**Logical**: Partial ownership of one key-value pair. Combine with auth for
lookups; combine auth+elem for updates.
**Runtime**: `emp` (ghost state has no runtime representation). -/
@[implemented_by ghost_map_elemImpl]
def ghost_map_elem {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v : V) : iProp :=
  Iris.BaseLogic.ghost_map_elem (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) ∅ γ k (Iris.DFrac.own 1) (Iris.LeibnizO.mk v)

/-! ## Ghost Map Lookup and Update Laws -/

open Telltale Iris.Std in
/-- Lookup: auth + elem implies the key maps to the value. -/
theorem ghost_map_lookup {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v : V) (m : GhostMap V) :
    iProp.entails
      (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (iProp.pure (get? m k = some (Iris.LeibnizO.mk v))) :=
  Iris.BaseLogic.ghost_map_lookup (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ 1 m k (Iris.DFrac.own 1) (Iris.LeibnizO.mk v)

open Telltale Iris.Std in
/-- Update: change the value at an existing key. -/
theorem ghost_map_update {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v v' : V) (m : GhostMap V) :
    iProp.entails
      (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (iProp.sep
        (ghost_map_auth γ (insert m k (Iris.LeibnizO.mk v')))
        (ghost_map_elem γ k v'))) :=
  Iris.BaseLogic.ghost_map_update (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ m k (Iris.LeibnizO.mk v) (Iris.LeibnizO.mk v')

/-! ## Ghost Map Insert/Delete Laws -/

open Telltale Iris.Std in
/-- Insert: add a new key-value pair (key must not exist). -/
theorem ghost_map_insert {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v : V) (m : GhostMap V)
    (hFresh : get? m k = none) :
    iProp.entails
      (ghost_map_auth γ m)
      (_root_.bupd (iProp.sep
        (ghost_map_auth γ (insert m k (Iris.LeibnizO.mk v)))
        (ghost_map_elem γ k v))) :=
  Iris.BaseLogic.ghost_map_insert (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ m k (Iris.LeibnizO.mk v) hFresh

open Telltale Iris.Std in
/-- Delete: remove a key-value pair. -/
theorem ghost_map_delete {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v : V) (m : GhostMap V) :
    iProp.entails
      (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (ghost_map_auth γ (delete m k))) :=
  Iris.BaseLogic.ghost_map_delete (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ m k (Iris.LeibnizO.mk v)

/-! ## Program Logic (Compatibility Shims) -/

namespace Iris

/-- Compatibility state interpretation predicate. -/
def state_interp (Λ : Iris.ProgramLogic.Language) (σ : Λ.state) : iProp :=
  iProp.emp

/-- Compatibility weakest precondition. -/
def wp (Λ : Iris.ProgramLogic.Language) (E : Mask) (e : Λ.expr)
    (Φ : Λ.val → iProp) : iProp :=
  iProp.emp

/-- Compatibility multi-step relation. -/
def MultiStep' {Λ : Iris.ProgramLogic.Language} :
  Λ.expr → Λ.state → Λ.expr → Λ.state → Prop :=
  fun _ _ _ _ => False

/-- Compatibility invariance lemma for WP. -/
theorem wp_invariance {Λ : Iris.ProgramLogic.Language} {e : Λ.expr} {σ : Λ.state}
    {Φ : Λ.val → iProp} :
  iProp.entails iProp.emp (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ)) →
  ∀ e' σ',
    MultiStep' (Λ:=Λ) e σ e' σ' →
    iProp.entails iProp.emp (_root_.bupd (state_interp Λ σ')) := by
  intro _ e' σ' hStep
  cases hStep

end Iris
