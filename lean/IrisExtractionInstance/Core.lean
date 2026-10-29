import IrisExtractionAPI

/-! # IrisExtractionInstance

Concrete Iris extraction boundary with runtime erasure mappings. -/

/-
The Problem. Iris ghost state (invariants, fancy updates, ghost variables) is
proof-only and must be erased at runtime. Without explicit erasure, compiled code
would fail to typecheck or execute nonsensical operations.

Solution Structure. We use `@[implemented_by]` to map logical definitions to trivial
runtime implementations:
1. Fancy updates → identity (mask changes are proof-only)
2. Invariants → their content (no runtime bookkeeping)
3. Ghost ownership → `emp` (ghost state doesn't exist at runtime)
This is sound because Iris adequacy connects logical correctness to operational behavior.
-/

/-! ## Trust Boundary

This file is the **Iris extraction trust boundary**. It contains:

1. **Logical definitions**: Full Iris definitions used by the Lean kernel for
   proof checking (e.g., `fupd`, `inv`, `ghost_var`).

2. **Runtime erasure**: `@[implemented_by]` attributes that substitute trivial
   implementations at codegen/eval time.

## Erasure Laws (Audit Checklist)

Each `@[implemented_by]` follows the pattern:
- **Logical definition**: Full Iris machinery for proof checking
- **Runtime implementation**: Trivial/identity for execution

| Construct | Logical | Runtime | Justification |
|-----------|---------|---------|---------------|
| `fupd E₁ E₂ P` | Fancy update modality | `P` | Mask changes are proof-only |
| `inv N P` | Invariant assertion | `P` | Invariant content only |
| `cinv N ct P` | Cancelable invariant | `P` | Invariant content only |
| `cancel_token_own ct` | Cancellation token | `emp` | Token is ghost ownership |
| `saved_prop_own γ P` | Saved proposition | `P` | Proposition content only |
| `ghost_var γ a` | Ghost variable | `emp` | Ghost ownership erased |
| `ghost_map_auth γ m` | Ghost map auth | `emp` | Ghost ownership erased |
| `ghost_map_elem γ k v` | Ghost map element | `emp` | Ghost ownership erased |

## Why This Is Sound

Ghost state in Iris is **proof-only by design**. From "Iris from the ground up":

> "Ghost state exists logically in the proof alongside the program execution
> but doesn't show up in the operational semantics or the running code."

The `@[implemented_by]` pattern implements this erasure:
- Proofs are checked against the full logical definitions
- Runtime execution uses the erased implementations
- The adequacy theorem connects logical correctness to operational behavior

## Audit Protocol

1. Verify each `@[implemented_by]` maps a ghost construct to its erased form
2. Run `just escape` — Iris hits should come only from this file
3. Run `lake build` — confirms type-correctness of the bridge
-/

set_option autoImplicit false

open Iris Iris.BI

variable [ti : Telltale.TelltaleIris]

/-! ## iProp Connectives -/

namespace iProp

def entails (P Q : iProp) : Prop := @Iris.BI.BIBase.Entails _ _ P Q
def emp : iProp := @Iris.BI.BIBase.emp _ _
def sep (P Q : iProp) : iProp := @Iris.BI.BIBase.sep _ _ P Q
def wand (P Q : iProp) : iProp := @Iris.BI.BIBase.wand _ _ P Q
def pure (φ : Prop) : iProp := @Iris.BI.BIBase.pure _ _ φ
def later (P : iProp) : iProp := @Iris.BI.BIBase.later _ _ P
def persistently (P : iProp) : iProp := @Iris.BI.BIBase.persistently _ _ P
def «exist» {α : Type} (Φ : α → iProp) : iProp :=
  @Iris.BI.BIBase.«exists» _ _ α Φ
def «forall» {α : Type} (Φ : α → iProp) : iProp :=
  @Iris.BI.BIBase.«forall» _ _ α Φ

end iProp

/-! ## Entailment Helpers -/

private theorem entails_refl (P : iProp) : iProp.entails P P :=
  BI.entails_refl

private theorem eq_entails {P Q : iProp} (h : P ⊣⊢ Q) : iProp.entails P Q := h.1

/-- Turn an upstream `⊢ P -∗ Q -∗ R` lemma into `P ∗ Q ⊢ R`. -/
private theorem wand2_entails {P Q R : iProp} (h : ⊢ P -∗ Q -∗ R) :
    iProp.entails (iProp.sep P Q) R :=
  BI.wand_elim (wand_entails h)

/-! ## Separation Logic Laws -/

theorem sep_comm (P Q : iProp) :
    iProp.entails (iProp.sep P Q) (iProp.sep Q P) :=
  eq_entails BI.sep_comm

theorem sep_assoc (P Q R : iProp) :
    iProp.entails (iProp.sep (iProp.sep P Q) R)
      (iProp.sep P (iProp.sep Q R)) :=
  eq_entails BI.sep_assoc

theorem sep_mono (P P' Q Q' : iProp) :
    iProp.entails P P' → iProp.entails Q Q' →
    iProp.entails (iProp.sep P Q) (iProp.sep P' Q') :=
  fun h1 h2 => BI.sep_mono h1 h2

theorem wand_intro (P Q R : iProp) :
    iProp.entails (iProp.sep P Q) R →
    iProp.entails P (iProp.wand Q R) :=
  fun h => BI.wand_intro h

theorem wand_elim (P Q : iProp) :
    iProp.entails (iProp.sep (iProp.wand P Q) P) Q :=
  BI.wand_elim BI.entails_refl

theorem pure_intro (φ : Prop) (P : iProp) :
    φ → iProp.entails P (iProp.sep (iProp.pure φ) P) := by
  intro hφ
  have hEmp : iProp.entails P (iProp.sep iProp.emp P) := BI.emp_sep.2
  have hSep : iProp.entails (iProp.sep iProp.emp P) (iProp.sep (iProp.pure φ) P) :=
    BI.sep_mono (BI.pure_intro hφ) (entails_refl P)
  exact BI.entails_trans hEmp hSep

theorem pure_elim (φ : Prop) (P : iProp) :
    (φ → iProp.entails iProp.emp P) → iProp.entails (iProp.pure φ) P :=
  fun h => BI.pure_elim φ BI.entails_refl
    (fun hφ => BI.entails_trans Affine.affine (h hφ))

theorem persistently_idemp (P : iProp) :
    iProp.entails (iProp.persistently (iProp.persistently P))
      (iProp.persistently P) :=
  eq_entails BI.persistently_idem

theorem persistently_sep_dup (P : iProp) :
    iProp.entails (iProp.persistently P)
      (iProp.sep (iProp.persistently P) (iProp.persistently P)) :=
  BI.persistently_sep_persistently.2

/-! ## Basic Update Modality -/

def bupd (P : iProp) : iProp := Iris.BUpd.bupd P

theorem bupd_mono (P Q : iProp) :
    iProp.entails P Q → iProp.entails (_root_.bupd P) (_root_.bupd Q) :=
  fun h => Iris.bupd_mono h

theorem bupd_intro (P : iProp) : iProp.entails P (_root_.bupd P) :=
  Iris.bupd_intro

theorem bupd_trans (P : iProp) :
    iProp.entails (_root_.bupd (_root_.bupd P)) (_root_.bupd P) :=
  Iris.bupd_trans

theorem bupd_frame_r (P Q : iProp) :
    iProp.entails (iProp.sep (_root_.bupd P) Q) (_root_.bupd (iProp.sep P Q)) :=
  Iris.bupd_frame_right

/-! ## Big Separating Conjunction (Lists) -/

def big_sepL {α : Type} (Φ : α → iProp) : List α → iProp :=
  fun l => l.foldr (fun a acc => iProp.sep (Φ a) acc) iProp.emp

theorem big_sep_l_nil {α : Type} (Φ : α → iProp) :
    iProp.entails (big_sepL Φ []) iProp.emp :=
  entails_refl _

theorem big_sep_l_cons {α : Type} (Φ : α → iProp) (x : α) (l : List α) :
    iProp.entails (big_sepL Φ (x :: l)) (iProp.sep (Φ x) (big_sepL Φ l)) :=
  entails_refl _

theorem big_sep_l_app {α : Type} (Φ : α → iProp) (l₁ l₂ : List α) :
    iProp.entails (big_sepL Φ (l₁ ++ l₂))
      (iProp.sep (big_sepL Φ l₁) (big_sepL Φ l₂)) := by
  induction l₁ with
  | nil =>
    simp only [big_sepL, List.foldr, List.nil_append]
    exact BI.emp_sep.2
  | cons x xs ih =>
    simp only [big_sepL, List.foldr, List.cons_append]
    refine BI.entails_trans (BI.sep_mono (entails_refl _) ih) ?_
    exact (BI.sep_assoc (P := Φ x)).2

/-! ## Masks and Namespaces

Masks are upstream `CoPset`s; namespaces map to masks via `nclose`. -/

namespace Mask

def top : Mask := CoPset.full
def empty : Mask := ∅
def diff (E₁ E₂ : Mask) : Mask := E₁ \ E₂
def union (E₁ E₂ : Mask) : Mask := E₁ ∪ E₂
def subseteq (E₁ E₂ : Mask) : Prop := E₁ ⊆ E₂
def disjoint (E₁ E₂ : Mask) : Prop := E₁ ## E₂

end Mask

namespace Namespace

def root : Telltale.Namespace := nroot
def append (N : Telltale.Namespace) (s : String) : Telltale.Namespace := ndot N s
def append_nat (N : Telltale.Namespace) (n : Nat) : Telltale.Namespace := ndot N n

end Namespace

def namespace_to_mask (N : Telltale.Namespace) : Mask := nclose N

/-! ## Fancy Update Modality

Fancy updates `|={E₁,E₂}=> P` are mask-changing view shifts that enable
atomic access to invariants. At runtime masks are proof-only bookkeeping,
so the runtime implementation is identity: `fupd E₁ E₂ P ↝ P`.
-/

/-- Runtime implementation: fancy update erases to identity on `P`. -/
def fupdImpl (_E₁ _E₂ : Mask) (P : iProp) : iProp := P

/-- Fancy update modality `|={E₁,E₂}=> P`.

**Logical**: upstream Iris fancy update (`uPred_fupd` over world satisfaction).
**Runtime**: Identity (mask tracking is proof-only). -/
@[implemented_by fupdImpl]
def fupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
  Iris.FUpd.fupd E₁ E₂ P

theorem fupd_intro (E : Mask) (P : iProp) :
    iProp.entails P (_root_.fupd E E P) :=
  Iris.fupd_intro

theorem fupd_mono (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails P Q → iProp.entails (_root_.fupd E₁ E₂ P) (_root_.fupd E₁ E₂ Q) :=
  fun h => Iris.fupd_mono h

theorem fupd_trans (E₁ E₂ E₃ : Mask) (P : iProp) :
    iProp.entails (_root_.fupd E₁ E₂ (_root_.fupd E₂ E₃ P)) (_root_.fupd E₁ E₃ P) :=
  Iris.fupd_trans

theorem fupd_frame_r (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails (iProp.sep (_root_.fupd E₁ E₂ P) Q)
      (_root_.fupd E₁ E₂ (iProp.sep P Q)) :=
  Iris.fupd_frame_right

theorem fupd_mask_subseteq (E₁ E₂ : Mask) (hSub : Mask.subseteq E₂ E₁) :
    iProp.entails iProp.emp (_root_.fupd E₁ E₂ (_root_.fupd E₂ E₁ iProp.emp)) :=
  Iris.fupd_mask_subseteq hSub

/-! ## Invariants

`inv N P` asserts that `P` is maintained, openable during a fancy update.
At runtime only the content matters, so `inv N P ↝ P`.
-/

/-- Runtime implementation: invariant erases to its content `P`. -/
def invImpl (_N : Telltale.Namespace) (P : iProp) : iProp := P

/-- Invariant assertion `inv N P` (upstream `Iris.inv`). -/
@[implemented_by invImpl]
def inv (N : Telltale.Namespace) (P : iProp) : iProp :=
  Iris.inv N P

theorem inv_persistent (N : Telltale.Namespace) (P : iProp) :
    iProp.entails (_root_.inv N P) (iProp.persistently (_root_.inv N P)) :=
  (Iris.inv_persistent N P).persistent

/-! ## Cancelable Invariants

`cinv N ct P` is an invariant that can be permanently canceled by consuming
the full cancellation token `cancel_token_own ct`. Both are proof-only: the
invariant erases to its content and the token to `emp`.
-/

/-- Cancelable invariant token handle. -/
abbrev CancelToken := GhostName

/-- Runtime implementation: cancel token erases to `emp`. -/
def cancel_token_ownImpl (_ct : CancelToken) : iProp := iProp.emp

/-- Full ownership of the cancellation token (`cinv_own ct 1`). -/
@[implemented_by cancel_token_ownImpl]
def cancel_token_own (ct : CancelToken) : iProp :=
  CancelableInvariant.own ct 1

/-- Runtime implementation: cancelable invariant erases to content `P`. -/
def cinvImpl (_N : Telltale.Namespace) (_ct : CancelToken) (P : iProp) : iProp := P

/-- Cancelable invariant `cinv N ct P` (upstream `CancelableInvariant.cinv`). -/
@[implemented_by cinvImpl]
def cinv (N : Telltale.Namespace) (ct : CancelToken) (P : iProp) : iProp :=
  CancelableInvariant.cinv N ct P

/-! ## Namespace and Allocation Lemmas -/

/-- Distinct `Nat` children of the same namespace are disjoint. -/
theorem namespace_disjoint (N : Telltale.Namespace) (n₁ n₂ : Nat) (hNe : n₁ ≠ n₂) :
    Mask.disjoint (namespace_to_mask (Namespace.append_nat N n₁))
      (namespace_to_mask (Namespace.append_nat N n₂)) :=
  ndot_ne_disjoint N hNe

/-- Allocate a cancelable invariant from `▷ P`. -/
theorem cinv_alloc (N : Telltale.Namespace) (E : Mask) (P : iProp) :
    iProp.entails (iProp.later P)
      (_root_.fupd E E (iProp.exist fun ct =>
        iProp.sep (cinv N ct P) (cancel_token_own ct))) :=
  wand_entails (CancelableInvariant.alloc E N P)

/-! ## Access and Cancel Lemmas -/

/-- Open a cancelable invariant using its full cancel token. -/
theorem cinv_acc (N : Telltale.Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (_root_.fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.sep (cancel_token_own ct)
            (iProp.wand (iProp.later P)
              (_root_.fupd (Mask.diff E (namespace_to_mask N)) E (iProp.pure True)))))) :=
  wand2_entails (CancelableInvariant.acc hSub)

/-- Cancel a cancelable invariant: consuming the full token yields `▷ P`
back permanently, and the invariant can never be opened again. -/
theorem cinv_cancel (N : Telltale.Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (_root_.fupd E E (iProp.later P)) :=
  wand2_entails (CancelableInvariant.cancel E hSub)
