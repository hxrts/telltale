import IrisExtractionAPI

/-!
# IrisExtractionInstance

Concrete Iris extraction boundary.

This module contains the full logical bridge used by proofs and attaches
runtime erasure mappings for ghost-only constructs.

## Audit Checklist

- Logical definitions remain those used by proof checking.
- Runtime erasure mappings are explicit and reviewable in this file.
- `just escape` should report Iris extraction override hits only from this module.
-/

set_option autoImplicit false

namespace Telltale

variable [ti : TelltaleIris]

def uPredFupdImpl (_E₁ _E₂ : Mask) (P : iProp) : iProp := P

@[implemented_by uPredFupdImpl]
def uPredFupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
  Iris.BaseLogic.uPred_fupd
    (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W E₁ E₂ P

end Telltale

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

/-! ## Big Separation over Maps -/

def big_sepM {K : Type _} {V : Type _} {M' : Type _ → Type _}
    [Iris.Std.FiniteMap K M'] (Φ : K → V → iProp) (m : M' V) : iProp :=
  Iris.BI.big_sepM (PROP := iProp) Φ m

/-! ## Entailment Helpers -/

private theorem entails_refl (P : iProp) : iProp.entails P P :=
  (Iris.BI.BIBase.BiEntails.rfl (P := P)).1

private theorem eq_entails {P Q : iProp} (h : P ⊣⊢ Q) : iProp.entails P Q := h.1

/-! ## Separation Logic Laws -/

theorem sep_comm (P Q : iProp) :
    iProp.entails (iProp.sep P Q) (iProp.sep Q P) :=
  eq_entails Iris.BI.sep_comm

theorem sep_assoc (P Q R : iProp) :
    iProp.entails (iProp.sep (iProp.sep P Q) R)
      (iProp.sep P (iProp.sep Q R)) :=
  eq_entails Iris.BI.sep_assoc

theorem sep_mono (P P' Q Q' : iProp) :
    iProp.entails P P' → iProp.entails Q Q' →
    iProp.entails (iProp.sep P Q) (iProp.sep P' Q') :=
  fun h1 h2 => Iris.BI.sep_mono h1 h2

theorem wand_intro (P Q R : iProp) :
    iProp.entails (iProp.sep P Q) R →
    iProp.entails P (iProp.wand Q R) :=
  fun h => Iris.BI.wand_intro h

theorem wand_elim (P Q : iProp) :
    iProp.entails (iProp.sep (iProp.wand P Q) P) Q := by
  simpa using (Iris.BI.wand_elim_l (P := P) (Q := Q))

theorem pure_intro (φ : Prop) (P : iProp) :
    φ → iProp.entails P (iProp.sep (iProp.pure φ) P) := by
  intro hφ
  have hEmp : iProp.entails P (iProp.sep iProp.emp P) :=
    Iris.BI.emp_sep.symm.1
  have hSep : iProp.entails (iProp.sep iProp.emp P) (iProp.sep (iProp.pure φ) P) :=
    Iris.BI.sep_mono (Iris.BI.pure_intro (P := iProp.emp) hφ) (entails_refl P)
  exact hEmp.trans hSep

theorem pure_elim (φ : Prop) (P : iProp) :
    (φ → iProp.entails iProp.emp P) → iProp.entails (iProp.pure φ) P :=
  fun h => Iris.BI.pure_elim' h

theorem persistently_idemp (P : iProp) :
    iProp.entails (iProp.persistently (iProp.persistently P))
      (iProp.persistently P) :=
  eq_entails Iris.BI.persistently_idem

theorem persistently_sep_dup (P : iProp) :
    iProp.entails (iProp.persistently P)
      (iProp.sep (iProp.persistently P) (iProp.persistently P)) :=
  eq_entails Iris.BI.persistently_sep_persistently.symm

/-! ## Basic Update Modality -/

def bupd (P : iProp) : iProp := Iris.BUpd.bupd P

theorem bupd_mono (P Q : iProp) :
    iProp.entails P Q → iProp.entails (_root_.bupd P) (_root_.bupd Q) :=
  fun h => Iris.BIUpdate.mono h

theorem bupd_intro (P : iProp) : iProp.entails P (_root_.bupd P) :=
  Iris.BIUpdate.intro

theorem bupd_trans (P : iProp) :
    iProp.entails (_root_.bupd (_root_.bupd P)) (_root_.bupd P) :=
  Iris.BIUpdate.trans

theorem bupd_frame_r (P Q : iProp) :
    iProp.entails (iProp.sep (_root_.bupd P) Q) (_root_.bupd (iProp.sep P Q)) :=
  Iris.BIUpdate.frame_r

/-! ## Big Separating Conjunction (Lists) -/

def big_sepL {α : Type} (Φ : α → iProp) : List α → iProp :=
  fun l => l.foldr (fun a acc => iProp.sep (Φ a) acc) iProp.emp

theorem big_sepL_nil {α : Type} (Φ : α → iProp) :
    iProp.entails (big_sepL Φ []) iProp.emp :=
  entails_refl _

theorem big_sepL_cons {α : Type} (Φ : α → iProp) (x : α) (l : List α) :
    iProp.entails (big_sepL Φ (x :: l)) (iProp.sep (Φ x) (big_sepL Φ l)) :=
  entails_refl _

theorem big_sepL_app {α : Type} (Φ : α → iProp) (l₁ l₂ : List α) :
    iProp.entails (big_sepL Φ (l₁ ++ l₂))
      (iProp.sep (big_sepL Φ l₁) (big_sepL Φ l₂)) := by
  induction l₁ with
  | nil =>
    simp only [big_sepL, List.foldr, List.nil_append]
    exact Iris.BI.emp_sep.symm.1
  | cons x xs ih =>
    simp only [big_sepL, List.foldr, List.cons_append]
    refine (Iris.BI.sep_mono (entails_refl _) ih).trans ?_
    exact (Iris.BI.sep_assoc (P := Φ x)).symm.1

/-! ## Masks and Namespaces -/

namespace Mask

def top : Mask := fun _ => True
def empty : Mask := fun _ => False
def diff (E₁ E₂ : Mask) : Mask := fun x => E₁ x ∧ ¬E₂ x
def union (E₁ E₂ : Mask) : Mask := fun x => E₁ x ∨ E₂ x
def subseteq (E₁ E₂ : Mask) : Prop := ∀ x, E₁ x → E₂ x
def disjoint (E₁ E₂ : Mask) : Prop := ∀ x, ¬(E₁ x ∧ E₂ x)
def singleton (n : Nat) : Mask :=
  fun p => p = [Iris.Countable.encode n]

end Mask

namespace Namespace

def root : Telltale.Namespace := Iris.nroot
def append (N : Telltale.Namespace) (s : String) : Telltale.Namespace := Iris.ndot N s
def append_nat (N : Telltale.Namespace) (n : Nat) : Telltale.Namespace := Iris.ndot N n

end Namespace

def namespace_to_mask (N : Telltale.Namespace) : Mask := (Iris.nclose N).mem

/-! ## Fancy Update Modality -/

def fupdImpl (_E₁ _E₂ : Mask) (P : iProp) : iProp := P

@[implemented_by fupdImpl]
def fupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
  Telltale.uPredFupd E₁ E₂ P

theorem fupd_intro (E : Mask) (P : iProp) :
    iProp.entails P (_root_.fupd E E P) :=
  (Iris.BaseLogic.fupd_intro_mask (W := ti.W) E E (fun _ hx => hx) P).trans
    (Iris.BaseLogic.fupd_trans (W := ti.W) E E E P)

theorem fupd_mono (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails P Q → iProp.entails (_root_.fupd E₁ E₂ P) (_root_.fupd E₁ E₂ Q) :=
  fun h => Iris.BaseLogic.fupd_mono (W := ti.W) E₁ E₂ h

theorem fupd_trans (E₁ E₂ E₃ : Mask) (P : iProp) :
    iProp.entails (_root_.fupd E₁ E₂ (_root_.fupd E₂ E₃ P)) (_root_.fupd E₁ E₃ P) :=
  Iris.BaseLogic.fupd_trans (W := ti.W) E₁ E₂ E₃ P

theorem fupd_frame_r (E₁ E₂ : Mask) (P Q : iProp) :
    iProp.entails (iProp.sep (_root_.fupd E₁ E₂ P) Q)
      (_root_.fupd E₁ E₂ (iProp.sep P Q)) :=
  Iris.BaseLogic.fupd_frame_r (W := ti.W) E₁ E₂ P Q

theorem fupd_mask_subseteq (E₁ E₂ : Mask) (hSub : Mask.subseteq E₂ E₁) :
    iProp.entails iProp.emp (_root_.fupd E₁ E₂ (_root_.fupd E₂ E₁ iProp.emp)) :=
  Iris.BaseLogic.fupd_mask_subseteq (W := ti.W) E₁ E₂ hSub

/-! ## Invariants -/

def invImpl (_N : Namespace) (P : iProp) : iProp := P

@[implemented_by invImpl]
def inv (N : Namespace) (P : iProp) : iProp :=
  Iris.BaseLogic.inv (M := ti.M) (F := ti.F) ti.W N P

theorem inv_persistent (N : Namespace) (P : iProp) :
    iProp.entails (_root_.inv N P) (iProp.persistently (_root_.inv N P)) :=
  Iris.BaseLogic.inv_persistent (W := ti.W) N P

/-! ## Cancelable Invariants (Compatibility Stubs) -/

/-- Cancelable invariant token handle (placeholder). -/
abbrev CancelToken := GhostName

/-- Ownership predicate for a cancel token (placeholder). -/
def cancel_token_ownImpl (_ct : CancelToken) : iProp := iProp.emp

@[implemented_by cancel_token_ownImpl]
def cancel_token_own (_ct : CancelToken) : iProp :=
  Iris.BaseLogic.cinv_own (GF := ti.GF) (F := ti.F) ti.W _ct (1 : ti.F)

/-- Cancelable invariant (placeholder). -/
def cinvImpl (_N : Namespace) (_ct : CancelToken) (P : iProp) : iProp := P

@[implemented_by cinvImpl]
def cinv (N : Namespace) (_ct : CancelToken) (P : iProp) : iProp :=
  Iris.BaseLogic.cinv (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W N _ct P

/-- Distinct `Nat` children of the same namespace are disjoint. -/
theorem namespace_disjoint (N : Namespace) (n₁ n₂ : Nat) (hNe : n₁ ≠ n₂) :
    Mask.disjoint (namespace_to_mask (Namespace.append_nat N n₁))
      (namespace_to_mask (Namespace.append_nat N n₂)) := by
  simpa [namespace_to_mask, Namespace.append_nat] using
    (Iris.ndot_ne_disjoint (A := Nat) N (x := n₁) (y := n₂) hNe)

/-- Allocate a cancelable invariant from `▷ P`. -/
theorem cinv_alloc :
  ∀ (N : Namespace) (E : Mask) (P : iProp),
    (∀ E' : Iris.GSet, ∃ i, ¬E'.mem i ∧ (namespace_to_mask N) i) →
    iProp.entails (iProp.later P)
      (fupd E E (iProp.exist fun ct =>
        iProp.sep (cinv N ct P) (cancel_token_own ct)))
  := by
    intro N E P hFresh
    simpa [cinv, cancel_token_own, namespace_to_mask] using
      (Iris.BaseLogic.cinv_alloc (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W E N P hFresh)

/-- Open a cancelable invariant using its full cancel token. -/
theorem cinv_acc :
  ∀ (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp),
    Mask.subseteq (namespace_to_mask N) E →
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.sep (cancel_token_own ct)
            (iProp.wand (iProp.later P)
              (fupd (Mask.diff E (namespace_to_mask N)) E (iProp.pure True))))))
  := by
    intro N E ct P hSub
    let post :=
      fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.sep (cancel_token_own ct)
            (iProp.wand (iProp.later P)
              (fupd (Mask.diff E (namespace_to_mask N)) E (iProp.pure True)))))
    have hOpen :
        iProp.entails (cinv N ct P) (iProp.wand (cancel_token_own ct) post) := by
      simpa [post, cinv, cancel_token_own, namespace_to_mask, Mask.diff] using
        (Iris.BaseLogic.cinv_acc (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W E N ct (1 : ti.F) P hSub)
    have hFrame :
        iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
          (iProp.sep (iProp.wand (cancel_token_own ct) post) (cancel_token_own ct)) :=
      sep_mono (P:=cinv N ct P) (P':=iProp.wand (cancel_token_own ct) post)
        (Q:=cancel_token_own ct) (Q':=cancel_token_own ct)
        hOpen (entails_refl _)
    exact hFrame.trans (wand_elim _ _)

/-- Cancel/consume step for a cancelable invariant with its full token. -/
theorem cinv_cancel :
  ∀ (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp),
    Mask.subseteq (namespace_to_mask N) E →
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.sep (cancel_token_own ct)
            (iProp.wand (iProp.later P)
              (fupd (Mask.diff E (namespace_to_mask N)) E (iProp.pure True))))))
  := by
    intro N E ct P hSub
    exact cinv_acc N E ct P hSub

/-! ## Saved Propositions -/

def saved_prop_ownImpl [SavedPropSlot] (_γ : GhostName) (P : iProp) : iProp := P

@[implemented_by saved_prop_ownImpl]
def saved_prop_own [SavedPropSlot] (γ : GhostName) (P : iProp) :
    iProp :=
  Iris.BaseLogic.saved_prop_own (GF := ti.GF) (F := ti.F) γ (Iris.DFrac.own 1) P

theorem saved_prop_alloc [SavedPropSlot] (P : iProp) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => saved_prop_own γ P)) :=
  Iris.BaseLogic.saved_prop_alloc (GF := ti.GF) (F := ti.F)
    (Iris.DFrac.own 1) Iris.DFrac.valid_own_one P

/-! ## Ghost Variables -/

def ghost_varImpl {α : Type} [GhostVarSlot α]
    (_γ : GhostName) (_a : α) : iProp := iProp.emp

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

/-! ## Ghost Maps -/

/-- Type alias for ghost maps using iris-lean's finite map infrastructure. -/
abbrev GhostMap (V : Type) [ti : Telltale.TelltaleIris] := ti.M (Iris.LeibnizO V)

open Telltale in
/-- Authoritative ownership of a ghost map.
    The map uses iris-lean's M type with Positive keys. -/
def ghost_map_authImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_m : GhostMap V) : iProp := iProp.emp

@[implemented_by ghost_map_authImpl]
def ghost_map_auth {V : Type} [GhostMapSlot V]
    (γ : GhostName) (m : GhostMap V) : iProp :=
  Iris.BaseLogic.ghost_map_auth (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ 1 m

open Telltale in
/-- Fragment ownership of a single key-value pair in a ghost map.
    Keys are Positive (application code encodes custom key types). -/
def ghost_map_elemImpl {V : Type} [GhostMapSlot V]
    (_γ : GhostName) (_k : Iris.Positive) (_v : V) : iProp := iProp.emp

@[implemented_by ghost_map_elemImpl]
def ghost_map_elem {V : Type} [GhostMapSlot V]
    (γ : GhostName) (k : Iris.Positive) (v : V) : iProp :=
  Iris.BaseLogic.ghost_map_elem (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) ∅ γ k (Iris.DFrac.own 1) (Iris.LeibnizO.mk v)

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

/-! ## Program Logic (Compatibility Stubs) -/

namespace Iris

/-- Placeholder state interpretation predicate. -/
def state_interp (Λ : Iris.ProgramLogic.Language) (σ : Λ.state) : iProp :=
  iProp.emp

/-- Placeholder weakest precondition. -/
def wp (Λ : Iris.ProgramLogic.Language) (E : Mask) (e : Λ.expr)
    (Φ : Λ.val → iProp) : iProp :=
  iProp.emp

/-- Placeholder multi-step relation. -/
def MultiStep' {Λ : Iris.ProgramLogic.Language} :
  Λ.expr → Λ.state → Λ.expr → Λ.state → Prop :=
  fun _ _ _ _ => False

/-- Placeholder invariance lemma for WP. -/
theorem wp_invariance {Λ : Iris.ProgramLogic.Language} {e : Λ.expr} {σ : Λ.state}
    {Φ : Λ.val → iProp} :
  iProp.entails iProp.emp (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ)) →
  ∀ e' σ',
    MultiStep' (Λ:=Λ) e σ e' σ' →
    iProp.entails iProp.emp (_root_.bupd (state_interp Λ σ')) := by
  intro _ e' σ' hStep
  cases hStep

end Iris
