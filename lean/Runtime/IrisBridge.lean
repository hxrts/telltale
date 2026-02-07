import Iris.Instances.IProp.Instance
import Iris.BaseLogic.Lib.Wsat
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.BaseLogic.Lib.Invariants
import Iris.BI.BigOp
import Iris.BaseLogic.Lib.GhostVar
import Iris.BaseLogic.Lib.GhostMap
import Iris.BaseLogic.Lib.SavedProp
import Iris.ProgramLogic.Language

/-!
# Telltale–Iris Bridge

Thin facade for iris-lean imports. Provides only what iris-lean actually exports.

1. `TelltaleIris` typeclass bundling abstract Iris parameters
2. Type aliases (`iProp`, `GhostName`, `Mask`, `Namespace`)
3. Separation logic laws, update modalities, invariants
4. Ghost variables, ghost maps, and saved propositions

Usage: Import `Runtime.IrisBridge` and add `variable [Telltale.TelltaleIris]`.
-/

set_option autoImplicit false

/-! ==============================================================
    Part 1: Parameter Bundle and Type Aliases (namespace Telltale)
    ============================================================== -/

namespace Telltale

open Iris Iris.Algebra Iris.Std Iris.BI Iris.BaseLogic COFE

/-! ## Parameter Bundle -/

class TelltaleIris where
  GF : BundledGFunctors
  M : Type _ → Type _
  F : Type _
  instUFraction : UFraction F
  instFiniteMap : FiniteMap Positive M
  instFiniteMapLaws : FiniteMapLaws Positive M
  instHeapFiniteMap : HeapFiniteMap Positive M
  instElemG_CoPsetDisj : ElemG GF (COFE.constOF CoPsetDisj)
  instElemG_GSetDisj : ElemG GF (COFE.constOF GSetDisj)
  instElemG_Inv : ElemG GF (InvF GF M F)
  W : WsatGS GF

attribute [instance] TelltaleIris.instUFraction
attribute [instance] TelltaleIris.instFiniteMap
attribute [instance] TelltaleIris.instFiniteMapLaws
attribute [instance] TelltaleIris.instHeapFiniteMap
attribute [instance] TelltaleIris.instElemG_CoPsetDisj
attribute [instance] TelltaleIris.instElemG_GSetDisj
attribute [instance] TelltaleIris.instElemG_Inv

/-! ## Core Type Aliases -/

variable [ti : TelltaleIris]

abbrev iProp : Type _ := IProp ti.GF
abbrev GhostName := GName
abbrev Mask := Iris.Set Positive
abbrev Namespace := Iris.Namespace

/-! ## Dispatch Typeclasses for Ghost State -/

class GhostVarSlot (α : Type) where
  instOFE : OFE (LeibnizO α)
  instDiscrete : OFE.Discrete (LeibnizO α)
  instLeibniz : OFE.Leibniz (LeibnizO α)
  instElemG : ElemG ti.GF (GhostVarF ti.F (LeibnizO α))

attribute [instance] GhostVarSlot.instOFE
attribute [instance] GhostVarSlot.instDiscrete
attribute [instance] GhostVarSlot.instLeibniz
attribute [instance] GhostVarSlot.instElemG

class SavedPropSlot where
  instElemG : ElemG ti.GF (SavedPropF ti.GF ti.F)

attribute [instance] SavedPropSlot.instElemG

/-- Slot for ghost maps with value type V.
    Keys are Positive (iris-lean's key type).
    Application code encodes custom key types to Positive. -/
class GhostMapSlot (V : Type) where
  instOFE : OFE (LeibnizO V)
  instDiscrete : OFE.Discrete (LeibnizO V)
  instLeibniz : OFE.Leibniz (LeibnizO V)
  instElemG : ElemG ti.GF (GhostMapF ti.GF ti.M ti.F (LeibnizO V))

attribute [instance] GhostMapSlot.instOFE
attribute [instance] GhostMapSlot.instDiscrete
attribute [instance] GhostMapSlot.instLeibniz
attribute [instance] GhostMapSlot.instElemG

/-! ## Internal Aliases -/

noncomputable def wsatGS : WsatGS ti.GF := ti.W

noncomputable def uPredFupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
  Iris.BaseLogic.uPred_fupd
    (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W E₁ E₂ P

end Telltale

/-! ==============================================================
    Part 2: Exports to Root Namespace
    ============================================================== -/

export Telltale (iProp GhostName GhostVarSlot GhostMapSlot SavedPropSlot)
export Iris (Positive)
export Telltale (Mask Namespace)

variable [ti : Telltale.TelltaleIris]

/-! ## iProp Connectives -/

namespace iProp

noncomputable def entails (P Q : iProp) : Prop := @Iris.BI.BIBase.Entails _ _ P Q
noncomputable def emp : iProp := @Iris.BI.BIBase.emp _ _
noncomputable def sep (P Q : iProp) : iProp := @Iris.BI.BIBase.sep _ _ P Q
noncomputable def wand (P Q : iProp) : iProp := @Iris.BI.BIBase.wand _ _ P Q
noncomputable def pure (φ : Prop) : iProp := @Iris.BI.BIBase.pure _ _ φ
noncomputable def later (P : iProp) : iProp := @Iris.BI.BIBase.later _ _ P
noncomputable def persistently (P : iProp) : iProp := @Iris.BI.BIBase.persistently _ _ P
noncomputable def «exist» {α : Type} (Φ : α → iProp) : iProp :=
  @Iris.BI.BIBase.«exists» _ _ α Φ
noncomputable def «forall» {α : Type} (Φ : α → iProp) : iProp :=
  @Iris.BI.BIBase.«forall» _ _ α Φ

end iProp

/-! ## Big Separation over Maps -/

noncomputable def big_sepM {K : Type _} {V : Type _} {M' : Type _ → Type _}
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

noncomputable def bupd (P : iProp) : iProp := Iris.BUpd.bupd P

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

noncomputable def big_sepL {α : Type} (Φ : α → iProp) : List α → iProp :=
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

noncomputable def fupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
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

noncomputable def inv (N : Namespace) (P : iProp) : iProp :=
  Iris.BaseLogic.inv (M := ti.M) (F := ti.F) ti.W N P

theorem inv_persistent (N : Namespace) (P : iProp) :
    iProp.entails (_root_.inv N P) (iProp.persistently (_root_.inv N P)) :=
  Iris.BaseLogic.inv_persistent (W := ti.W) N P

/-! ## Cancelable Invariants (Compatibility Stubs) -/

/-- Cancelable invariant token handle (placeholder). -/
abbrev CancelToken := GhostName

/-- Ownership predicate for a cancel token (placeholder). -/
axiom cancel_token_own : CancelToken → iProp

/-- Cancelable invariant (placeholder). -/
axiom cinv : Namespace → CancelToken → iProp → iProp

/-- Namespaces for cancelable invariants are disjoint (placeholder). -/
axiom namespace_disjoint :
  ∀ N₁ N₂ : Namespace, N₁ ≠ N₂ →
    Mask.disjoint (namespace_to_mask N₁) (namespace_to_mask N₂)

/-- Allocate a cancelable invariant (placeholder). -/
axiom cinv_alloc :
  ∀ (N : Namespace) (E : Mask) (P : iProp),
    iProp.entails (iProp.later P)
      (fupd E E (iProp.exist fun ct =>
        iProp.sep (cinv N ct P) (cancel_token_own ct)))

/-- Open a cancelable invariant (placeholder). -/
axiom cinv_acc :
  ∀ (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp),
    Mask.subseteq (namespace_to_mask N) E →
    iProp.entails (cinv N ct P)
      (fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.wand (iProp.later P)
            (fupd (Mask.diff E (namespace_to_mask N)) E iProp.emp))))

/-- Cancel a cancelable invariant (placeholder). -/
axiom cinv_cancel :
  ∀ (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp),
    Mask.subseteq (namespace_to_mask N) E →
    iProp.entails (iProp.sep (cinv N ct P) (cancel_token_own ct))
      (fupd E (Mask.diff E (namespace_to_mask N)) (iProp.later P))

/-! ## Saved Propositions -/

noncomputable def saved_prop_own [SavedPropSlot] (γ : GhostName) (P : iProp) :
    iProp :=
  Iris.BaseLogic.saved_prop_own (GF := ti.GF) (F := ti.F) γ (Iris.DFrac.own 1) P

theorem saved_prop_alloc [SavedPropSlot] (P : iProp) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => saved_prop_own γ P)) :=
  Iris.BaseLogic.saved_prop_alloc (GF := ti.GF) (F := ti.F)
    (Iris.DFrac.own 1) Iris.DFrac.valid_own_one P

/-! ## Ghost Variables -/

noncomputable def ghost_var {α : Type} [GhostVarSlot α]
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
noncomputable def ghost_map_auth {V : Type} [GhostMapSlot V]
    (γ : GhostName) (m : GhostMap V) : iProp :=
  Iris.BaseLogic.ghost_map_auth (GF := ti.GF) (M := ti.M) (F := ti.F)
    (V := Iris.LeibnizO V) γ 1 m

open Telltale in
/-- Fragment ownership of a single key-value pair in a ghost map.
    Keys are Positive (application code encodes custom key types). -/
noncomputable def ghost_map_elem {V : Type} [GhostMapSlot V]
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
axiom state_interp (Λ : Iris.ProgramLogic.Language) (σ : Λ.state) : iProp

/-- Placeholder weakest precondition. -/
axiom wp (Λ : Iris.ProgramLogic.Language) (E : Mask) (e : Λ.expr)
    (Φ : Λ.val → iProp) : iProp

/-- Placeholder multi-step relation. -/
axiom MultiStep' {Λ : Iris.ProgramLogic.Language} :
  Λ.expr → Λ.state → Λ.expr → Λ.state → Prop

/-- Placeholder invariance lemma for WP. -/
axiom wp_invariance {Λ : Iris.ProgramLogic.Language} {e : Λ.expr} {σ : Λ.state}
    {Φ : Λ.val → iProp} :
  iProp.entails iProp.emp (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ)) →
  ∀ e' σ',
    MultiStep' (Λ:=Λ) e σ e' σ' →
    iProp.entails iProp.emp (_root_.bupd (state_interp Λ σ'))

end Iris
