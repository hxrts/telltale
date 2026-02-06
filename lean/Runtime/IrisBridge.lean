import Iris.Instances.IProp.Instance
import Iris.BaseLogic.Lib.Wsat
import Iris.BaseLogic.Lib.FancyUpdates
import Iris.BaseLogic.Lib.Invariants
import Iris.BaseLogic.Lib.CancelableInvariants
import Iris.BaseLogic.Lib.GhostMap
import Iris.BaseLogic.Lib.GhostVar
import Iris.BaseLogic.Lib.SavedProp
import Iris.BaseLogic.Lib.AuthOwn
import Iris.BaseLogic.Lib.GenHeap
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Adequacy

/-!
# Telltale–Iris Bridge

Single facade for all iris-lean imports. Provides:

1. `TelltaleIris` typeclass bundling abstract Iris parameters
2. Type aliases (`iProp`, `GhostName`, `Mask`, `Namespace`)
3. Dispatch typeclasses (`GhostMapSlot`, `GhostVarSlot`, `SavedPropSlot`)
4. Separation logic, ghost state, update modalities, invariants, WP, and heap primitives

Usage: Import `Runtime.IrisBridge` and add `variable [Telltale.TelltaleIris]`.
The Compat layer (`Runtime.Compat`) re-exports this for downstream modules.
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

/-! ## Dispatch Typeclasses -/

class GhostMapSlot (K V : Type) where
  encode : K → Positive
  encode_inj : Function.Injective encode
  instOFE : OFE (LeibnizO V)
  instDiscrete : OFE.Discrete (LeibnizO V)
  instLeibniz : OFE.Leibniz (LeibnizO V)
  instElemG : ElemG ti.GF (GhostMapF ti.GF ti.M ti.F (LeibnizO V))

attribute [instance] GhostMapSlot.instOFE
attribute [instance] GhostMapSlot.instDiscrete
attribute [instance] GhostMapSlot.instLeibniz
attribute [instance] GhostMapSlot.instElemG

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

/-! ## Auth Wrapper

iris-lean defines `Auth` at root level, so we place our shim Auth here.
When retiring the axiom, downstream code should use `Telltale.Auth`. -/

structure Auth (α : Type) where
  inner : α
  isAuth : Bool

namespace Auth
def auth {α : Type} (a : α) : Auth α := ⟨a, true⟩
def frag {α : Type} (b : α) : Auth α := ⟨b, false⟩
end Auth

/-! ## Internal Aliases -/

noncomputable def wsatGS : WsatGS ti.GF := ti.W

noncomputable def uPredFupd (E₁ E₂ : Mask) (P : iProp) : iProp :=
  Iris.BaseLogic.uPred_fupd
    (GF := ti.GF) (M := ti.M) (F := ti.F) ti.W E₁ E₂ P

end Telltale

/-! ==============================================================
    Part 2: Adapter Definitions (root namespace)
    ==============================================================

    Every definition below matches an axiom signature in the shim files.
    Proved where iris-lean provides the theorem; `sorry` otherwise.
-/

-- Export core types to root namespace.
export Telltale (iProp GhostName GhostMapSlot GhostVarSlot SavedPropSlot)

-- Mask and Namespace are exported separately to control ambiguity.
export Telltale (Mask Namespace)

-- Convenience alias for backwards compatibility (avoids collision with iris-lean's root Auth)
abbrev TAuth := Telltale.Auth

namespace TAuth
export Telltale.Auth (auth frag)
end TAuth

variable [ti : Telltale.TelltaleIris]

/-! ## iProp Connectives (ResourceAlgebra.lean lines 14–23) -/

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

/-! ## Entailment Helpers -/

private theorem entails_refl (P : iProp) : iProp.entails P P :=
  (Iris.BI.BIBase.BiEntails.rfl (P := P)).1

private theorem eq_entails {P Q : iProp} (h : P ⊣⊢ Q) : iProp.entails P Q := h.1

/-! ## Separation Logic Laws (ResourceAlgebra.lean lines 26–44) -/

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

/-! ## Ghost Ownership Typeclasses (ResourceAlgebra.lean lines 49–52) -/

class Valid (α : Type) where valid : α → Prop
class Included (α : Type) where included : α → α → Prop
class FramePreservingUpdate (α : Type) where fpu : α → α → Prop
class LocalUpdate (α : Type) where lu : (α × α) → (α × α) → Prop

/-- Ghost ownership (polymorphic stub). -/
noncomputable def own (γ : GhostName) {α : Type} (a : α) : iProp := sorry

/-! ## Basic Update Modality (ResourceAlgebra.lean lines 58–70) -/

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

noncomputable def own_update (γ : GhostName) {α : Type} (a b : α)
    [FramePreservingUpdate α] :
    iProp.entails (own γ a) (_root_.bupd (own γ b)) := sorry

noncomputable def own_alloc {α : Type} (a : α) [Valid α] :
    iProp.entails iProp.emp (_root_.bupd (iProp.exist fun γ => own γ a)) := sorry

/-! ## Auth RA (ResourceAlgebra.lean lines 74–84)

Note: iris-lean defines `Auth` at root level, so the shim Auth is at
`Telltale.Auth`. When retiring the axiom, downstream code should use
`Telltale.Auth.auth`/`Telltale.Auth.frag` (or `open Telltale` selectively). -/

noncomputable def auth_frag_included {α : Type} (γ : GhostName) (a b : α)
    [Included α] :
    iProp.entails
      (iProp.sep (own γ (Telltale.Auth.auth a)) (own γ (Telltale.Auth.frag b)))
      (iProp.pure (Included.included b a)) := sorry

noncomputable def auth_update {α : Type} (γ : GhostName) (a a' b b' : α)
    [LocalUpdate α] :
    iProp.entails
      (iProp.sep (own γ (Telltale.Auth.auth a)) (own γ (Telltale.Auth.frag b)))
      (_root_.bupd (iProp.sep (own γ (Telltale.Auth.auth a'))
        (own γ (Telltale.Auth.frag b')))) := sorry

/-! ## Ghost Map (ResourceAlgebra.lean lines 88–112) -/

structure GMap (K V : Type) where
  entries : List (K × V)

namespace GMap
variable {K V : Type}

def lookup [BEq K] (m : GMap K V) (k : K) : Option V :=
  (m.entries.find? (fun p => p.1 == k)).map Prod.snd

def insert [BEq K] (m : GMap K V) (k : K) (v : V) : GMap K V :=
  ⟨(k, v) :: m.entries.filter (fun p => !(p.1 == k))⟩

def delete [BEq K] (m : GMap K V) (k : K) : GMap K V :=
  ⟨m.entries.filter (fun p => !(p.1 == k))⟩

def empty : GMap K V := ⟨[]⟩

instance : EmptyCollection (GMap K V) := ⟨GMap.empty⟩
end GMap

noncomputable def ghost_map_auth (γ : GhostName) {K V : Type}
    (m : GMap K V) : iProp := sorry

noncomputable def ghost_map_elem (γ : GhostName) {K V : Type}
    (k : K) (v : V) : iProp := sorry

theorem ghost_map_alloc {K V : Type} [BEq K] [DecidableEq K] (m : GMap K V) :
    iProp.entails iProp.emp (_root_.bupd (iProp.exist fun γ =>
      iProp.sep (ghost_map_auth γ m)
        (iProp.forall fun k => iProp.forall fun v =>
          iProp.wand (iProp.pure (GMap.lookup m k = some v))
            (ghost_map_elem γ k v)))) := sorry

theorem ghost_map_lookup {K V : Type} [BEq K] [DecidableEq K]
    (γ : GhostName) (k : K) (v : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (iProp.pure (GMap.lookup m k = some v)) := sorry

theorem ghost_map_insert {K V : Type} [BEq K] [DecidableEq K]
    (γ : GhostName) (k : K) (v : V) (m : GMap K V)
    (hNone : GMap.lookup m k = none) :
    iProp.entails (ghost_map_auth γ m)
      (_root_.bupd (iProp.sep (ghost_map_auth γ (GMap.insert m k v))
        (ghost_map_elem γ k v))) := sorry

theorem ghost_map_update {K V : Type} [BEq K] [DecidableEq K]
    (γ : GhostName) (k : K) (v v' : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (iProp.sep (ghost_map_auth γ (GMap.insert m k v'))
        (ghost_map_elem γ k v'))) := sorry

theorem ghost_map_delete {K V : Type} [BEq K] [DecidableEq K]
    (γ : GhostName) (k : K) (v : V) (m : GMap K V) :
    iProp.entails (iProp.sep (ghost_map_auth γ m) (ghost_map_elem γ k v))
      (_root_.bupd (ghost_map_auth γ (GMap.delete m k))) := sorry

/-! ## Big Separating Conjunction (ResourceAlgebra.lean lines 116–129) -/

noncomputable def big_sepL {α : Type} (Φ : α → iProp) : List α → iProp :=
  fun l => l.foldr (fun a acc => iProp.sep (Φ a) acc) iProp.emp

noncomputable def big_sepM {K V : Type} (Φ : K → V → iProp) :
    GMap K V → iProp :=
  fun m => m.entries.foldr (fun ⟨k, v⟩ acc => iProp.sep (Φ k v) acc) iProp.emp

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
    -- big_sepL Φ [] = emp, so emp ∗ big_sepL Φ l₂ ⊣⊢ big_sepL Φ l₂
    simp only [big_sepL, List.foldr, List.nil_append]
    exact Iris.BI.emp_sep.symm.1
  | cons x xs ih =>
    -- big_sepL Φ ((x :: xs) ++ l₂) = Φ x ∗ big_sepL Φ (xs ++ l₂)
    simp only [big_sepL, List.foldr, List.cons_append]
    -- Need: Φ x ∗ big_sepL Φ (xs ++ l₂) ⊢ (Φ x ∗ big_sepL Φ xs) ∗ big_sepL Φ l₂
    -- By ih: big_sepL Φ (xs ++ l₂) ⊢ big_sepL Φ xs ∗ big_sepL Φ l₂
    -- So: Φ x ∗ (big_sepL Φ xs ∗ big_sepL Φ l₂) ⊢ (Φ x ∗ big_sepL Φ xs) ∗ big_sepL Φ l₂
    -- This is sep_assoc.symm
    refine (Iris.BI.sep_mono (entails_refl _) ih).trans ?_
    exact (Iris.BI.sep_assoc (P := Φ x)).symm.1

theorem big_sepM_insert {K V : Type} [BEq K] [DecidableEq K]
    (Φ : K → V → iProp) (m : GMap K V) (k : K) (v : V)
    (hNone : GMap.lookup m k = none) :
    iProp.entails (big_sepM Φ (GMap.insert m k v))
      (iProp.sep (Φ k v) (big_sepM Φ m)) := sorry

theorem big_sepM_lookup {K V : Type} [BEq K] [DecidableEq K]
    (Φ : K → V → iProp) (m : GMap K V) (k : K) (v : V)
    (hLook : GMap.lookup m k = some v) :
    iProp.entails (big_sepM Φ m)
      (iProp.sep (Φ k v) (big_sepM Φ (GMap.delete m k))) := sorry

/-! ## Masks and Namespaces (Invariants.lean lines 15–30) -/

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

theorem namespace_disjoint (N₁ N₂ : Telltale.Namespace) (h : N₁ ≠ N₂) :
    Mask.disjoint (namespace_to_mask N₁) (namespace_to_mask N₂) := sorry

/-! ## Fancy Update Modality (Invariants.lean lines 34–43) -/

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

/-! ## Invariants (Invariants.lean lines 47–56) -/

noncomputable def inv (N : Namespace) (P : iProp) : iProp :=
  Iris.BaseLogic.inv (M := ti.M) (F := ti.F) ti.W N P

theorem inv_persistent (N : Namespace) (P : iProp) :
    iProp.entails (_root_.inv N P) (iProp.persistently (_root_.inv N P)) :=
  Iris.BaseLogic.inv_persistent (W := ti.W) N P

theorem inv_alloc (N : Namespace) (E : Mask) (P : iProp) :
    iProp.entails (iProp.later P) (_root_.fupd E E (_root_.inv N P)) := by
  -- iris-lean requires a freshness hypothesis for namespace allocation.
  -- Namespaces contain infinitely many names, so fresh names always exist.
  -- The proof requires GSet infrastructure not exposed here.
  sorry

theorem inv_acc (N : Namespace) (E : Mask) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (_root_.inv N P) (_root_.fupd E (Mask.diff E (namespace_to_mask N))
      (iProp.sep (iProp.later P)
        (iProp.wand (iProp.later P)
          (_root_.fupd (Mask.diff E (namespace_to_mask N)) E iProp.emp)))) := by
  -- iris-lean's inv_acc returns `pure True` in the closing wand, we return `emp`.
  -- The conversion requires showing `pure True ⊣⊢ emp`.
  sorry

/-! ## Cancelable Invariants (Invariants.lean lines 60–77) -/

def CancelToken : Type := GhostName

/-- Cancelable invariant ownership token (full ownership).
    Requires `ElemG GF (constOF CinvR)` instance not yet in TelltaleIris. -/
noncomputable def cancel_token_own (ct : CancelToken) : iProp := sorry

/-- Cancelable invariant.
    Requires `ElemG GF (constOF CinvR)` instance not yet in TelltaleIris. -/
noncomputable def cinv (N : Namespace) (ct : CancelToken) (P : iProp) : iProp := sorry

theorem cinv_persistent (N : Namespace) (ct : CancelToken) (P : iProp) :
    iProp.entails (_root_.cinv N ct P)
      (iProp.persistently (_root_.cinv N ct P)) := sorry

theorem cinv_alloc (N : Namespace) (E : Mask) (P : iProp) :
    iProp.entails (iProp.later P) (_root_.fupd E E (iProp.exist fun ct =>
      iProp.sep (_root_.cinv N ct P) (cancel_token_own ct))) := by
  -- iris-lean requires a freshness hypothesis for namespace allocation.
  -- The proof requires GSet infrastructure not exposed here.
  sorry

theorem cinv_acc (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (_root_.cinv N ct P)
      (_root_.fupd E (Mask.diff E (namespace_to_mask N))
        (iProp.sep (iProp.later P)
          (iProp.wand (iProp.later P)
            (_root_.fupd (Mask.diff E (namespace_to_mask N)) E iProp.emp)))) := by
  -- cinv_acc in iris-lean takes cinv and cinv_own separately via wand.
  -- Our signature bundles them. We need to adapt the signature.
  -- For now, use sorry as the signature adaptation is non-trivial.
  sorry

theorem cinv_cancel (N : Namespace) (E : Mask) (ct : CancelToken) (P : iProp)
    (hSub : Mask.subseteq (namespace_to_mask N) E) :
    iProp.entails (iProp.sep (_root_.cinv N ct P) (cancel_token_own ct))
      (_root_.fupd E (Mask.diff E (namespace_to_mask N)) (iProp.later P)) := by
  -- iris-lean's cinv_cancel is via wand, our signature uses sep.
  -- We need: cinv ∗ cinv_own ⊢ |={E,E∖N}=> ▷P
  -- iris-lean gives: cinv ⊢ cinv_own -∗ |={E,E∖N}=> (▷P ∗ cinv_own ∗ (▷P -∗ |={E∖N,E}=> emp))
  -- This requires extracting the first component and discarding the rest.
  sorry

/-! ## Saved Propositions (SavedProp.lean lines 15–22) -/

/-- Saved proposition with full ownership (no fractional permissions exposed). -/
noncomputable def saved_prop_own [SavedPropSlot] (γ : GhostName) (P : iProp) :
    iProp :=
  Iris.BaseLogic.saved_prop_own (GF := ti.GF) (F := ti.F) γ (Iris.DFrac.own 1) P

theorem saved_prop_alloc [SavedPropSlot] (P : iProp) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => saved_prop_own γ P)) :=
  Iris.BaseLogic.saved_prop_alloc (GF := ti.GF) (F := ti.F)
    (Iris.DFrac.own 1) Iris.DFrac.valid_own_one P

theorem saved_prop_agree [SavedPropSlot] (γ : GhostName) (P Q : iProp) :
    iProp.entails (iProp.sep (saved_prop_own γ P) (saved_prop_own γ Q))
      (iProp.sep (iProp.later (iProp.wand P Q))
        (iProp.later (iProp.wand Q P))) := by
  -- iris-lean gives UPred.eq P Q (internal equality), which is stronger
  -- than ▷(P -∗ Q) ∗ ▷(Q -∗ P). We need to derive the wands from equality.
  -- For now, use sorry as the conversion requires internal equality infrastructure.
  sorry

theorem saved_prop_persistent [SavedPropSlot] (γ : GhostName) (P : iProp) :
    iProp.entails (saved_prop_own γ P)
      (iProp.persistently (saved_prop_own γ P)) := by
  -- Our saved_prop_own uses DFrac.own 1, not DFrac.discard, so it's not
  -- automatically persistent. We need to go through bupd to discard the fraction.
  -- The proper fix is to use discarded fractions for persistence.
  sorry

/-! ## Ghost Variables (SavedProp.lean lines 26–32) -/

/-- Ghost variable with full ownership (no fractional permissions exposed). -/
noncomputable def ghost_var {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a : α) : iProp :=
  Iris.BaseLogic.ghost_var (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.DFrac.own 1) (Iris.LeibnizO.mk a)

theorem ghost_var_alloc {α : Type} [GhostVarSlot α] (a : α) :
    iProp.entails iProp.emp
      (_root_.bupd (iProp.exist fun γ => ghost_var γ a)) := by
  -- The type mismatch between our API and iris-lean's requires wrapping/unwrapping.
  -- iris-lean returns ∃ γ, ghost_var γ (LeibnizO.mk a), we return ∃ γ, ghost_var γ a.
  -- These are definitionally equal given our definition of ghost_var.
  exact Iris.BaseLogic.ghost_var_alloc (GF := ti.GF) (F := ti.F)
    (A := Iris.LeibnizO α) (Iris.LeibnizO.mk a)

theorem ghost_var_agree {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a b : α) :
    iProp.entails (iProp.sep (ghost_var γ a) (ghost_var γ b))
      (iProp.pure (a = b)) := by
  -- iris-lean proves LeibnizO.mk a = LeibnizO.mk b, we need a = b
  have h := Iris.BaseLogic.ghost_var_agree (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.DFrac.own 1) (Iris.DFrac.own 1) (Iris.LeibnizO.mk a) (Iris.LeibnizO.mk b)
  refine h.trans ?_
  exact Iris.BI.pure_mono (fun heq => Iris.LeibnizO.mk.injEq a b ▸ heq)

theorem ghost_var_update {α : Type} [GhostVarSlot α]
    (γ : GhostName) (a b : α) :
    iProp.entails (ghost_var γ a) (_root_.bupd (ghost_var γ b)) :=
  Iris.BaseLogic.ghost_var_update (GF := ti.GF) (F := ti.F) (A := Iris.LeibnizO α)
    γ (Iris.LeibnizO.mk a) (Iris.LeibnizO.mk b)

/-! ## Language and WP (WeakestPre.lean) -/

namespace Iris

universe u

class Language (Λ : Type u) where
  expr : Type
  val : Type
  state : Type
  of_val : val → expr
  to_val : expr → Option val
  prim_step : expr → state → List (expr × state × List expr)

class EctxLanguage (Λ : Type u) extends Language Λ where
  ectx : Type
  empty_ectx : ectx
  comp_ectx : ectx → ectx → ectx
  fill : ectx → expr → expr
  decomp : expr → ectx × expr

noncomputable def wp (Λ : Type u) [Language Λ] (E : Mask) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) : iProp := sorry

noncomputable def state_interp (Λ : Type u) [Language Λ]
    (σ : Language.state Λ) : iProp := sorry

theorem wp_value (Λ : Type u) [Language Λ] (E : Mask)
    (v : Language.val Λ) (Φ : Language.val Λ → iProp) :
    iProp.entails (Φ v) (wp Λ E (Language.of_val v) Φ) := sorry

theorem wp_strong_mono (Λ : Type u) [Language Λ] (E₁ E₂ : Mask)
    (e : Language.expr Λ)
    (Φ Ψ : Language.val Λ → iProp) (hSub : Mask.subseteq E₁ E₂) :
    iProp.entails
      (iProp.sep (wp Λ E₁ e Φ)
        (iProp.forall fun v => iProp.wand (Φ v) (_root_.fupd E₂ E₂ (Ψ v))))
      (wp Λ E₂ e Ψ) := sorry

theorem wp_bind (Λ : Type u) [EctxLanguage Λ] (E : Mask)
    (K : EctxLanguage.ectx Λ) (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) :
    iProp.entails
      (wp Λ E e (fun v => wp Λ E (EctxLanguage.fill K (Language.of_val v)) Φ))
      (wp Λ E (EctxLanguage.fill K e) Φ) := sorry

theorem wp_frame_l (Λ : Type u) [Language Λ] (E : Mask)
    (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp) (R : iProp) :
    iProp.entails (iProp.sep R (wp Λ E e Φ))
      (wp Λ E e (fun v => iProp.sep R (Φ v))) := sorry

theorem wp_fupd (Λ : Type u) [Language Λ] (E : Mask)
    (e : Language.expr Λ) (Φ : Language.val Λ → iProp) :
    iProp.entails (wp Λ E e (fun v => _root_.fupd E E (Φ v)))
      (wp Λ E e Φ) := sorry

theorem wp_lift_step (Λ : Type u) [Language Λ] (E : Mask)
    (e : Language.expr Λ)
    (Φ : Language.val Λ → iProp)
    (hNotVal : Language.to_val e = none) :
    iProp.entails
      (iProp.forall fun σ =>
        iProp.wand (state_interp Λ σ)
          (_root_.fupd E Mask.empty
            (iProp.sep
              (iProp.pure (Language.prim_step e σ ≠ []))
              (iProp.forall fun eσefs =>
                iProp.wand
                  (iProp.pure (eσefs ∈ Language.prim_step e σ))
                  (_root_.fupd Mask.empty E
                    (iProp.sep (state_interp Λ eσefs.2.1)
                      (iProp.sep (wp Λ E eσefs.1 Φ)
                        (big_sepL
                          (fun e' => wp Λ Mask.top e' (fun _ => iProp.emp))
                          eσefs.2.2))))))))
      (wp Λ E e Φ) := sorry

/-! ## Adequacy -/

def MultiStep {Λ : Type u} [Language Λ] :
    Language.expr Λ → Language.state Λ → Language.val Λ → Language.state Λ → Prop := sorry

def MultiStep' {Λ : Type u} [Language Λ] :
    Language.expr Λ → Language.state Λ → Language.expr Λ → Language.state Λ → Prop := sorry

theorem wp_adequacy (Λ : Type u) [Language Λ]
    (e : Language.expr Λ) (σ : Language.state Λ)
    (Φ : Language.val Λ → iProp) (φ : Language.val Λ → Prop)
    (hWP : iProp.entails iProp.emp
      (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ)))
    (hPost : ∀ v, iProp.entails (Φ v) (iProp.pure (φ v))) :
    ∀ v σ', MultiStep e σ v σ' → φ v := sorry

theorem wp_invariance (Λ : Type u) [Language Λ]
    (e : Language.expr Λ) (σ : Language.state Λ)
    (Φ : Language.val Λ → iProp)
    (hWP : iProp.entails iProp.emp
      (iProp.wand (state_interp Λ σ) (wp Λ Mask.top e Φ))) :
    ∀ e' σ', MultiStep' e σ e' σ' →
      iProp.entails iProp.emp (_root_.bupd (state_interp Λ σ')) := sorry

end Iris

/-! ## Generalized Heap (GenHeap.lean) -/

noncomputable def HeapLookup {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Option (Iris.Language.val Λ) := sorry

noncomputable def HeapInsert {Λ : Type} [Iris.Language Λ] :
    Iris.Language.state Λ → Nat → Iris.Language.val Λ → Iris.Language.state Λ := sorry

noncomputable def pointsto {Λ : Type} [Iris.Language Λ]
    (l : Nat) (v : Iris.Language.val Λ) : iProp := sorry

theorem gen_heap_alloc {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) (hFresh : HeapLookup σ l = none) :
    iProp.entails (Iris.state_interp Λ σ)
      (_root_.bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v))
        (pointsto l v))) := sorry

theorem gen_heap_valid {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (iProp.pure (HeapLookup σ l = some v)) := sorry

theorem gen_heap_update {Λ : Type} [Iris.Language Λ] (σ : Iris.Language.state Λ)
    (l : Nat) (v v' : Iris.Language.val Λ) :
    iProp.entails (iProp.sep (Iris.state_interp Λ σ) (pointsto l v))
      (_root_.bupd (iProp.sep (Iris.state_interp Λ (HeapInsert σ l v'))
        (pointsto l v'))) := sorry
