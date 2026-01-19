import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable

set_option linter.dupNamespace false

/-
The Problem. Coinductive types can represent infinite trees, but we often need
finite representations (e.g., to convert back to inductive types). A coinductive
type is "regular" if it has only finitely many distinct reachable subterms.

The difficulty is defining reachability for M-types and proving closure properties
of reachable sets that support the termination arguments in toInductive.

Solution Structure.
1. Define childRel: one-step child relation via PFunctor.M.dest
2. Define Reachable: reflexive-transitive closure of childRel
3. Define Regular: the reachable set is finite
4. Prove closure lemmas for building regular types from regular children
-/

namespace RumpsteakV2.Coinductive

open Classical

/-! ## Reachability -/

/-- One-step child relation: c is a child of t if c = f(i) for some destructor. -/
def childRel (t c : LocalTypeC) : Prop :=
  ∃ (s : LocalTypeHead) (f : LocalTypeChild s → LocalTypeC) (i : LocalTypeChild s),
    PFunctor.M.dest t = ⟨s, f⟩ ∧ f i = c

/-- The set of subterms reachable from t via childRel. -/
def Reachable (t : LocalTypeC) : Set LocalTypeC :=
  { s | Relation.ReflTransGen childRel t s }

/-- If current is reachable from root and child is a child of current,
    then child is reachable from root. -/
lemma reachable_step {root current child : LocalTypeC}
    (h_current : current ∈ Reachable root) (h_child : childRel current child) :
    child ∈ Reachable root :=
  h_current.tail h_child

/-! ## Regularity -/

/-- A coinductive type is regular if its reachable set is finite.
    Regular types can be converted back to inductive representations. -/
def Regular (t : LocalTypeC) : Prop :=
  Set.Finite (Reachable t)

/-- Alias for regularity, used as a bridge witness in conversions. -/
def HasFiniteRep (t : LocalTypeC) : Prop := Regular t

/-! ## Productivity (observability of all reachable nodes) -/

/-- A coinductive type is productive if every reachable node is observable. -/
def ProductiveC (t : LocalTypeC) : Prop :=
  ∀ s, s ∈ Reachable t → ObservableC s

lemma productive_of_reachable {t s : LocalTypeC}
    (hprod : ProductiveC t) (hs : s ∈ Reachable t) : ProductiveC s := by
  intro u hu
  have : u ∈ Reachable t := hs.trans hu
  exact hprod _ this

/-! ## Closed Sets -/

/-- A finite set is closed under children if it contains all children of members. -/
def IsClosedSet (s : Finset LocalTypeC) : Prop :=
  ∀ x ∈ s, ∀ c, childRel x c → c ∈ s

/-- The finite reachable set is closed under children. -/
lemma reachable_is_closed_set (t : LocalTypeC) (h : Regular t) :
    IsClosedSet (Set.Finite.toFinset h) := by
  intro s hs c hchild
  have hs' : s ∈ Reachable t := (Set.Finite.mem_toFinset h).1 hs
  have hc' : c ∈ Reachable t := reachable_step hs' hchild
  exact (Set.Finite.mem_toFinset h).2 hc'

/-- Membership in a closed set propagates to children. -/
lemma mem_of_closed_child {s : Finset LocalTypeC} {x c : LocalTypeC}
    (h_closed : IsClosedSet s) (hx : x ∈ s) (hc : childRel x c) : c ∈ s :=
  h_closed _ hx _ hc

/-! ## Finset Helpers -/

/-- Inserting a member preserves subset. -/
lemma subset_insert_of_mem {α : Type} [DecidableEq α] {s v : Finset α} {x : α}
    (h1 : x ∈ s) (h2 : v ⊆ s) : Insert.insert x v ⊆ s :=
  Finset.insert_subset h1 h2

/-- Cardinality decreases when inserting a new element from a finite superset. -/
lemma card_sub_insert_lt {α : Type} [DecidableEq α] {s v : Finset α} {x : α}
    (h1 : x ∈ s) (h2 : x ∉ v) (h3 : v ⊆ s) :
    s.card - (Insert.insert x v).card < s.card - v.card := by
  have h_card_insert : (insert x v).card = v.card + 1 :=
    Finset.card_insert_of_notMem h2
  have hsub : v ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨h3, by aesop⟩
  exact Nat.sub_lt_sub_left (by linarith [Finset.card_lt_card hsub]) (by linarith)

end RumpsteakV2.Coinductive
