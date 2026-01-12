import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC

set_option linter.dupNamespace false

/-!
# Regularity for Coinductive Local Types

Defines reachability, regularity, and closedness lemmas used to extract
finite representations from coinductive session types.
-/

namespace RumpsteakV2.Coinductive

open Classical

/-- One-step child relation induced by the M-type destructor. -/
def childRel (t c : LocalTypeC) : Prop :=
  ∃ (s : LocalTypeHead) (f : LocalTypeChild s → LocalTypeC) (i : LocalTypeChild s),
    PFunctor.M.dest t = ⟨s, f⟩ ∧ f i = c

/-- Reachable subterms via the reflexive-transitive closure of `childRel`. -/
def Reachable (t : LocalTypeC) : Set LocalTypeC :=
  { s | Relation.ReflTransGen childRel t s }

/-- Regular coinductive types: finitely many reachable states. -/
def Regular (t : LocalTypeC) : Prop :=
  Set.Finite (Reachable t)

/-- Alias for regularity, used as the bridge witness. -/
def HasFiniteRep (t : LocalTypeC) : Prop := Regular t

/-- If `current` is reachable and `child` is a child of `current`, then `child` is reachable. -/
lemma reachable_step {root current child : LocalTypeC}
    (h_current : current ∈ Reachable root) (h_child : childRel current child) :
    child ∈ Reachable root := by
  exact h_current.tail h_child

/-- A finite set is closed under children if it contains all children of its elements. -/
def IsClosedSet (s : Finset LocalTypeC) : Prop :=
  ∀ x ∈ s, ∀ c, childRel x c → c ∈ s

/-- The finite set of reachable states is closed under children. -/
lemma reachable_is_closed_set (t : LocalTypeC) (h : Regular t) :
    IsClosedSet (Set.Finite.toFinset h) := by
  intro s hs c hchild
  have hs' : s ∈ Reachable t := by
    simpa using (Set.Finite.mem_toFinset h).1 hs
  have hc' : c ∈ Reachable t := reachable_step hs' hchild
  exact (Set.Finite.mem_toFinset h).2 hc'

/-- If a set is closed under children, then children of members are in the set. -/
lemma mem_of_closed_child {s : Finset LocalTypeC} {x : LocalTypeC} {c : LocalTypeC}
    (h_closed : IsClosedSet s) (hx : x ∈ s) (hc : childRel x c) : c ∈ s :=
  h_closed _ hx _ hc

/-- Inserting a member preserves subset. -/
lemma subset_insert_of_mem {α : Type} [DecidableEq α] {s v : Finset α} {x : α}
    (h1 : x ∈ s) (h2 : v ⊆ s) : Insert.insert x v ⊆ s :=
  Finset.insert_subset h1 h2

/-- Card decreases when inserting a new element from a finite superset. -/
lemma card_sub_insert_lt {α : Type} [DecidableEq α] {s : Finset α} {v : Finset α} {x : α}
    (h1 : x ∈ s) (h2 : x ∉ v) (h3 : v ⊆ s) :
    s.card - (Insert.insert x v).card < s.card - v.card := by
  have h_card_insert : (insert x v).card = v.card + 1 := by
    exact Finset.card_insert_of_notMem h2
  exact Nat.sub_lt_sub_left
    (by
      have : v.card < s.card := by
        have hssub : v ⊂ s := by
          exact Finset.ssubset_iff_subset_ne.mpr ⟨h3, by aesop⟩
        exact Finset.card_lt_card hssub
      linarith)
    (by linarith)

end RumpsteakV2.Coinductive
