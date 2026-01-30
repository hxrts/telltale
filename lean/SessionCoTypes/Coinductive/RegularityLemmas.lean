import Mathlib
import SessionCoTypes.Coinductive.Regularity
import SessionCoTypes.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
The Problem. To prove that constructed coinductive types are regular, we need
lemmas showing that regularity is preserved by constructors and bisimilarity.
The key insight is that a node is regular if all its children are regular.

Solution Structure.
1. Connect childRel to the children accessor function
2. Decompose reachability into "is root" or "reachable from some child"
3. Prove regular_of_children: regularity propagates up from children
4. Prove regular_of_bisim: bisimilar types have the same regularity
-/

namespace SessionCoTypes.Coinductive

open Classical

/-! ## Relating childRel to children -/

/-- Convert a childRel witness to a child index. -/
lemma childRel_to_children {t c : LocalTypeC} (h : childRel t c) :
    ∃ i : LocalTypeChild (head t), children t i = c := by
  rcases h with ⟨s, f, i, hdest, hchild⟩
  have hhead : head t = s := by simp [head, hdest]
  refine ⟨cast (by simp [hhead]) i, ?_⟩
  cases hhead; cases hdest
  simpa [children] using hchild

/-! ## Decomposing Reachability -/

/-- A reachable node is either the root or reachable from some child. -/
lemma reachable_decomp {t u : LocalTypeC} (h : u ∈ Reachable t) :
    u = t ∨ ∃ i : LocalTypeChild (head t), u ∈ Reachable (children t i) := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hrest hstep ih =>
      cases ih with
      | inl hb =>
          subst hb
          rcases childRel_to_children hstep with ⟨i, hchild⟩
          refine Or.inr ⟨i, ?_⟩
          simpa [Reachable, hchild] using Relation.ReflTransGen.refl
      | inr hchild =>
          rcases hchild with ⟨i, hi⟩
          exact Or.inr ⟨i, hi.tail hstep⟩

/-- Reachable set is contained in root plus union of children's reachable sets. -/
lemma reachable_subset_children (t : LocalTypeC) :
    Reachable t ⊆ ({t} ∪ ⋃ i : LocalTypeChild (head t), Reachable (children t i)) := by
  intro u hu
  rcases reachable_decomp hu with rfl | ⟨i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)

/-! ## Regularity Propagation -/

/-- If all children of a node are regular, then the node is regular.
    This is the key lemma for building regular types. -/
lemma regular_of_children (t : LocalTypeC)
    (h : ∀ i : LocalTypeChild (head t), Regular (children t i)) : Regular t := by
  classical
  haveI : Fintype (LocalTypeChild (head t)) := by
    cases hhead : head t <;> infer_instance
  have hfinite_children : Set.Finite (⋃ i, Reachable (children t i)) := by
    simpa using Set.finite_iUnion (f := fun i => Reachable (children t i)) (H := h)
  have hfinite_union : Set.Finite ({t} ∪ ⋃ i, Reachable (children t i)) :=
    (Set.finite_singleton t).union hfinite_children
  exact Set.Finite.subset hfinite_union (reachable_subset_children t)

/-- Regularity is preserved under bisimilarity.
    Since bisimilarity equals equality, this is immediate. -/
lemma regular_of_bisim {x y : LocalTypeC} (h : Bisim x y) (hx : Regular x) : Regular y := by
  have hxy : x = y := (Bisim_eq_iff x y).1 h
  simpa [hxy] using hx

end SessionCoTypes.Coinductive
