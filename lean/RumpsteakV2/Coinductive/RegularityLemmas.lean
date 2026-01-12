import Mathlib
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Coinductive.Bisim

set_option linter.dupNamespace false

/-!
# Regularity transport lemmas

Regularity is preserved by constructors (via child regularity) and by bisimilarity.
-/

namespace RumpsteakV2.Coinductive

open Classical

/-- Convert `childRel` into a child index for `children`. -/
lemma childRel_to_children {t c : LocalTypeC} (h : childRel t c) :
    ∃ i : LocalTypeChild (head t), children t i = c := by
  rcases h with ⟨s, f, i, hdest, hchild⟩
  have hhead : head t = s := by
    simpa [head, hdest]
  refine ⟨cast (by simpa [hhead]) i, ?_⟩
  cases hhead
  cases hdest
  simpa [children] using hchild

/-- Decompose reachability: either the root or reachable from a child. -/
lemma reachable_decomp {t u : LocalTypeC} (h : u ∈ Reachable t) :
    u = t ∨ ∃ i : LocalTypeChild (head t), u ∈ Reachable (children t i) := by
  induction h with
  | refl =>
      exact Or.inl rfl
  | tail hrest hstep ih =>
      cases ih with
      | inl hb =>
          subst hb
          rcases childRel_to_children hstep with ⟨i, hchild⟩
          refine Or.inr ⟨i, ?_⟩
          -- hchild : children _ i = u, so u is trivially reachable from that child
          simpa [Reachable, hchild] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen childRel (children _ i) (children _ i))
      | inr hchild =>
          rcases hchild with ⟨i, hi⟩
          refine Or.inr ⟨i, ?_⟩
          exact hi.tail hstep

/-- Reachable set is contained in the root plus reachable children. -/
lemma reachable_subset_children (t : LocalTypeC) :
    Reachable t ⊆ ({t} ∪ ⋃ i : LocalTypeChild (head t), Reachable (children t i)) := by
  intro u hu
  rcases reachable_decomp hu with rfl | ⟨i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr (by exact Set.mem_iUnion.mpr ⟨i, hi⟩)

/-- If all children are regular, the node is regular. -/
lemma regular_of_children (t : LocalTypeC)
    (h : ∀ i : LocalTypeChild (head t), Regular (children t i)) : Regular t := by
  classical
  haveI : Fintype (LocalTypeChild (head t)) := by
    cases hhead : head t <;> infer_instance
  have hfinite_children : Set.Finite (⋃ i : LocalTypeChild (head t), Reachable (children t i)) := by
    simpa using (Set.finite_iUnion (f := fun i => Reachable (children t i)) (H := fun i => h i))
  have hfinite_root : Set.Finite ({t} : Set LocalTypeC) := Set.finite_singleton t
  have hfinite_union : Set.Finite ({t} ∪ ⋃ i : LocalTypeChild (head t), Reachable (children t i)) :=
    hfinite_root.union hfinite_children
  exact Set.Finite.subset hfinite_union (reachable_subset_children t)

/-- Regularity is preserved under bisimilarity (extensionality). -/
lemma regular_of_bisim {x y : LocalTypeC} (h : Bisim x y) (hx : Regular x) : Regular y := by
  have hxy : x = y := (Bisim_eq_iff x y).1 h
  simpa [hxy] using hx

end RumpsteakV2.Coinductive
