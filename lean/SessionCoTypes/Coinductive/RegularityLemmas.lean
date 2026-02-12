import Mathlib
import SessionCoTypes.Coinductive.Regularity
import SessionCoTypes.Coinductive.Bisim

/-! # SessionCoTypes.Coinductive.RegularityLemmas

Regularity lemmas for coinductive local types: child decomposition,
reachability decomposition, and regularity transport across bisimilarity.
-/

set_option linter.dupNamespace false


/-
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

/-- Canonical list of child indices for each node head. -/
private def childIndices (s : LocalTypeHead) : List (LocalTypeChild s) :=
  match s with
  | .end => []
  | .var _ => []
  | .mu _ => [()]
  | .send _ ls => List.finRange ls.length
  | .recv _ ls => List.finRange ls.length

/-- Every child index is contained in `childIndices`. -/
private theorem mem_childIndices (s : LocalTypeHead) (i : LocalTypeChild s) :
    i ∈ childIndices s := by
  cases s
  · cases i
  · cases i
  · cases i
    simp [childIndices]
  · exact List.mem_finRange i
  · exact List.mem_finRange i

/-- Collect all child witness states into one list. -/
private def childWitnessStates (t : LocalTypeC)
    (h : ∀ i : LocalTypeChild (head t), Regular (children t i)) : List LocalTypeC :=
  (childIndices (head t)).flatMap (fun i => (h i).states)

/-- If all children of a node are regular, then the node is regular.
    This is the key lemma for building regular types. -/
def regular_of_children (t : LocalTypeC)
    (h : ∀ i : LocalTypeChild (head t), Regular (children t i)) : Regular t := by
  refine
    { states := t :: childWitnessStates t h
      root_mem := by simp [childWitnessStates]
      closed := ?_ }
  intro x hx c hchild
  have hx' : x = t ∨ x ∈ childWitnessStates t h := by
    simpa [childWitnessStates] using (List.mem_cons.1 hx)
  cases hx' with
  | inl hxt =>
      cases hxt
      rcases childRel_to_children hchild with ⟨i, hi⟩
      have hi_mem : i ∈ childIndices (head t) := mem_childIndices (head t) i
      have hc_mem_child : c ∈ childWitnessStates t h := by
        refine List.mem_flatMap.2 ?_
        refine ⟨i, hi_mem, ?_⟩
        simpa [childWitnessStates, hi] using (h i).root_mem
      exact List.mem_cons_of_mem _ hc_mem_child
  | inr hxChild =>
      rcases List.mem_flatMap.1 hxChild with ⟨i, hi_mem, hx_mem_i⟩
      have hc_mem_i : c ∈ (h i).states :=
        (h i).closed x hx_mem_i c hchild
      have hc_mem_child : c ∈ childWitnessStates t h :=
        List.mem_flatMap.2 ⟨i, hi_mem, hc_mem_i⟩
      exact List.mem_cons_of_mem _ hc_mem_child

/-- Regularity is preserved under bisimilarity.
    Since bisimilarity equals equality, this is immediate. -/
def regular_of_bisim {x y : LocalTypeC} (h : Bisim x y) (hx : Regular x) : Regular y := by
  have hxy : x = y := (Bisim_eq_iff x y).1 h
  simpa [hxy] using hx

end SessionCoTypes.Coinductive
