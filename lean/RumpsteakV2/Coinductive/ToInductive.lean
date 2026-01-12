import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# toInductive: Regular LocalTypeC → LocalTypeR

Constructs a finite inductive representation from a regular coinductive
local type by traversing reachable states and inserting `mu` binders for
visited nodes.
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-- Find the index of a value in a list. -/
def indexOf {α : Type} [DecidableEq α] (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map Nat.succ

/-- Deterministic name for a state based on its index in the reachable list. -/
noncomputable def nameFor (t : LocalTypeC) (all : Finset LocalTypeC) : String :=
  let l := all.toList
  match indexOf t l with
  | some i => "s" ++ toString i
  | none => "unknown"

/-- Auxiliary conversion with a visited set for cycle detection. -/
noncomputable def toInductiveAux (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all)
    (h_visited : visited ⊆ all) (h_current : current ∈ all) : LocalTypeR :=
  if h : current ∈ visited then
    .var (nameFor current all)
  else
    let name := nameFor current all
    let visited' := Insert.insert current visited
    let body := match hdest : PFunctor.M.dest current with
      | ⟨.end, _⟩ => LocalTypeR.end
      | ⟨.var x, _⟩ => LocalTypeR.var x
      | ⟨.mu x, k⟩ =>
          let child := k ()
          have hchild : childRel current child := by
            exact ⟨.mu x, k, (), hdest, rfl⟩
          have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
          LocalTypeR.mu x
            (toInductiveAux root all visited' child h_closed
              (subset_insert_of_mem h_current h_visited) hchild_mem)
      | ⟨.send p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := by
              exact ⟨.send p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body :=
              toInductiveAux root all visited' child
                h_closed
                (subset_insert_of_mem h_current h_visited)
                hchild_mem
            (labels.get i, body)
          LocalTypeR.send p (List.ofFn f)
      | ⟨.recv p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := by
              exact ⟨.recv p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body :=
              toInductiveAux root all visited' child
                h_closed
                (subset_insert_of_mem h_current h_visited)
                hchild_mem
            (labels.get i, body)
          LocalTypeR.recv p (List.ofFn f)
    LocalTypeR.mu name body
termination_by all.card - visited.card
decreasing_by
  all_goals
    apply card_sub_insert_lt h_current
    · exact h
    · exact h_visited

/-- A regular coinductive local type has a finite inductive representation. -/
noncomputable def toInductive (t : LocalTypeC) (h : Regular t) : LocalTypeR :=
  let all := Set.Finite.toFinset h
  toInductiveAux t all ∅ t (reachable_is_closed_set t h)
    (by exact Finset.empty_subset _)
    (by
      have hmem : t ∈ Reachable t := Relation.ReflTransGen.refl
      exact (Set.Finite.mem_toFinset h).2 hmem)

end RumpsteakV2.Coinductive
