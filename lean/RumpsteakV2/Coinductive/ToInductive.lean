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

/-- Collect the head name of a coinductive node (vars + μ binders). -/
def namesOf (c : LocalTypeC) : Finset String :=
  match head c with
  | .var x => {x}
  | .mu x => {x}
  | _ => ∅

/-- All head names appearing in a finite set of coinductive nodes. -/
def namesIn (all : Finset LocalTypeC) : Finset String :=
  all.biUnion namesOf

/-! ### Fresh name generation -/

/-- Maximum string length in a finite set. -/
def maxLen (avoid : Finset String) : Nat :=
  (avoid.image String.length).sup id

@[simp] lemma sup_eq_max (a b : Nat) : a ⊔ b = max a b := rfl

lemma maxLen_insert {avoid : Finset String} {s : String} :
    maxLen (insert s avoid) = max (maxLen avoid) s.length := by
  classical
  simp [maxLen, Finset.image_insert, Finset.sup_insert, max_comm, max_left_comm, max_assoc]

lemma length_le_maxLen {avoid : Finset String} {x : String} (hs : x ∈ avoid) :
    x.length ≤ maxLen avoid := by
  classical
  have hx : x.length ∈ (avoid.image String.length) := by
    exact Finset.mem_image.2 ⟨x, hs, rfl⟩
  simpa [maxLen] using (Finset.le_sup (s := avoid.image String.length) (f := id) hx)


/- Deterministic fresh name for a state based on its index in the reachable list. -/
/-- Base prefix derived from a node's index. -/
noncomputable def baseName (t : LocalTypeC) (all : Finset LocalTypeC) : String :=
  let l := all.toList
  match indexOf t l with
  | some i => "s" ++ toString i
  | none => "sunknown"

/-- Deterministic fresh name for a state based on its index in the reachable list. -/
noncomputable def nameFor (t : LocalTypeC) (all : Finset LocalTypeC) : String :=
  let base := baseName t all
  let avoid := namesIn all
  let suffixLen := maxLen avoid + 1
  base ++ "_" ++ String.replicate suffixLen 'a'

lemma nameFor_not_mem_namesIn (t : LocalTypeC) (all : Finset LocalTypeC) :
    nameFor t all ∉ namesIn all := by
  classical
  intro hmem
  have hlen : (nameFor t all).length ≤ maxLen (namesIn all) :=
    length_le_maxLen (avoid := namesIn all) hmem
  -- But nameFor has length > maxLen (namesIn all).
  have hgt : maxLen (namesIn all) < (nameFor t all).length := by
    -- length of the generated name is base.length + 1 + (maxLen + 1)
    have h_underscore : ("_" : String).length = 1 := by
      decide
    have hlen_name :
        (nameFor t all).length =
          (baseName t all).length + 1 + (maxLen (namesIn all) + 1) := by
      simp [nameFor, baseName, String.length_replicate, h_underscore, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    -- maxLen < maxLen + 1 ≤ base.length + 1 + (maxLen + 1)
    have hlt : maxLen (namesIn all) < maxLen (namesIn all) + 1 := Nat.lt_succ_self _
    have hle :
        maxLen (namesIn all) + 1 ≤
          (baseName t all).length + 1 + (maxLen (namesIn all) + 1) := by
      -- a + 1 ≤ b + 1 + (a + 1)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.le_add_left (maxLen (namesIn all) + 1) ((baseName t all).length + 1))
    have hlt' : maxLen (namesIn all) <
        (baseName t all).length + 1 + (maxLen (namesIn all) + 1) :=
      lt_of_lt_of_le hlt hle
    simpa [hlen_name] using hlt'
  exact (lt_irrefl _ (lt_of_le_of_lt hlen hgt))

/-- Auxiliary conversion with a visited set for cycle detection. -/
noncomputable def toInductiveAux (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all)
    (h_visited : visited ⊆ all) (h_current : current ∈ all) : LocalTypeR :=
  let name :=
    match head current with
    | .mu x => x
    | _ => nameFor current all
  if h : current ∈ visited then
    .var name
  else
    let visited' := Insert.insert current visited
    let body := match hdest : PFunctor.M.dest current with
      | ⟨.end, _⟩ => LocalTypeR.end
      | ⟨.var x, _⟩ => LocalTypeR.var x
      | ⟨.mu x, k⟩ =>
          let child := k ()
          have hchild : childRel current child := by
            exact ⟨.mu x, k, (), hdest, rfl⟩
          have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
          toInductiveAux root all visited' child h_closed
            (subset_insert_of_mem h_current h_visited) hchild_mem
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
    match head current with
    | .mu _ => LocalTypeR.mu name body
    | .var _ => body
    | _ =>
        if name ∈ body.freeVars then
          LocalTypeR.mu name body
        else
          body
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