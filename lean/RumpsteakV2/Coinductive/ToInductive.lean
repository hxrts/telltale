import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Regularity
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
The Problem. Given a regular coinductive type (one with finitely many reachable
states), we want to construct an equivalent finite inductive type. This enables
round-tripping between the two representations.

The difficulty is handling cycles: a coinductive type can have recursive structure
that requires mu-binders in the inductive representation. We need to:
- Track visited nodes to detect back-edges
- Generate fresh names for mu-binders that don't clash
- Insert mu-binders only where needed (when a recursive reference occurs)

Solution Structure.
1. Fresh name generation: nameFor produces names longer than any existing name
2. toInductiveAux: recursive traversal with visited set for cycle detection
3. toInductive: entry point that initializes with the reachable set
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## Helper Functions -/

/-- Find the index of a value in a list (for deterministic naming). -/
def indexOf {α : Type} [DecidableEq α] (x : α) : List α → Option Nat
  | []      => none
  | y :: ys => if x = y then some 0 else (indexOf x ys).map Nat.succ

/-- Collect names from a coinductive node's head (var and mu binders). -/
def namesOf (c : LocalTypeC) : Finset String :=
  match head c with
  | .var x => {x}
  | .mu x  => {x}
  | _      => ∅

/-- All names appearing in heads of a set of coinductive nodes. -/
def namesIn (all : Finset LocalTypeC) : Finset String :=
  all.biUnion namesOf

/-! ## Fresh Name Generation -/

/-- Maximum string length in a finite set of strings. -/
def maxLen (avoid : Finset String) : Nat :=
  (avoid.image String.length).sup id

@[simp] lemma sup_eq_max (a b : Nat) : a ⊔ b = max a b := rfl

lemma maxLen_insert {avoid : Finset String} {s : String} :
    maxLen (insert s avoid) = max (maxLen avoid) s.length := by
  classical
  simp [maxLen, Finset.image_insert, Finset.sup_insert, max_comm]

lemma length_le_maxLen {avoid : Finset String} {x : String} (hs : x ∈ avoid) :
    x.length ≤ maxLen avoid := by
  classical
  have hx : x.length ∈ (avoid.image String.length) := Finset.mem_image.2 ⟨x, hs, rfl⟩
  simpa [maxLen] using Finset.le_sup (s := avoid.image String.length) (f := id) hx

/-- Base name prefix derived from a node's index in the reachable set. -/
noncomputable def baseName (t : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match indexOf t all.toList with
  | some i => "s" ++ toString i
  | none   => "sunknown"

/-- Generate a fresh name for a state that doesn't clash with any existing name.
    Works by appending a suffix longer than any existing name. -/
noncomputable def nameFor (t : LocalTypeC) (all : Finset LocalTypeC) : String :=
  let base := baseName t all
  let avoid := namesIn all
  let suffixLen := maxLen avoid + 1
  base ++ "_" ++ String.replicate suffixLen 'a'

/-- The generated name is guaranteed fresh (not in namesIn). -/
lemma nameFor_not_mem_namesIn (t : LocalTypeC) (all : Finset LocalTypeC) :
    nameFor t all ∉ namesIn all := by
  classical
  intro hmem
  have hlen : (nameFor t all).length ≤ maxLen (namesIn all) :=
    length_le_maxLen (avoid := namesIn all) hmem
  have hgt : maxLen (namesIn all) < (nameFor t all).length := by
    have h_underscore : ("_" : String).length = 1 := by decide
    have hlen_name : (nameFor t all).length =
        (baseName t all).length + 1 + (maxLen (namesIn all) + 1) := by
      simp [nameFor, baseName, String.length_replicate, h_underscore,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    have hlt : maxLen (namesIn all) < maxLen (namesIn all) + 1 := Nat.lt_succ_self _
    have hle : maxLen (namesIn all) + 1 ≤
        (baseName t all).length + 1 + (maxLen (namesIn all) + 1) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.le_add_left (maxLen (namesIn all) + 1) ((baseName t all).length + 1)
    simpa [hlen_name] using lt_of_lt_of_le hlt hle
  exact lt_irrefl _ (lt_of_le_of_lt hlen hgt)

/-! ## Main Conversion -/

/-- Convert a regular coinductive type to inductive, tracking visited nodes.

    The algorithm:
    - If current node is visited, emit a variable reference (back-edge)
    - Otherwise, recurse into children with current added to visited
    - Wrap in mu if a recursive reference was generated -/
noncomputable def toInductiveAux (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all)
    (h_visited : visited ⊆ all) (h_current : current ∈ all) : LocalTypeR :=
  let name := match head current with
    | .mu x => x
    | _     => nameFor current all
  if h : current ∈ visited then
    by
      -- use `h` so the binder is not unused (also feeds termination)
      simpa [h] using (.var name)
  else
    let visited' := Insert.insert current visited
    let body := match hdest : PFunctor.M.dest current with
      | ⟨.end, _⟩   => LocalTypeR.end
      | ⟨.var x, _⟩ => LocalTypeR.var x
      | ⟨.mu x, k⟩  =>
          let child := k ()
          have hchild : childRel current child := ⟨.mu x, k, (), hdest, rfl⟩
          have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
          toInductiveAux root all visited' child h_closed
            (subset_insert_of_mem h_current h_visited) hchild_mem
      | ⟨.send p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := ⟨.send p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body := toInductiveAux root all visited' child h_closed
              (subset_insert_of_mem h_current h_visited) hchild_mem
            (labels[i], body)
          LocalTypeR.send p (List.ofFn f)
      | ⟨.recv p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := ⟨.recv p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body := toInductiveAux root all visited' child h_closed
              (subset_insert_of_mem h_current h_visited) hchild_mem
            (labels[i], body)
          LocalTypeR.recv p (List.ofFn f)
    -- Wrap in mu if needed
    match head current with
    | .mu _  => LocalTypeR.mu name body
    | .var _ => body
    | _      => if name ∈ body.freeVars then LocalTypeR.mu name body else body
termination_by all.card - visited.card
decreasing_by
  all_goals
    apply card_sub_insert_lt h_current
    · exact h
    · exact h_visited

/-! ## Entry Point -/

/-- Convert a regular coinductive local type to its inductive representation. -/
noncomputable def toInductive (t : LocalTypeC) (h : Regular t) : LocalTypeR :=
  let all := Set.Finite.toFinset h
  toInductiveAux t all ∅ t (reachable_is_closed_set t h)
    (Finset.empty_subset _)
    ((Set.Finite.mem_toFinset h).2 Relation.ReflTransGen.refl)

end RumpsteakV2.Coinductive
