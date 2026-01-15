import Mathlib.Tactic

/-
The Problem. Testing mutual recursion with explicit termination metrics. When
structural recursion is insufficient or unclear, we use `sizeOf` with
`decreasing_by` to prove termination manually.

Solution Structure. Define the same tree type, prove size lemmas showing each
recursive call decreases the measure, and use these in `decreasing_by` tactics.
-/

/-! # RumpsteakV2.Protocol.Projection.MutualTestSizeOf

Minimal mutual recursion test using `sizeOf` + `decreasing_by`.

This is an internal test file for debugging mutual recursion patterns.
It is not part of the semantic interface and does not export definitions for proofs.
-/

namespace RumpsteakV2.Protocol.Projection.MutualTestSizeOf

/-! ## Test Type -/

/-- Minimal tree type for testing sizeOf-based termination. -/
inductive MT2 where
  | leaf : Nat → MT2
  | node : List MT2 → MT2
deriving Repr, Inhabited

/-! ## Size Lemmas -/

/-- The head of a cons is smaller than the whole list. -/
private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf x < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

/-- The tail of a cons is smaller than the whole list. -/
private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

/-- The children list is smaller than the node containing it. -/
private theorem sizeOf_list_lt_node (xs : List MT2) :
    sizeOf xs < sizeOf (MT2.node xs) := by
  simp only [MT2.node.sizeOf_spec]
  omega

/-! ## Mutually Recursive Functions -/

mutual
  /-- Count total nodes in a tree (including internal nodes). -/
  def countNodes : MT2 → Nat
    | .leaf _ => 1
    | .node xs => 1 + countList xs
  termination_by t => sizeOf t
  decreasing_by
    all_goals
      first
      | exact sizeOf_list_lt_node _

  /-- Count total nodes across a list of trees. -/
  def countList : List MT2 → Nat
    | [] => 0
    | x :: xs => countNodes x + countList xs
  termination_by xs => sizeOf xs
  decreasing_by
    all_goals
      first
      | exact sizeOf_head_lt_cons _ _
      | exact sizeOf_tail_lt_cons _ _
end

/-! ## Simplification Lemmas -/

/-- Counting a leaf gives 1. -/
@[simp] theorem countNodes_leaf (n : Nat) : countNodes (.leaf n) = 1 := by
  simp [countNodes]

/-- Counting an empty list gives 0. -/
@[simp] theorem countList_nil : countList ([] : List MT2) = 0 := by
  simp [countList]

/-- Counting a cons distributes over the head and tail. -/
@[simp] theorem countList_cons (x : MT2) (xs : List MT2) :
    countList (x :: xs) = countNodes x + countList xs := by
  simp [countList]

end RumpsteakV2.Protocol.Projection.MutualTestSizeOf
