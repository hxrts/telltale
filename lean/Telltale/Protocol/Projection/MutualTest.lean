import Mathlib.Tactic

/-
The Problem. Testing mutual recursion patterns in Lean 4. We need to verify
that mutually recursive functions over nested list structures terminate using
structural recursion, and that basic simplification lemmas hold.

Solution Structure. Define a minimal tree type with mutual recursion between
node counting and list traversal, prove termination structurally, and establish
basic simp lemmas.
-/

/-! # Telltale.Protocol.Projection.MutualTest

Minimal mutual recursion test for Lean 4 syntax/termination.

This is an internal test file for debugging mutual recursion patterns.
It is not part of the semantic interface and does not export definitions for proofs.
-/

namespace Telltale.Protocol.Projection.MutualTest

/-! ## Test Type -/

/-- Minimal tree type for testing mutual recursion. -/
inductive MT where
  | leaf : Nat → MT
  | node : List MT → MT
deriving Repr, Inhabited

/-! ## Mutually Recursive Functions -/

mutual
  /-- Count total nodes in a tree (including internal nodes). -/
  def countNodes : MT → Nat
    | .leaf _ => 1
    | .node xs => 1 + countList xs
  termination_by structural t => t

  /-- Count total nodes across a list of trees. -/
  def countList : List MT → Nat
    | [] => 0
    | x :: xs => countNodes x + countList xs
  termination_by structural xs => xs
end

/-! ## Simplification Lemmas -/

/-- Counting a leaf gives 1. -/
@[simp] theorem countNodes_leaf (n : Nat) : countNodes (.leaf n) = 1 := by
  simp [countNodes]

/-- Counting an empty list gives 0. -/
@[simp] theorem countList_nil : countList ([] : List MT) = 0 := by
  simp [countList]

/-- Counting a cons distributes over the head and tail. -/
@[simp] theorem countList_cons (x : MT) (xs : List MT) :
    countList (x :: xs) = countNodes x + countList xs := by
  simp [countList]

end Telltale.Protocol.Projection.MutualTest
