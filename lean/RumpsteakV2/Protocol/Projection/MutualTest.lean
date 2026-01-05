import Mathlib.Tactic

/-! # RumpsteakV2.Protocol.Projection.MutualTest

Minimal mutual recursion test for Lean 4 syntax/termination.
-/

namespace RumpsteakV2.Protocol.Projection.MutualTest

inductive MT where
  | leaf : Nat → MT
  | node : List MT → MT
deriving Repr, Inhabited

mutual
  def countNodes : MT → Nat
    | .leaf _ => 1
    | .node xs => 1 + countList xs
  termination_by structural t => t

  def countList : List MT → Nat
    | [] => 0
    | x :: xs => countNodes x + countList xs
  termination_by structural xs => xs
end

@[simp] theorem countNodes_leaf (n : Nat) : countNodes (.leaf n) = 1 := by
  simp [countNodes]

@[simp] theorem countList_nil : countList ([] : List MT) = 0 := by
  simp [countList]

@[simp] theorem countList_cons (x : MT) (xs : List MT) :
    countList (x :: xs) = countNodes x + countList xs := by
  simp [countList]

end RumpsteakV2.Protocol.Projection.MutualTest
