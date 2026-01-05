import Mathlib.Tactic

/-! # RumpsteakV2.Protocol.Projection.MutualTestSizeOf

Minimal mutual recursion test using `sizeOf` + `decreasing_by`.
-/

namespace RumpsteakV2.Protocol.Projection.MutualTestSizeOf

inductive MT2 where
  | leaf : Nat → MT2
  | node : List MT2 → MT2
deriving Repr, Inhabited

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf x < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_list_lt_node (xs : List MT2) :
    sizeOf xs < sizeOf (MT2.node xs) := by
  simp only [MT2.node.sizeOf_spec]
  omega

mutual
  def countNodes : MT2 → Nat
    | .leaf _ => 1
    | .node xs => 1 + countList xs
  termination_by t => sizeOf t
  decreasing_by
    all_goals
      first
      | exact sizeOf_list_lt_node _

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

@[simp] theorem countNodes_leaf (n : Nat) : countNodes (.leaf n) = 1 := by
  simp [countNodes]

@[simp] theorem countList_nil : countList ([] : List MT2) = 0 := by
  simp [countList]

@[simp] theorem countList_cons (x : MT2) (xs : List MT2) :
    countList (x :: xs) = countNodes x + countList xs := by
  simp [countList]

end RumpsteakV2.Protocol.Projection.MutualTestSizeOf
