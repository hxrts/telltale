import Mathlib.Tactic
import RumpsteakV2.Protocol.Projection.MutualTestSizeOf

/-! # RumpsteakV2.Protocol.Projection.MutualTestIncr

Incremental mutual recursion examples to debug syntax/termination.

This is an internal test file for debugging mutual recursion patterns.
It is not part of the semantic interface and does not export definitions for proofs.
-/

namespace RumpsteakV2.Protocol.Projection.MutualTestIncr

namespace Step1

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

end Step1

namespace Step2

open RumpsteakV2.Protocol.Projection.MutualTestSizeOf

inductive MT where
  | leaf : Nat → MT
  | node : List MT → MT
  deriving Repr, Inhabited

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf x < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_list_lt_node (xs : List MT) :
    sizeOf xs < sizeOf (MT.node xs) := by
  simp only [MT.node.sizeOf_spec]
  omega

mutual
  def countNodes : MT → Nat
    | .leaf _ => 1
    | .node xs => 1 + countList xs
  termination_by t => sizeOf t
  decreasing_by
    all_goals
      first
      | exact sizeOf_list_lt_node _

  def countList : List MT → Nat
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

@[simp] theorem countList_nil : countList ([] : List MT) = 0 := by
  simp [countList]

@[simp] theorem countList_cons (x : MT) (xs : List MT) :
    countList (x :: xs) = countNodes x + countList xs := by
  simp [countList]

end Step2

namespace Step3

open Step2

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf x < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (xs : List α) :
    sizeOf xs < sizeOf (x :: xs) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_list_lt_node (xs : List MT) :
    sizeOf xs < sizeOf (MT.node xs) := by
  simp only [MT.node.sizeOf_spec]
  omega

mutual
  theorem countNodes_ge_one : ∀ t : MT, 1 ≤ Step2.countNodes t
    | .leaf _ => by
        simp
    | .node xs => by
        have hxs : 0 ≤ Step2.countList xs := countList_nonneg xs
        have h : 1 ≤ Step2.countList xs + 1 := Nat.succ_le_succ hxs
        simp only [Step2.countNodes]
        rw [Nat.add_comm]
        exact h
  termination_by t => sizeOf t
  decreasing_by
    all_goals
      exact sizeOf_list_lt_node _

  theorem countList_nonneg : ∀ xs : List MT, 0 ≤ Step2.countList xs
    | [] => by
        simp
    | x :: xs => by
        have hx1 : 1 ≤ Step2.countNodes x := countNodes_ge_one x
        have hx : 0 ≤ Step2.countNodes x := Nat.le_trans (Nat.zero_le 1) hx1
        have hxs : 0 ≤ Step2.countList xs := countList_nonneg xs
        have hsum' : 0 + 0 ≤ Step2.countNodes x + Step2.countList xs :=
          Nat.add_le_add hx hxs
        have hsum : 0 ≤ Step2.countNodes x + Step2.countList xs := by
          exact le_of_eq_of_le (by simp) hsum'
        simp only [Step2.countList]
        exact hsum
  termination_by xs => sizeOf xs
  decreasing_by
    all_goals
      first
      | exact sizeOf_head_lt_cons _ _
      | exact sizeOf_tail_lt_cons _ _
end

end Step3

end RumpsteakV2.Protocol.Projection.MutualTestIncr
