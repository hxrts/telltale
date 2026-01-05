import Mathlib.Data.List.Basic

namespace List

/-- Compat: `List.get!` defined via `getD` with default. -/
def get! [Inhabited α] (l : List α) (i : Nat) : α :=
  l.getD i default

theorem get!_eq_getD [Inhabited α] (l : List α) (i : Nat) :
    l.get! i = l.getD i default := rfl

@[simp] theorem get!_nil [Inhabited α] (i : Nat) :
    ([] : List α).get! i = default := by
  simp [List.get!]

@[simp] theorem get!_cons_zero [Inhabited α] (a : α) (l : List α) :
    (a :: l).get! 0 = a := by
  simp [List.get!]

@[simp] theorem get!_cons_succ [Inhabited α] (a : α) (l : List α) (n : Nat) :
    (a :: l).get! (n + 1) = l.get! n := by
  simp [List.get!, List.getD]

end List
