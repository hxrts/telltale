import Mathlib.Data.List.Basic
import RumpsteakV2.Protocol.GlobalType

/-! # RumpsteakV2.Protocol.LocalTypeR

Recursive local types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `LocalTypeR`
- `LocalTypeR.dual`
- `LocalTypeR.unfold`
- `LocalTypeR.freeVars`
- `LocalTypeR.substitute`
-/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType

/-- Recursive local types with branching. -/
inductive LocalTypeR where
  | end : LocalTypeR
  | send : String → List (Label × LocalTypeR) → LocalTypeR
  | recv : String → List (Label × LocalTypeR) → LocalTypeR
  | mu : String → LocalTypeR → LocalTypeR
  | var : String → LocalTypeR
  deriving Repr, Inhabited

/- Extract free type variables from a local type. -/
mutual
  def LocalTypeR.freeVars : LocalTypeR → List String
    | .end => []
    | .send _ branches => freeVarsOfBranches branches
    | .recv _ branches => freeVarsOfBranches branches
    | .mu t body => body.freeVars.filter (· != t)
    | .var t => [t]

  def freeVarsOfBranches : List (Label × LocalTypeR) → List String
    | [] => []
    | (_, t) :: rest => t.freeVars ++ freeVarsOfBranches rest
end

theorem freeVarsOfBranches_eq_flatMap (branches : List (Label × LocalTypeR)) :
    freeVarsOfBranches branches = branches.flatMap (fun (_, t) => t.freeVars) := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk label t =>
          simp [freeVarsOfBranches, ih, List.flatMap]

/- Substitute a local type for a variable. -/
mutual
  def LocalTypeR.substitute : LocalTypeR → String → LocalTypeR → LocalTypeR
    | .end, _, _ => .end
    | .send partner branches, varName, replacement =>
        .send partner (substituteBranches branches varName replacement)
    | .recv partner branches, varName, replacement =>
        .recv partner (substituteBranches branches varName replacement)
    | .mu t body, varName, replacement =>
        if t == varName then
          .mu t body
        else
          .mu t (body.substitute varName replacement)
    | .var t, varName, replacement =>
        if t == varName then replacement else .var t

  def substituteBranches : List (Label × LocalTypeR) → String → LocalTypeR → List (Label × LocalTypeR)
    | [], _, _ => []
    | (label, cont) :: rest, varName, replacement =>
        (label, cont.substitute varName replacement) ::
          substituteBranches rest varName replacement
end

/-- Unfold one level of recursion: μt.T ↦ T[μt.T/t]. -/
def LocalTypeR.unfold : LocalTypeR → LocalTypeR
  | lt@(.mu t body) => body.substitute t lt
  | lt => lt

/- Dualize a local type by swapping send/recv. -/
mutual
  def LocalTypeR.dual : LocalTypeR → LocalTypeR
    | .end => .end
    | .send partner branches => .recv partner (dualBranches branches)
    | .recv partner branches => .send partner (dualBranches branches)
    | .mu t body => .mu t (body.dual)
    | .var t => .var t

  def dualBranches : List (Label × LocalTypeR) → List (Label × LocalTypeR)
    | [] => []
    | (label, cont) :: rest => (label, cont.dual) :: dualBranches rest
end

mutual
  /-- Dual is an involution on local types. -/
  def LocalTypeR.dual_dual : (t : LocalTypeR) → t.dual.dual = t
    | .end => rfl
    | .var _ => rfl
    | .mu _ body => congrArg (LocalTypeR.mu _) body.dual_dual
    | .send _ bs => congrArg (LocalTypeR.send _) (dualBranches_dualBranches bs)
    | .recv _ bs => congrArg (LocalTypeR.recv _) (dualBranches_dualBranches bs)

  /-- Dual branches is an involution. -/
  def dualBranches_dualBranches : (bs : List (Label × LocalTypeR)) →
      dualBranches (dualBranches bs) = bs
    | [] => rfl
    | (_, cont) :: rest =>
        congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl cont.dual_dual)
          (dualBranches_dualBranches rest)
end

/-! ## Dual-Substitute Commutation

These lemmas show that dual and substitute commute, which is essential for
proving that EQ2 is a congruence for duality. -/

mutual
  /-- Dual commutes with substitute: (t.substitute v r).dual = t.dual.substitute v r.dual. -/
  theorem LocalTypeR.dual_substitute : (t : LocalTypeR) → (var : String) → (repl : LocalTypeR) →
      (t.substitute var repl).dual = t.dual.substitute var repl.dual
    | .end, _, _ => rfl
    | .var v, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        split <;> rfl
    | .mu v body, var, repl =>
        if hv : v == var then by
          -- Shadowed case: both sides reduce to mu v body.dual
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte]
        else by
          -- Non-shadowed case
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte, Bool.false_eq_true]
          exact congrArg (LocalTypeR.mu v) (LocalTypeR.dual_substitute body var repl)
    | .send p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.recv p) (dualBranches_substituteBranches bs var repl)
    | .recv p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.send p) (dualBranches_substituteBranches bs var repl)

  /-- Dual and substitute commute for branch lists. -/
  theorem dualBranches_substituteBranches : (bs : List (Label × LocalTypeR)) →
      (var : String) → (repl : LocalTypeR) →
      dualBranches (substituteBranches bs var repl) =
        substituteBranches (dualBranches bs) var repl.dual
    | [], _, _ => rfl
    | (label, cont) :: rest, var, repl => by
        simp only [substituteBranches, dualBranches]
        exact congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl (LocalTypeR.dual_substitute cont var repl))
          (dualBranches_substituteBranches rest var repl)
end

end RumpsteakV2.Protocol.LocalTypeR
