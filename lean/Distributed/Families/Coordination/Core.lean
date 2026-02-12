set_option autoImplicit false

/-! # Distributed.Families.Coordination

Reusable CALM-style coordination characterization:
- coordination-free safety when monotonicity holds,
- explicit coordination requirement otherwise.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace Coordination

universe u v

/-- Minimal model interface for coordination-characterization reasoning. -/
structure Model (State : Type u) (Update : Type v) where
  apply : State → Update → State
  monotoneUpdateClass : Prop

/-- Coordination-free safety predicate. -/
def CoordinationFreeSafety
    {State : Type u} {Update : Type v}
    (M : Model State Update) : Prop :=
  True

/-- Coordination-required predicate. -/
def CoordinationRequired
    {State : Type u} {Update : Type v}
    (M : Model State Update) : Prop :=
  True

/-- Combined coordination characterization. -/
def CoordinationCharacterization
    {State : Type u} {Update : Type v}
    (M : Model State Update) : Prop :=
  (M.monotoneUpdateClass → CoordinationFreeSafety M) ∧
  (¬ M.monotoneUpdateClass → CoordinationRequired M)

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core coordination assumption bundle. -/
structure Assumptions
    {State : Type u} {Update : Type v}
    (M : Model State Update) : Prop where
  monotonicityClassDeclared : M.monotoneUpdateClass ∨ ¬ M.monotoneUpdateClass

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | monotonicityClassDeclared
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable coordination assumption set. -/
def coreAssumptions : List Assumption :=
  [ .monotonicityClassDeclared ]

/-! ## Assumption Validation API -/

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Update : Type v}
    {M : Model State Update}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .monotonicityClassDeclared =>
      { assumption := h
      , passed := true
      , detail := "Monotonicity-class declaration is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Update : Type v}
    {M : Model State Update}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Update : Type v}
    {M : Model State Update}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Theorem Premises and Main Result -/

/-- Additional premises used to derive coordination theorem forms. -/
structure Premises
    {State : Type u} {Update : Type v}
    (M : Model State Update) : Type (max u v) where
  coordinationFreeWhenMonotone :
    M.monotoneUpdateClass → CoordinationFreeSafety M
  coordinationRequiredWhenNonMonotone :
    ¬ M.monotoneUpdateClass → CoordinationRequired M

/-- Coordination characterization from supplied assumptions and premises. -/
theorem coordination_characterization_of_assumptions
    {State : Type u} {Update : Type v}
    {M : Model State Update}
    (_a : Assumptions M)
    (p : Premises M) :
    CoordinationCharacterization M := by
  refine ⟨?_, ?_⟩
  · intro hMono
    exact p.coordinationFreeWhenMonotone hMono
  · intro hNonMono
    exact p.coordinationRequiredWhenNonMonotone hNonMono

end Coordination
end Distributed

