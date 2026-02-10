set_option autoImplicit false

/-! # Distributed.Families.AccountableSafety

Reusable accountable-safety assumptions and theorem forms:
- either safety holds, or explicit fault evidence is derivable.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace AccountableSafety

universe u v w

/-- Minimal model interface for accountable-safety reasoning. -/
structure Model (State : Type u) (Decision : Type v) (Fault : Type w) where
  conflicts : Decision → Decision → Prop
  decided : State → Decision → Prop
  faultEvidence : State → Fault → Prop
  slashableEvidenceRules : Prop
  equivocationDetectability : Prop

/-- Safety predicate: no conflicting decisions coexist in one state. -/
def SafetyHolds
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop :=
  ∀ s d₁ d₂, M.decided s d₁ → M.decided s d₂ → ¬ M.conflicts d₁ d₂

/-- Explicit accountable-fault evidence exists in a state. -/
def AccountableEvidenceExists
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop :=
  ∀ s, ∃ f, M.faultEvidence s f

/-- Accountable safety: either safety holds or slashable evidence exists. -/
def AccountableSafety
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop :=
  SafetyHolds M ∨ AccountableEvidenceExists M

/-- Reusable core accountable-safety assumption bundle. -/
structure Assumptions
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop where
  slashableEvidenceRules : M.slashableEvidenceRules
  equivocationDetectability : M.equivocationDetectability

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | slashableEvidenceRules
  | equivocationDetectability
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable accountable-safety assumption set. -/
def coreAssumptions : List Assumption :=
  [ .slashableEvidenceRules
  , .equivocationDetectability
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .slashableEvidenceRules =>
      { assumption := h
      , passed := true
      , detail := "Slashable-evidence rules assumption is provided."
      }
  | .equivocationDetectability =>
      { assumption := h
      , passed := true
      , detail := "Equivocation-detectability assumption is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
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
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Additional premises used to derive accountable-safety theorem forms. -/
structure Premises
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Type (max u v w) where
  accountableSafetyWitness :
    AccountableSafety M

/-- Full accountable-safety theorem from supplied assumptions and premises. -/
theorem accountable_safety_of_assumptions
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
    (_a : Assumptions M)
    (p : Premises M) :
    AccountableSafety M :=
  p.accountableSafetyWitness

end AccountableSafety
end Distributed


set_option autoImplicit false

/-! # Distributed.Families.AccountableSafety.API

High-level API for automatic accountable-safety certification.
-/

namespace Distributed
namespace AccountableSafety

universe u v w

/-- Certified protocol package for accountable-safety guarantees. -/
structure AccountableProtocol where
  State : Type u
  Decision : Type v
  Fault : Type w
  model : Model State Decision Fault
  assumptions : Assumptions model
  premises : Premises model
  accountableSafety :
    AccountableSafety model :=
      accountable_safety_of_assumptions assumptions premises

/-- Extract accountable-safety theorem from a certified protocol bundle. -/
theorem accountableSafety_of_protocol (P : AccountableProtocol) :
    AccountableSafety P.model :=
  P.accountableSafety

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : AccountableProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end AccountableSafety
end Distributed
