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
  evidenceForConflict : State → Decision → Decision → Fault → Prop
  verifies : State → Fault → Prop
  slashable : Fault → Prop

/-- Safety predicate: no conflicting decisions coexist in one state. -/
def SafetyHolds
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop :=
  ∀ s d₁ d₂, M.decided s d₁ → M.decided s d₂ → ¬ M.conflicts d₁ d₂

/-- Explicit accountable-fault evidence exists in a state. -/
def SlashableEvidenceForConflict
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) (s : State) (d₁ d₂ : Decision) : Prop :=
  ∃ f, M.evidenceForConflict s d₁ d₂ f ∧
    M.faultEvidence s f ∧ M.verifies s f ∧ M.slashable f

/-- Accountable safety: conflicts either do not occur or yield slashable evidence. -/
def AccountableSafety
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Prop :=
  ∀ s d₁ d₂,
    M.decided s d₁ →
    M.decided s d₂ →
    ¬ M.conflicts d₁ d₂ ∨ SlashableEvidenceForConflict M s d₁ d₂

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core accountable-safety assumption bundle. -/
structure Assumptions
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (M : Model State Decision Fault) : Type (max u v w) where
  conflictEvidenceConstructible :
    ∀ s d₁ d₂,
      M.decided s d₁ →
      M.decided s d₂ →
      M.conflicts d₁ d₂ →
      ∃ f, M.evidenceForConflict s d₁ d₂ f
  evidenceIsFaultEvidence :
    ∀ s d₁ d₂ f, M.evidenceForConflict s d₁ d₂ f → M.faultEvidence s f
  evidenceVerifies :
    ∀ s d₁ d₂ f, M.evidenceForConflict s d₁ d₂ f → M.verifies s f
  evidenceSlashable :
    ∀ s d₁ d₂ f, M.evidenceForConflict s d₁ d₂ f → M.slashable f

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | conflictEvidenceConstructible
  | evidenceIsFaultEvidence
  | evidenceVerifies
  | evidenceSlashable
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable accountable-safety assumption set. -/
def coreAssumptions : List Assumption :=
  [ .conflictEvidenceConstructible
  , .evidenceIsFaultEvidence
  , .evidenceVerifies
  , .evidenceSlashable
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .conflictEvidenceConstructible =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Conflicting decisions construct explicit fault evidence."
      }
  | .evidenceIsFaultEvidence =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Constructed conflict evidence is registered as fault evidence."
      }
  | .evidenceVerifies =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Constructed conflict evidence verifies."
      }
  | .evidenceSlashable =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Constructed conflict evidence is slashable."
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

/-! ## Main Result -/

/-- Full accountable-safety theorem from conflict evidence semantics. -/
theorem accountable_safety_of_assumptions
    {State : Type u} {Decision : Type v} {Fault : Type w}
    {M : Model State Decision Fault}
    (a : Assumptions M) :
    AccountableSafety M := by
  intro s d₁ d₂ hDec₁ hDec₂
  by_cases hConflict : M.conflicts d₁ d₂
  · rcases a.conflictEvidenceConstructible s d₁ d₂ hDec₁ hDec₂ hConflict with ⟨f, hEvidence⟩
    exact Or.inr
      ⟨ f
      , hEvidence
      , a.evidenceIsFaultEvidence s d₁ d₂ f hEvidence
      , a.evidenceVerifies s d₁ d₂ f hEvidence
      , a.evidenceSlashable s d₁ d₂ f hEvidence
      ⟩
  · exact Or.inl hConflict

end AccountableSafety
end Distributed
