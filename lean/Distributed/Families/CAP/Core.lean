set_option autoImplicit false

/-! # Distributed.Families.CAP

Reusable hypothesis bundles for CAP-style impossibility proofs.

This module provides:
- reusable model assumptions,
- protocol-level CAP target predicates,
- pointers to the proved impossibility theorem in `CAP.Theorem`.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace CAP

universe u v

/-- Minimal model interface for CAP reasoning. -/
structure Model (State : Type u) (Party : Type v) where
  initial : State → Prop
  partitioned : State → Prop
  available : State → Prop
  stronglyConsistent : State → Prop
  /-- Asynchronous setting assumption. -/
  asynchronous : Prop
  /-- Partition tolerance assumption for the model. -/
  partitionTolerant : Prop

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core CAP assumption bundle. -/
structure Assumptions
    {State : Type u} {Party : Type v}
    (M : Model State Party) : Prop where
  asynchronous : M.asynchronous
  partitionTolerant : M.partitionTolerant

/-- Built-in CAP assumption labels for summary/validation APIs. -/
inductive Assumption where
  | asynchronous
  | partitionTolerant
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one CAP assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable CAP assumption set. -/
def coreAssumptions : List Assumption :=
  [ .asynchronous
  , .partitionTolerant
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one CAP assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .asynchronous =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Asynchrony assumption is provided."
      }
  | .partitionTolerant =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Partition-tolerance assumption is provided."
      }

/-- Validate a list of CAP assumptions. -/
def validateAssumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of CAP assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for CAP assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Proved Impossibility

The CAP impossibility is proved (not assumed) for a concrete two-node
asynchronous register model in `Distributed.Families.CAP.Theorem`
(`Register.cap_impossible`). The former `ImpossibilityPremises`, which
supplied the inconsistent partitioned run as a hypothesis, was removed.
-/

end CAP
end Distributed
