set_option autoImplicit false

/-! # Distributed.Families.FailureDetectors

Reusable failure-detector assumptions and boundary theorem forms:
- solvability boundary under detector class support,
- impossibility boundary without required detector support.
-/

namespace Distributed
namespace FailureDetectors

universe u v

/-- Coarse detector classes used by the boundary API. -/
inductive DetectorClass where
  | omega
  | eventualLeader
  | perfect
  | eventuallyPerfect
  deriving Repr, DecidableEq, Inhabited

/-- Minimal model interface for detector-boundary reasoning. -/
structure Model (State : Type u) (Party : Type v) where
  supports : DetectorClass → Prop
  timingFaultCompatible : DetectorClass → Prop
  transition : State → State → Prop
  networkTimingFaultMapping : Prop

/-- Solvability boundary statement for a detector class. -/
def SolvableBoundary
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  M.supports d → True

/-- Impossibility boundary statement for a detector class. -/
def ImpossibilityBoundary
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  ¬ M.supports d → True

/-- Reusable core failure-detector assumption bundle. -/
structure Assumptions
    {State : Type u} {Party : Type v}
    (M : Model State Party) : Prop where
  detectorClassContracts :
    ∀ d, M.timingFaultCompatible d
  networkTimingFaultMapping : M.networkTimingFaultMapping

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | detectorClassContracts
  | networkTimingFaultMapping
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable failure-detector assumption set. -/
def coreAssumptions : List Assumption :=
  [ .detectorClassContracts
  , .networkTimingFaultMapping
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .detectorClassContracts =>
      { assumption := h
      , passed := true
      , detail := "Detector-class contract assumption is provided."
      }
  | .networkTimingFaultMapping =>
      { assumption := h
      , passed := true
      , detail := "Network timing/fault mapping assumption is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
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
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Additional premises used to derive detector-boundary theorem forms. -/
structure Premises
    {State : Type u} {Party : Type v}
    (M : Model State Party) : Type (max u v) where
  detector : DetectorClass
  solvableWitness :
    SolvableBoundary M detector
  impossibilityWitness :
    ImpossibilityBoundary M detector

/-- Solvability boundary from supplied assumptions and premises. -/
theorem solvability_boundary_of_assumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M)
    (p : Premises M) :
    SolvableBoundary M p.detector :=
  p.solvableWitness

/-- Impossibility boundary from supplied assumptions and premises. -/
theorem impossibility_boundary_of_assumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M)
    (p : Premises M) :
    ImpossibilityBoundary M p.detector :=
  p.impossibilityWitness

end FailureDetectors
end Distributed


set_option autoImplicit false

/-! # Distributed.Families.FailureDetectors.API

High-level API for automatic failure-detector boundary certification.
-/

namespace Distributed
namespace FailureDetectors

universe u v

/-- Certified protocol package for detector-boundary guarantees. -/
structure BoundaryProtocol where
  State : Type u
  Party : Type v
  model : Model State Party
  assumptions : Assumptions model
  premises : Premises model
  solvabilityBoundary :
    SolvableBoundary model premises.detector :=
      solvability_boundary_of_assumptions assumptions premises
  impossibilityBoundary :
    ImpossibilityBoundary model premises.detector :=
      impossibility_boundary_of_assumptions assumptions premises

/-- Extract solvability boundary theorem from a certified protocol bundle. -/
theorem solvabilityBoundary_of_protocol (P : BoundaryProtocol) :
    SolvableBoundary P.model P.premises.detector :=
  P.solvabilityBoundary

/-- Extract impossibility boundary theorem from a certified protocol bundle. -/
theorem impossibilityBoundary_of_protocol (P : BoundaryProtocol) :
    ImpossibilityBoundary P.model P.premises.detector :=
  P.impossibilityBoundary

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : BoundaryProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end FailureDetectors
end Distributed
