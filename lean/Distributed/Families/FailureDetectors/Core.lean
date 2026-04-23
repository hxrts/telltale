set_option autoImplicit false

/-! # Distributed.Families.FailureDetectors

Reusable failure-detector assumptions and boundary theorem forms:
- solvability boundary under detector class support,
- impossibility boundary without required detector support.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

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
  solvesConsensus : DetectorClass → Prop
  transition : State → State → Prop
  networkTimingFaultMapping : Prop

/-- Solvability boundary statement for a detector class. -/
def SolvableBoundary
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  M.supports d → M.solvesConsensus d

/-- Impossibility boundary statement for a detector class. -/
def ImpossibilityBoundary
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  M.timingFaultCompatible d → ¬ M.supports d → ¬ M.solvesConsensus d

/-- Detector implementability under the model's timing/fault mapping. -/
def DetectorImplementable
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  M.timingFaultCompatible d ∧ M.supports d

/-- Detector reduction obligation: consensus reduces to the detector class. -/
def ConsensusReducesToDetector
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  DetectorImplementable M d → M.solvesConsensus d

/-- Unsupported compatible detector classes cannot implement the consensus target. -/
def DetectorClassTooWeak
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (d : DetectorClass) : Prop :=
  M.timingFaultCompatible d → ¬ M.supports d → ¬ M.solvesConsensus d

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core failure-detector assumption bundle. -/
structure Assumptions
    {State : Type u} {Party : Type v}
    (M : Model State Party) where
  detectorClassContracts :
    ∀ d, M.timingFaultCompatible d
  networkTimingFaultMapping : M.networkTimingFaultMapping
  supportedCompatibleDetectorSolves :
    ∀ d, ConsensusReducesToDetector M d
  unsupportedCompatibleDetectorCannotSolve :
    ∀ d, DetectorClassTooWeak M d

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

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .detectorClassContracts =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Detector-class contract assumption is provided."
      }
  | .networkTimingFaultMapping =>
      { assumption := h
      , passed := proofCarryingValidationPassed
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

/-! ## Derived Boundaries -/

/-- Solvability boundary from supplied assumptions and premises. -/
theorem solvability_boundary_of_assumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M)
    (detector : DetectorClass) :
    SolvableBoundary M detector := by
  intro hSupports
  exact a.supportedCompatibleDetectorSolves detector
    ⟨a.detectorClassContracts detector, hSupports⟩

/-- Impossibility boundary from supplied assumptions and premises. -/
theorem impossibility_boundary_of_assumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M)
    (detector : DetectorClass) :
    ImpossibilityBoundary M detector :=
  a.unsupportedCompatibleDetectorCannotSolve detector

end FailureDetectors
end Distributed
