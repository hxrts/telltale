import Consensus.Hypotheses
import Consensus.ClassicalValidation

set_option autoImplicit false

/-! # Consensus.Api

High-level API helpers for consensus and classical-property validation.
-/

namespace Consensus

/-- Summary of hypothesis validation for one protocol spec. -/
structure HypothesisSummary where
  space : ProtocolSpace
  results : List ValidationResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Build a hypothesis summary for an arbitrary hypothesis bundle. -/
def validateWithHypotheses (p : ProtocolSpec) (hs : List Hypothesis) : HypothesisSummary :=
  let (space, results, ok) := runValidation p hs
  { space := space, results := results, allPassed := ok }

/-- Validate the protocol against the built-in BFT hypothesis bundle. -/
def validateAsBFT (p : ProtocolSpec) : HypothesisSummary :=
  validateWithHypotheses p bftHypotheses

/-- Validate the protocol against the built-in Nakamoto hypothesis bundle. -/
def validateAsNakamoto (p : ProtocolSpec) : HypothesisSummary :=
  validateWithHypotheses p nakamotoHypotheses

/-- Validate the protocol against the built-in hybrid hypothesis bundle. -/
def validateAsHybrid (p : ProtocolSpec) : HypothesisSummary :=
  validateWithHypotheses p hybridHypotheses

/-- Validate the protocol against characterization hypotheses from `work/consensus.md`. -/
def validateCharacterization (p : ProtocolSpec) : HypothesisSummary :=
  validateWithHypotheses p characterizationHypotheses

/-- True iff every classical-property validation passed. -/
def allClassicalPassed (rs : List ClassicalValidationResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Combined summary over consensus hypotheses and classical-property checks. -/
structure CombinedSummary where
  consensus : HypothesisSummary
  classical : List ClassicalValidationResult
  classicalAllPassed : Bool
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Validate with an arbitrary hypothesis bundle and classical property set. -/
def validateWithClassical (p : ProtocolSpec) (ev : ClassicalEvidence)
    (hs : List Hypothesis) (ps : List ClassicalProperty) : CombinedSummary :=
  let c := validateWithHypotheses p hs
  let cls := validateClassicalProperties p ev ps
  let clsOk := allClassicalPassed cls
  { consensus := c
  , classical := cls
  , classicalAllPassed := clsOk
  , allPassed := c.allPassed && clsOk
  }

/-- One-shot validation using core hypotheses plus the classical core property set. -/
def validateWithClassicalCore (p : ProtocolSpec) (ev : ClassicalEvidence) : CombinedSummary :=
  validateWithClassical p ev coreHypotheses classicalCoreProperties

end Consensus

