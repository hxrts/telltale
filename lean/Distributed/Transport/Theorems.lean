import Distributed.Model.Assumptions
import Distributed.Transport.Context
import Distributed.Transport.Contracts

set_option autoImplicit false

/-! # Distributed.Transport.Theorems

High-level API helpers for consensus and classical-property validation.
-/

namespace Distributed

/-- Build an assumption summary for an arbitrary assumption bundle. -/
def validateWithAssumptions (p : ProtocolSpec) (hs : List Assumption) : AssumptionSummary :=
  runAssumptionValidation p hs

/-- Validate the protocol against the built-in BFT assumption bundle. -/
def validateAsBFT (p : ProtocolSpec) : AssumptionSummary :=
  validateWithAssumptions p bftAssumptions

/-- Validate the protocol against the built-in Nakamoto assumption bundle. -/
def validateAsNakamoto (p : ProtocolSpec) : AssumptionSummary :=
  validateWithAssumptions p nakamotoAssumptions

/-- Validate the protocol against the built-in hybrid assumption bundle. -/
def validateAsHybrid (p : ProtocolSpec) : AssumptionSummary :=
  validateWithAssumptions p hybridAssumptions

/-- Validate the protocol against characterization assumptions from `work/consensus.md`. -/
def validateCharacterization (p : ProtocolSpec) : AssumptionSummary :=
  validateWithAssumptions p characterizationAssumptions

/-- Validate with an arbitrary assumption bundle and classical property set. -/
def validateWithClassical (p : ProtocolSpec) (ev : ClassicalEvidence)
    (hs : List Assumption) (ps : List ClassicalProperty) : CombinedSummary :=
  let c := validateWithAssumptions p hs
  let cls := validateClassicalProperties p ev ps
  let clsOk := allClassicalPassed cls
  { consensus := c
  , classical := cls
  , classicalAllPassed := clsOk
  , allPassed := c.allPassed && clsOk
  }

/-- One-shot validation using core assumptions plus the classical core property set. -/
def validateWithClassicalCore (p : ProtocolSpec) (ev : ClassicalEvidence) : CombinedSummary :=
  validateWithClassical p ev coreAssumptions classicalCoreProperties

end Distributed
