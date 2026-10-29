import Protocol.Classical.Framework

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Transport Ledger

Bookkeeping for transported-theorem discharge planning in Paper 3.
This is intentionally lightweight and proof-facing (not runtime-facing).
-/

namespace ProtocolClassical

/-! ## Ledger Types -/

inductive LedgerPlacement where
  | mainText
  | appendixD
  deriving DecidableEq, Repr

/-- Discharge status of a ledger entry. `conditionalOnAssumedInput` marks a
family whose named classical theorem is an assumed witness field (Option B):
Lean derives only consequences from it. `elementaryIdentityOnly` marks a family
that proves only an elementary identity, no classical theorem. -/
inductive LedgerStatus where
  | planned
  | inProgress
  | discharged
  | conditionalOnAssumedInput
  | elementaryIdentityOnly
  deriving DecidableEq, Repr

structure TransportLedgerEntry where
  id : String
  theoremName : String
  moduleName : String
  placement : LedgerPlacement
  status : LedgerStatus
  notes : String
  deriving DecidableEq, Repr

/-! ## Canonical Entries -/

/-- Main-text exemplar (SLA tails via LDP), conditional on an assumed `LDPWitness`. -/
def mainTextExemplar : TransportLedgerEntry :=
  { id := "ldp_sla_tail"
    theoremName := "Large Deviations / SLA Tail Bounds"
    moduleName := "Classical.LargeDeviationPrinciple"
    placement := .mainText
    status := .conditionalOnAssumedInput
    notes := "Assumed exponential tail (LDPWitness); derived by main_text_ldp_sla_tail_of_witness." }

/-- Appendix D discharge set (current shortlist). -/
def appendixDDischargeSet : List TransportLedgerEntry :=
  [ { id := "foster_lyapunov_harris"
      theoremName := "Foster-Lyapunov-Harris Stability"
      moduleName := "Classical.FosterLyapunovHarris"
      placement := .appendixD
      status := .conditionalOnAssumedInput
      notes := "Deterministic drift input; appendix_d_foster_discharge. No Harris recurrence." }
  , { id := "maxweight_backpressure"
      theoremName := "MaxWeight Backpressure"
      moduleName := "Classical.MaxWeightBackpressure"
      placement := .appendixD
      status := .conditionalOnAssumedInput
      notes := "Optimality is the assumed MaxWeightChoice.optimal field; not proved." }
  , { id := "mixing_time_bounds"
      theoremName := "Mixing Time Bounds"
      moduleName := "Classical.MixingTimeBounds"
      placement := .appendixD
      status := .conditionalOnAssumedInput
      notes := "Assumed geometric envelope (MixingWitness); appendix_d_mixing_discharge." }
  , { id := "mean_field_propagation_of_chaos"
      theoremName := "Mean-Field / Propagation of Chaos"
      moduleName := "Classical.PropagationOfChaos"
      placement := .appendixD
      status := .elementaryIdentityOnly
      notes := "Finite-average reindexing identity only; no mean-field limit." } ]

/-! ## Aggregated Ledger and Basic Facts -/

/-- Full ledger: main-text exemplar followed by the Appendix D set. -/
def transportLedger : List TransportLedgerEntry :=
  mainTextExemplar :: appendixDDischargeSet

/-- The main-text exemplar is in the ledger. -/
theorem main_text_exemplar_in_ledger :
    mainTextExemplar ∈ transportLedger := by
  simp [transportLedger]

/-- Every Appendix D entry is tagged with the Appendix D placement. -/
theorem appendix_entries_tagged :
    ∀ e ∈ appendixDDischargeSet, e.placement = .appendixD := by
  intro e hMem
  simp [appendixDDischargeSet] at hMem
  rcases hMem with h | h | h | h
  · simp [h]
  · simp [h]
  · simp [h]
  · simp [h]

end ProtocolClassical
