import Protocol.Classical.Framework

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Transport Ledger

Bookkeeping for transported-theorem discharge planning in Paper 3.
This is intentionally lightweight and proof-facing (not runtime-facing).
-/

namespace ProtocolClassical

inductive LedgerPlacement where
  | mainText
  | appendixD
  deriving DecidableEq, Repr

inductive LedgerStatus where
  | planned
  | inProgress
  | discharged
  deriving DecidableEq, Repr

structure TransportLedgerEntry where
  id : String
  theoremName : String
  moduleName : String
  placement : LedgerPlacement
  status : LedgerStatus
  notes : String
  deriving DecidableEq, Repr

/-- Main-text discharged exemplar (SLA tails via LDP). -/
def mainTextExemplar : TransportLedgerEntry :=
  { id := "ldp_sla_tail"
    theoremName := "Large Deviations / SLA Tail Bounds"
    moduleName := "Classical.LargeDeviationPrinciple"
    placement := .mainText
    status := .discharged
    notes := "Discharged by Protocol.Classical.Instantiation.mainText_ldp_sla_tail." }

/-- Appendix D discharge set (current shortlist). -/
def appendixDDischargeSet : List TransportLedgerEntry :=
  [ { id := "foster_lyapunov_harris"
      theoremName := "Foster-Lyapunov-Harris Stability"
      moduleName := "Classical.FosterLyapunovHarris"
      placement := .appendixD
      status := .discharged
      notes := "Discharged by appendixD_foster_discharge." }
  , { id := "maxweight_backpressure"
      theoremName := "MaxWeight Backpressure"
      moduleName := "Classical.MaxWeightBackpressure"
      placement := .appendixD
      status := .discharged
      notes := "Discharged by appendixD_maxWeight_discharge." }
  , { id := "mixing_time_bounds"
      theoremName := "Mixing Time Bounds"
      moduleName := "Classical.MixingTimeBounds"
      placement := .appendixD
      status := .discharged
      notes := "Discharged by appendixD_mixing_discharge." }
  , { id := "mean_field_propagation_of_chaos"
      theoremName := "Mean-Field / Propagation of Chaos"
      moduleName := "Classical.PropagationOfChaos"
      placement := .appendixD
      status := .discharged
      notes := "Discharged by appendixD_meanField_discharge." } ]

def transportLedger : List TransportLedgerEntry :=
  mainTextExemplar :: appendixDDischargeSet

theorem mainTextExemplar_in_ledger :
    mainTextExemplar ∈ transportLedger := by
  simp [transportLedger]

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
