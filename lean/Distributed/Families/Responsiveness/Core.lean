set_option autoImplicit false

/-! # Distributed.Families.Responsiveness

Reusable responsiveness assumptions and theorem forms:
- eventual decision,
- responsive latency bound independent of timeout after GST.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace Responsiveness

universe u v w x

/-- Minimal model interface for responsiveness reasoning. -/
structure Model (State : Type u) (Value : Type v) (Event : Type w) (Party : Type x) where
  initial : State → Prop
  step : State → Event → Option State
  decide : State → Option Value
  optimisticNetworkWindow : (Nat → State) → Nat → Nat → Prop
  authenticationStrongAfterGST : (Nat → State) → Nat → Prop
  leaderResponsiveWindow : (Nat → State) → Nat → Nat → Prop
  timeoutAdmissible : Nat → (Nat → State) → Prop

/-- A run eventually decides if some index yields a decision value. -/
def EventuallyDecidesOnRun
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) : Prop :=
  ∃ n v, M.decide (run n) = some v

/-- A run decides at a concrete logical time. -/
def DecidesAt
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) (n : Nat) : Prop :=
  ∃ v, M.decide (run n) = some v

/-- The optimistic post-GST portion of a run contains a decision. -/
def OptimisticPostGSTDecision
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) (gst : Nat) : Prop :=
  ∃ n, gst ≤ n ∧ DecidesAt M run n

/-- A run decides inside the timeout-independent optimistic window. -/
def TimeoutIndependentDecisionWindow
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State)
    (gst : Nat) (optimisticBound : Nat) : Prop :=
  ∀ _timeout : Nat, ∃ offset, offset ≤ optimisticBound ∧ DecidesAt M run (gst + offset)

/-- Universal termination over a designated fair-run predicate. -/
def TerminatesOnAllFairRuns
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party)
    (FairRun : (Nat → State) → Prop) : Prop :=
  ∀ run, FairRun run → M.initial (run 0) → EventuallyDecidesOnRun M run

/-- Responsiveness form: post-GST decision bound does not depend on timeout. -/
def TimeoutIndependentLatencyBound
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party)
    (FairRun : (Nat → State) → Prop)
    (gst : Nat) (optimisticBound : Nat) : Prop :=
  ∀ timeout : Nat, ∀ run, FairRun run → M.initial (run 0) →
    ∃ n, n ≤ gst + optimisticBound ∧ ∃ v, M.decide (run n) = some v

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core responsiveness assumption bundle. -/
structure Assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Type (max u v w x) where
  FairRun : (Nat → State) → Prop
  gst : Nat
  optimisticBound : Nat
  optimisticNetwork :
    ∀ run, FairRun run → M.initial (run 0) →
      M.optimisticNetworkWindow run gst optimisticBound
  authenticationStrong :
    ∀ run, FairRun run → M.initial (run 0) → M.authenticationStrongAfterGST run gst
  leaderQuality :
    ∀ run, FairRun run → M.initial (run 0) →
      M.leaderResponsiveWindow run gst optimisticBound
  timeoutSchedule :
    ∀ timeout run, FairRun run → M.initial (run 0) → M.timeoutAdmissible timeout run
  optimisticProgress :
    ∀ run, FairRun run → M.initial (run 0) → OptimisticPostGSTDecision M run gst
  timeoutIndependentProgress :
    ∀ timeout run, FairRun run → M.initial (run 0) → M.timeoutAdmissible timeout run →
      TimeoutIndependentDecisionWindow M run gst optimisticBound

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | fairRunSemantics
  | optimisticNetwork
  | authenticationStrong
  | leaderQuality
  | timeoutSchedule
  | optimisticProgress
  | timeoutIndependentProgress
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable responsiveness assumption set. -/
def coreAssumptions : List Assumption :=
  [ .fairRunSemantics
  , .optimisticNetwork
  , .authenticationStrong
  , .leaderQuality
  , .timeoutSchedule
  , .optimisticProgress
  , .timeoutIndependentProgress
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .fairRunSemantics =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "A reusable fair-run predicate, GST, and optimistic bound are provided."
      }
  | .optimisticNetwork =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Fair initial runs satisfy the optimistic network window."
      }
  | .authenticationStrong =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Fair initial runs satisfy authentication strength after GST."
      }
  | .leaderQuality =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Fair initial runs satisfy the responsive leader-quality window."
      }
  | .timeoutSchedule =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Timeout schedules considered by the latency theorem are admissible."
      }
  | .optimisticProgress =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Optimistic fair initial runs have a decision after GST."
      }
  | .timeoutIndependentProgress =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Optimistic fair initial runs decide within a timeout-independent window."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
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
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Derived Responsiveness Results -/

/-- Eventual decision follows from optimistic post-GST progress. -/
theorem eventual_decision_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) :
    TerminatesOnAllFairRuns M a.FairRun := by
  intro run hFair hInit
  rcases a.optimisticProgress run hFair hInit with ⟨n, _hGST, v, hDec⟩
  exact ⟨n, v, hDec⟩

/-- Timeout-independent post-GST latency bound from optimistic progress windows. -/
theorem timeout_independent_latency_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) :
    TimeoutIndependentLatencyBound M a.FairRun a.gst a.optimisticBound := by
  intro timeout run hFair hInit
  have hTimeout := a.timeoutSchedule timeout run hFair hInit
  rcases a.timeoutIndependentProgress timeout run hFair hInit hTimeout timeout with
    ⟨offset, hOffset, v, hDec⟩
  exact ⟨a.gst + offset, Nat.add_le_add_left hOffset a.gst, v, hDec⟩

end Responsiveness
end Distributed
