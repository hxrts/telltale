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
  optimisticPreconditions : Prop
  authenticationStrong : Prop
  leaderQuality : Prop

/-- A run eventually decides if some index yields a decision value. -/
def EventuallyDecidesOnRun
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) : Prop :=
  ∃ n v, M.decide (run n) = some v

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

/-- Reusable core responsiveness assumption bundle. -/
structure Assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop where
  optimisticPreconditions : M.optimisticPreconditions
  authenticationStrong : M.authenticationStrong
  leaderQuality : M.leaderQuality

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | optimisticPreconditions
  | authenticationStrong
  | leaderQuality
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable responsiveness assumption set. -/
def coreAssumptions : List Assumption :=
  [ .optimisticPreconditions
  , .authenticationStrong
  , .leaderQuality
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .optimisticPreconditions =>
      { assumption := h
      , passed := true
      , detail := "Optimistic responsiveness preconditions are provided."
      }
  | .authenticationStrong =>
      { assumption := h
      , passed := true
      , detail := "Authentication-strength precondition is provided."
      }
  | .leaderQuality =>
      { assumption := h
      , passed := true
      , detail := "Leader-quality precondition is provided."
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

/-- Additional premises used to derive responsiveness theorem forms. -/
structure Premises
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Type (max u v w x) where
  FairRun : (Nat → State) → Prop
  gst : Nat
  optimisticBound : Nat
  eventualDecisionAfterGST :
    ∀ run, FairRun run → M.initial (run 0) →
      ∃ n, gst ≤ n ∧ ∃ v, M.decide (run n) = some v
  timeoutIndependentBound :
    ∀ timeout : Nat, ∀ run, FairRun run → M.initial (run 0) →
      ∃ n, n ≤ gst + optimisticBound ∧ ∃ v, M.decide (run n) = some v

/-- Eventual decision follows under the supplied assumptions and premises. -/
theorem eventual_decision_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M)
    (p : Premises M) :
    TerminatesOnAllFairRuns M p.FairRun := by
  intro run hFair hInit
  rcases p.eventualDecisionAfterGST run hFair hInit with ⟨n, _hGST, v, hDec⟩
  exact ⟨n, v, hDec⟩

/-- Timeout-independent post-GST latency bound from the supplied premises. -/
theorem timeout_independent_latency_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M)
    (p : Premises M) :
    TimeoutIndependentLatencyBound M p.FairRun p.gst p.optimisticBound :=
  p.timeoutIndependentBound

end Responsiveness
end Distributed


