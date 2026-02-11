set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony

Reusable partial-synchrony assumptions and liveness theorems:
- eventual decision,
- bounded post-GST termination.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace PartialSynchrony

universe u v w x

/-- Minimal model interface for partial-synchrony liveness reasoning. -/
structure Model (State : Type u) (Value : Type v) (Event : Type w) (Party : Type x) where
  initial : State → Prop
  step : State → Event → Option State
  decide : State → Option Value
  eventualSynchrony : Prop
  fairPacemaker : Prop
  eventuallyCorrectLeader : Prop

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

/-- Termination bound measured from GST. -/
def BoundedTerminationAfterGST
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party)
    (FairRun : (Nat → State) → Prop)
    (gst : Nat) (bound : Nat) : Prop :=
  ∀ run, FairRun run → M.initial (run 0) →
    ∃ n, n ≤ gst + bound ∧ ∃ v, M.decide (run n) = some v

/-- Reusable core partial-synchrony assumption bundle. -/
structure Assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop where
  eventualSynchrony : M.eventualSynchrony
  fairPacemaker : M.fairPacemaker
  eventuallyCorrectLeader : M.eventuallyCorrectLeader

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | eventualSynchrony
  | fairPacemaker
  | eventuallyCorrectLeader
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable partial-synchrony assumption set. -/
def coreAssumptions : List Assumption :=
  [ .eventualSynchrony
  , .fairPacemaker
  , .eventuallyCorrectLeader
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .eventualSynchrony =>
      { assumption := h
      , passed := true
      , detail := "Eventual synchrony (GST) assumption is provided."
      }
  | .fairPacemaker =>
      { assumption := h
      , passed := true
      , detail := "Fair pacemaker assumption is provided."
      }
  | .eventuallyCorrectLeader =>
      { assumption := h
      , passed := true
      , detail := "Eventually-correct leader assumption is provided."
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

/-- Additional premises used to derive the standard DLS-style liveness forms. -/
structure Premises
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Type (max u v w x) where
  FairRun : (Nat → State) → Prop
  gst : Nat
  postGSTBound : Nat
  eventualDecisionAfterGST :
    ∀ run, FairRun run → M.initial (run 0) →
      ∃ n, gst ≤ n ∧ ∃ v, M.decide (run n) = some v
  boundedDecisionFromInitial :
    ∀ run, FairRun run → M.initial (run 0) →
      ∃ n, n ≤ gst + postGSTBound ∧ ∃ v, M.decide (run n) = some v

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

/-- Bounded post-GST termination follows under the supplied assumptions/premises. -/
theorem bounded_postGST_termination_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M)
    (p : Premises M) :
    BoundedTerminationAfterGST M p.FairRun p.gst p.postGSTBound :=
  p.boundedDecisionFromInitial

end PartialSynchrony
end Distributed


