import Distributed.Families.PartialSynchrony.Rounds

set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony

Reusable partial-synchrony assumptions and liveness theorems:
- eventual decision,
- bounded post-GST termination.
-/

/-
The Problem. Earlier versions assumed post-GST progress and bounded-window
progress directly; those fields were the liveness conclusions.
Solution Structure. Each fair run refines a concrete view-based execution
(`Rounds`) with GST, post-GST delay bound `Δ`, and rotating leaders; progress
is proved there (`Rounds.decided_after_gst`) and transported along the
refinement.
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

/-- The post-GST portion of a run contains a decision. -/
def PostGSTDecision
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) (gst : Nat) : Prop :=
  ∃ n, gst ≤ n ∧ DecidesAt M run n

/-- A run decides inside the configured post-GST latency window. -/
def BoundedDecisionWindow
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State)
    (gst : Nat) (bound : Nat) : Prop :=
  ∃ offset, offset ≤ bound ∧ DecidesAt M run (gst + offset)

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

/-! ## Assumption Atoms and Contracts -/

/-- Partial-synchrony assumptions. The only link to the abstract model is a
refinement: once the concrete execution has decided, the abstract state
reports a decision. Progress itself is proved, not assumed. -/
structure Assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Type (max u v w x) where
  FairRun : (Nat → State) → Prop
  params : Rounds.Params
  timing : params.TimingOK
  realizedByRounds :
    ∀ run, FairRun run → M.initial (run 0) →
      ∃ R : Rounds.RoundRun, Rounds.Admissible params R ∧ Rounds.HasHonest params R ∧
        ∀ t, Rounds.DecidedBy params R t → ∃ v, M.decide (run t) = some v

variable {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
  {M : Model State Value Event Party}

/-- Global stabilisation time. -/
def Assumptions.gst (a : Assumptions M) : Nat := a.params.gst

/-- Post-GST message-delay bound `Δ`. -/
def Assumptions.messageDelayBound (a : Assumptions M) : Nat := a.params.delta

/-- Derived post-GST decision latency `(2n+1)·L`. -/
def Assumptions.postGSTBound (a : Assumptions M) : Nat := Rounds.latencyBound a.params

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | timing
  | realizedByRounds
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable partial-synchrony assumption set. -/
def coreAssumptions : List Assumption :=
  [.timing, .realizedByRounds]

/-! ## Assumption Validation API -/

/-- Constant `true` for the refinement field: it quantifies over all fair runs
and cannot be decided; the bundle's type carries its proof. -/
def proofCarriedNoRuntimeCheck : Bool :=
  true

/-- Validate one assumption: `timing` is decided over the concrete parameters. -/
def validateAssumption (a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .timing =>
      { assumption := h, passed := decide a.params.TimingOK
      , detail := "0 < n, 0 < L and 2Δ ≤ L." }
  | .realizedByRounds =>
      { assumption := h, passed := proofCarriedNoRuntimeCheck
      , detail := "Fair runs refine an admissible view-based execution with an honest party." }

/-- Soundness of the decided label. -/
theorem validateAssumption_timing_sound (P : Rounds.Params)
    (h : decide P.TimingOK = true) : P.TimingOK :=
  of_decide_eq_true h

/-- Validate a list of assumptions. -/
def validateAssumptions (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
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
def runAssumptionValidation (a : Assumptions M) (hs : List Assumption) : AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Derived Liveness Results -/

/-- Bounded post-GST termination, proved from the concrete round model. -/
theorem bounded_post_gst_termination_of_assumptions (a : Assumptions M) :
    BoundedTerminationAfterGST M a.FairRun a.gst a.postGSTBound := by
  intro run hFair hInit
  obtain ⟨R, hAdm, hHon, hRef⟩ := a.realizedByRounds run hFair hInit
  exact ⟨_, le_rfl, hRef _ (Rounds.decided_after_gst a.params R a.timing hAdm hHon)⟩

/-- Eventual decision follows from bounded post-GST termination. -/
theorem eventual_decision_of_assumptions (a : Assumptions M) :
    TerminatesOnAllFairRuns M a.FairRun := by
  intro run hFair hInit
  obtain ⟨n, _, v, hv⟩ := bounded_post_gst_termination_of_assumptions a run hFair hInit
  exact ⟨n, v, hv⟩

/-- Post-GST decision within the bounded window. -/
theorem post_gst_decision_of_assumptions (a : Assumptions M) (run : Nat → State)
    (hFair : a.FairRun run) (hInit : M.initial (run 0)) :
    BoundedDecisionWindow M run a.gst a.postGSTBound := by
  obtain ⟨R, hAdm, hHon, hRef⟩ := a.realizedByRounds run hFair hInit
  exact ⟨_, le_rfl, hRef _ (Rounds.decided_after_gst a.params R a.timing hAdm hHon)⟩

end PartialSynchrony
end Distributed
