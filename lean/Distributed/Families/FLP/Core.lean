set_option autoImplicit false

/-! # Distributed.Families.FLP

Reusable hypothesis bundles for FLP-style lower-bound proofs.

This module provides abstract model assumption labels and a small validation
API. The impossibility theorem is proved in `Distributed.Families.FLP.Theorem`.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace FLP

universe u v w x

/-- Minimal asynchronous consensus model interface for FLP reasoning. -/
structure Model (State : Type u) (Value : Type v) (Event : Type w) (Party : Type x) where
  initial : State → Prop
  step : State → Event → Option State
  decide : State → Option Value
  validValue : Value → Prop
  /-- Reachability relation used by the proof layer (can encode multi-step semantics). -/
  reachable : State → State → Prop
  /-- Asynchrony/no-oracle assumption statement for this model. -/
  asynchronous : Prop
  /-- Crash resilience to one failed party (model-level statement). -/
  crashResilientOne : Prop

/-- Deterministic transition semantics. -/
def Deterministic
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop :=
  ∀ s e s₁ s₂, M.step s e = some s₁ → M.step s e = some s₂ → s₁ = s₂

/-- Agreement: two decided states cannot decide conflicting values. -/
def Agreement
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop :=
  ∀ s₁ s₂ v₁ v₂, M.decide s₁ = some v₁ → M.decide s₂ = some v₂ → v₁ = v₂

/-- Validity: only model-valid values can be decided from initial executions. -/
def Validity
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop :=
  ∀ s v, M.initial s → M.decide s = some v → M.validValue v

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core FLP assumption bundle.
Any FLP theorem can depend on this single object instead of repeating assumptions. -/
structure Assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Prop where
  asynchronous : M.asynchronous
  deterministic : Deterministic M
  crashResilientOne : M.crashResilientOne
  agreement : Agreement M
  validity : Validity M

/-- Built-in FLP assumption labels for summary/validation APIs. -/
inductive Assumption where
  | asynchronous
  | deterministic
  | crashResilientOne
  | agreement
  | validity
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one FLP assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable FLP assumption set. -/
def coreAssumptions : List Assumption :=
  [ .asynchronous
  , .deterministic
  , .crashResilientOne
  , .agreement
  , .validity
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle.
Because `Assumptions` stores proofs, each requested atom is certified true. -/
def validateAssumption
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .asynchronous =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Asynchrony/no-oracle assumption is provided."
      }
  | .deterministic =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Deterministic transition semantics assumption is provided."
      }
  | .crashResilientOne =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Crash resilience with one failed party is provided."
      }
  | .agreement =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Agreement assumption is provided."
      }
  | .validity =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Validity assumption is provided."
      }

/-- Validate a list of FLP assumptions. -/
def validateAssumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of FLP assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for FLP assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Assumption Projection Lemmas -/

/-- Standard projection lemma: extract the deterministic assumption for reuse. -/
theorem deterministic_of
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) : Deterministic M :=
  a.deterministic

/-- Standard projection lemma: extract agreement for reuse. -/
theorem agreement_of
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) : Agreement M :=
  a.agreement

/-- Standard projection lemma: extract validity for reuse. -/
theorem validity_of
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) : Validity M :=
  a.validity

/-! ## Termination Predicates -/

/-- A run eventually decides if some index yields a decision value. -/
def EventuallyDecidesOnRun
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) (run : Nat → State) : Prop :=
  ∃ n v, M.decide (run n) = some v

/-- Universal termination property over a designated fairness predicate. -/
def TerminatesOnAllFairRuns
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party)
    (FairRun : (Nat → State) → Prop) : Prop :=
  ∀ run, FairRun run → M.initial (run 0) → EventuallyDecidesOnRun M run

/-! ## Proved Impossibility

The FLP impossibility itself is proved (not assumed) for the concrete
asynchronous message-passing model in `Distributed.Families.FLP.Theorem`
(`Async.flp_impossibility`); the abstract `Model` above only carries the
assumption-label validation API. The former `LowerBoundPremises` /
`ImpossibilityPremises` (which assumed the valency argument) were removed.
-/

end FLP
end Distributed
