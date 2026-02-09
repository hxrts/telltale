set_option autoImplicit false

/-! # Distributed.Families.FLP.Assumptions

Reusable hypothesis bundles for FLP-style lower-bound proofs.

This module intentionally separates:
- protocol/model assumptions (`Assumptions`), reusable across theorems
- lower-bound-specific construction premises (`LowerBoundPremises`)
- a small validation API mirroring the style used in `Distributed.Model.Assumptions`
-/

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

/-- Validate one assumption against an assumption bundle.
Because `Assumptions` stores proofs, each requested atom is certified true. -/
def validateAssumption
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .asynchronous =>
      { assumption := h
      , passed := true
      , detail := "Asynchrony/no-oracle assumption is provided."
      }
  | .deterministic =>
      { assumption := h
      , passed := true
      , detail := "Deterministic transition semantics assumption is provided."
      }
  | .crashResilientOne =>
      { assumption := h
      , passed := true
      , detail := "Crash resilience with one failed party is provided."
      }
  | .agreement =>
      { assumption := h
      , passed := true
      , detail := "Agreement assumption is provided."
      }
  | .validity =>
      { assumption := h
      , passed := true
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

/-- Additional premises typically discharged by FLP valency lemmas.
This isolates the two-step FLP proof pattern into reusable inputs. -/
structure LowerBoundPremises
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party) : Type (max u v w x) where
  Uncommitted : State → Prop
  FairRun : (Nat → State) → Prop
  initialUncommitted : ∃ s, M.initial s ∧ Uncommitted s
  /-- "There exists an infinite fair extension staying uncommitted" premise. -/
  fairUncommittedExtension : ∀ s, Uncommitted s →
    ∃ run, run 0 = s ∧ FairRun run ∧ ∀ n, Uncommitted (run n)

/-- Stronger premises for the full FLP impossibility statement:
    uncommitted states are precisely non-deciding states for the lower-bound run. -/
structure ImpossibilityPremises
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (M : Model State Value Event Party)
    : Type (max u v w x) extends LowerBoundPremises M where
  uncommittedNotDeciding : ∀ s, Uncommitted s → M.decide s = none

/-- FLP lower-bound shape from reusable assumptions + valency premises.
This theorem is the reusable endpoint consumed by concrete FLP instantiations. -/
theorem lowerBound_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M)
    (p : LowerBoundPremises M) :
    ∃ run, p.FairRun run ∧ ∀ n, p.Uncommitted (run n) := by
  rcases p.initialUncommitted with ⟨s₀, _hInit, hUncommitted⟩
  rcases p.fairUncommittedExtension s₀ hUncommitted with ⟨run, _h0, hFair, hAll⟩
  exact ⟨run, hFair, hAll⟩

/-- Construct a fair initial run that never decides, from full FLP premises. -/
theorem nonterminatingRun_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (_a : Assumptions M)
    (p : ImpossibilityPremises M) :
    ∃ run, p.FairRun run ∧ M.initial (run 0) ∧ ∀ n, M.decide (run n) = none := by
  rcases p.initialUncommitted with ⟨s₀, hInit, hUncommitted⟩
  rcases p.fairUncommittedExtension s₀ hUncommitted with ⟨run, h0, hFair, hAll⟩
  refine ⟨run, hFair, ?_, ?_⟩
  · simpa [h0] using hInit
  · intro n
    exact p.uncommittedNotDeciding _ (hAll n)

/-- Full FLP impossibility form: no deterministic async crash-resilient protocol
    can guarantee decision on all fair runs under the supplied valency premises. -/
theorem impossibility_of_assumptions
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    {M : Model State Value Event Party}
    (a : Assumptions M)
    (p : ImpossibilityPremises M) :
    ¬ TerminatesOnAllFairRuns M p.FairRun := by
  intro hTerm
  rcases nonterminatingRun_of_assumptions a p with ⟨run, hFair, hInit, hNone⟩
  rcases hTerm run hFair hInit with ⟨n, v, hDec⟩
  have hNoDec : M.decide (run n) = none := hNone n
  rw [hNoDec] at hDec
  cases hDec

end FLP
end Distributed


set_option autoImplicit false

/-! # Distributed.Families.FLP.API

High-level API for automatic FLP lower-bound certification.

When a protocol instance is built with the reusable FLP hypotheses and the
standard lower-bound premises, the FLP non-termination witness theorem is
materialized automatically.
-/

namespace Distributed
namespace FLP

universe u v w x

/-- A protocol packaged for FLP lower-bound certification.

`lowerBound` has a default proof term, so users only provide model assumptions
and valency-style premises; the theorem is derived automatically. -/
structure LowerBoundProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : LowerBoundPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_assumptions assumptions premises

/-- Stronger protocol package: includes premises sufficient to derive
the full FLP impossibility (negation of universal fair-run termination). -/
structure ImpossibilityProtocol where
  State : Type u
  Value : Type v
  Event : Type w
  Party : Type x
  model : Model State Value Event Party
  assumptions : Assumptions model
  premises : ImpossibilityPremises model
  lowerBound :
    ∃ run, premises.FairRun run ∧ ∀ n, premises.Uncommitted (run n) :=
      lowerBound_of_assumptions assumptions premises.toLowerBoundPremises
  impossibility :
    ¬ TerminatesOnAllFairRuns model premises.FairRun :=
      impossibility_of_assumptions assumptions premises

/-- Extract the FLP lower-bound theorem from a certified protocol bundle. -/
theorem lowerBound_of_protocol (P : LowerBoundProtocol) :
    ∃ run, P.premises.FairRun run ∧ ∀ n, P.premises.Uncommitted (run n) :=
  P.lowerBound

/-- Extract the full FLP impossibility theorem from a full protocol bundle. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) :
    ¬ TerminatesOnAllFairRuns P.model P.premises.FairRun :=
  P.impossibility

/-- Runtime-style certificate object for downstream APIs. -/
structure LowerBoundCertificate (P : LowerBoundProtocol) where
  run : Nat → P.State
  fair : P.premises.FairRun run
  uncommitted : ∀ n, P.premises.Uncommitted (run n)

/-- Materialize an explicit certificate from a certified protocol bundle. -/
noncomputable def certify (P : LowerBoundProtocol) : LowerBoundCertificate P := by
  classical
  refine ⟨Classical.choose P.lowerBound, ?_, ?_⟩
  · exact (Classical.choose_spec P.lowerBound).1
  · exact (Classical.choose_spec P.lowerBound).2

/-- FLP core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : LowerBoundProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

/-- FLP core assumptions are always validated for a certified full protocol. -/
theorem coreAssumptions_allPassed_impossibility (P : ImpossibilityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end FLP
end Distributed
