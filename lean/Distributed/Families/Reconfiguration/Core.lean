set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration

Reusable reconfiguration assumptions and theorem forms:
- no split-brain across reconfiguration,
- safe handoff,
- liveness preservation.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace Reconfiguration

universe u v w x

/-- Minimal model interface for reconfiguration reasoning. -/
structure Model (State : Type u) (Decision : Type v) (Certificate : Type w) where
  transitionStep : State → State → Prop
  epoch : State → Nat
  transitionCertified : State → Nat → Certificate → Prop
  committed : State → Decision → Prop
  live : State → Prop
  conflicts : Decision → Decision → Prop

/-- No-split-brain property across one reconfiguration step. -/
def NoSplitBrainAcrossReconfiguration
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    (M : Model State Decision Certificate) : Prop :=
  ∀ {sOld sNew dOld dNew},
    M.transitionStep sOld sNew →
    M.committed sOld dOld →
    M.committed sNew dNew →
    ¬ M.conflicts dOld dNew

/-- Safe-handoff property across one reconfiguration step. -/
def SafeHandoff
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    (M : Model State Decision Certificate) : Prop :=
  ∀ {sOld sNew d},
    M.transitionStep sOld sNew →
    M.committed sOld d →
    M.committed sNew d

/-- Liveness-preservation property across one reconfiguration step. -/
def LivenessPreserved
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    (M : Model State Decision Certificate) : Prop :=
  ∀ {sOld sNew},
    M.transitionStep sOld sNew →
    M.live sOld →
    M.live sNew

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core reconfiguration assumption bundle. -/
structure Assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    (M : Model State Decision Certificate) where
  Participant : Type x
  signer : Certificate → Participant → Prop
  epochTransitionCertificates :
    ∀ {sOld sNew},
      M.transitionStep sOld sNew →
      ∃ c, M.transitionCertified sNew (M.epoch sNew) c
  committedCarriesEpochCertificate :
    ∀ {s d},
      M.committed s d →
      ∃ c, M.transitionCertified s (M.epoch s) c
  oldNewQuorumOverlap :
    ∀ {sOld sNew cOld cNew},
      M.transitionStep sOld sNew →
      M.transitionCertified sOld (M.epoch sOld) cOld →
      M.transitionCertified sNew (M.epoch sNew) cNew →
      ∃ p, signer cOld p ∧ signer cNew p
  epochMonotonicity :
    ∀ {sOld sNew},
      M.transitionStep sOld sNew →
      M.epoch sOld ≤ M.epoch sNew
  overlapSignerExcludesConflict :
    ∀ {sOld sNew cOld cNew p dOld dNew},
      M.transitionStep sOld sNew →
      M.transitionCertified sOld (M.epoch sOld) cOld →
      M.transitionCertified sNew (M.epoch sNew) cNew →
      signer cOld p →
      signer cNew p →
      M.committed sOld dOld →
      M.committed sNew dNew →
      ¬ M.conflicts dOld dNew
  handoffPreservesCommittedPrefix :
    ∀ {sOld sNew d},
      M.transitionStep sOld sNew →
      M.committed sOld d →
      M.committed sNew d
  progressPreservedByMonotoneEpoch :
    ∀ {sOld sNew},
      M.transitionStep sOld sNew →
      M.epoch sOld ≤ M.epoch sNew →
      M.live sOld →
      M.live sNew

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | epochTransitionCertificates
  | oldNewQuorumOverlap
  | epochMonotonicity
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable reconfiguration assumption set. -/
def coreAssumptions : List Assumption :=
  [ .epochTransitionCertificates
  , .oldNewQuorumOverlap
  , .epochMonotonicity
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .epochTransitionCertificates =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Epoch-transition certificate assumption is provided."
      }
  | .oldNewQuorumOverlap =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Old/new quorum overlap assumption is provided."
      }
  | .epochMonotonicity =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Epoch monotonicity assumption is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
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
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Derived Results -/

/-- No split-brain follows under the supplied assumptions and premises. -/
theorem no_split_brain_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
    (a : Assumptions M) :
    NoSplitBrainAcrossReconfiguration M := by
  intro sOld sNew dOld dNew hStep hOld hNew
  rcases a.committedCarriesEpochCertificate hOld with ⟨cOld, hCertOld⟩
  rcases a.committedCarriesEpochCertificate hNew with ⟨cNew, hCertNew⟩
  rcases a.oldNewQuorumOverlap hStep hCertOld hCertNew with ⟨p, hSignOld, hSignNew⟩
  exact
    a.overlapSignerExcludesConflict
      hStep hCertOld hCertNew hSignOld hSignNew hOld hNew

/-- Safe handoff follows under the supplied assumptions and premises. -/
theorem safe_handoff_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
    (a : Assumptions M) :
    SafeHandoff M :=
  a.handoffPreservesCommittedPrefix

/-- Liveness preservation follows under the supplied assumptions and premises. -/
theorem liveness_preserved_of_assumptions
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    {M : Model State Decision Certificate}
    (a : Assumptions M) :
    LivenessPreserved M := by
  intro sOld sNew hStep hLive
  exact a.progressPreservedByMonotoneEpoch hStep (a.epochMonotonicity hStep) hLive

end Reconfiguration
end Distributed
