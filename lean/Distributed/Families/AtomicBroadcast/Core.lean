set_option autoImplicit false

/-! # Distributed.Families.AtomicBroadcast

Reusable atomic-broadcast assumptions and theorem forms:
- total-order consistency,
- log-prefix compatibility,
- consensus <-> atomic-broadcast bridge.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace AtomicBroadcast

universe u v w

/-- Minimal model interface for atomic-broadcast reasoning. -/
structure Model (State : Type u) (Message : Type v) (Value : Type w) where
  initial : State → Prop
  log : State → List Message
  decide : State → Option Value
  messageValue : Message → Option Value
  reliableBroadcast : Prop
  agreementPremise : Prop
  orderingPremise : Prop

/-- List-prefix predicate. -/
def IsPrefix {α : Type u} (xs ys : List α) : Prop :=
  ∃ tail, ys = xs ++ tail

/-- Total-order consistency predicate over delivered logs. -/
def TotalOrderConsistency
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop :=
  ∀ s₁ s₂ m,
    m ∈ M.log s₁ ↔ m ∈ M.log s₂

/-- Log-prefix compatibility predicate over delivered logs. -/
def LogPrefixCompatibility
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop :=
  ∀ s₁ s₂,
    IsPrefix (M.log s₁) (M.log s₂) ∨ IsPrefix (M.log s₂) (M.log s₁)

/-- Consensus-style agreement induced by atomic-broadcast state. -/
def ConsensusAgreement
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop :=
  ∀ s₁ s₂ v₁ v₂,
    M.decide s₁ = some v₁ →
    M.decide s₂ = some v₂ →
    v₁ = v₂

/-- Atomic-broadcast log carries decided values. -/
def AtomicBroadcastCarriesDecision
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop :=
  ∀ s v,
    M.decide s = some v →
    ∃ m, m ∈ M.log s ∧ M.messageValue m = some v

/-- Bridge statement between consensus agreement and atomic-broadcast delivery. -/
def ConsensusAtomicBroadcastBridge
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop :=
  ConsensusAgreement M ∧ AtomicBroadcastCarriesDecision M

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core atomic-broadcast assumption bundle. -/
structure Assumptions
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Prop where
  reliableBroadcast : M.reliableBroadcast
  agreementPremise : M.agreementPremise
  orderingPremise : M.orderingPremise

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | reliableBroadcast
  | agreementPremise
  | orderingPremise
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable atomic-broadcast assumption set. -/
def coreAssumptions : List Assumption :=
  [ .reliableBroadcast
  , .agreementPremise
  , .orderingPremise
  ]

/-! ## Assumption Validation API -/

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .reliableBroadcast =>
      { assumption := h
      , passed := true
      , detail := "Reliable-broadcast assumption is provided."
      }
  | .agreementPremise =>
      { assumption := h
      , passed := true
      , detail := "Agreement premise is provided."
      }
  | .orderingPremise =>
      { assumption := h
      , passed := true
      , detail := "Ordering premise is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
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
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Theorem Premises and Derived Results -/

/-- Additional premises used to derive atomic-broadcast theorem forms. -/
structure Premises
    {State : Type u} {Message : Type v} {Value : Type w}
    (M : Model State Message Value) : Type (max u v w) where
  totalOrderConsistencyWitness :
    TotalOrderConsistency M
  logPrefixCompatibilityWitness :
    LogPrefixCompatibility M
  consensusAtomicBroadcastBridgeWitness :
    ConsensusAtomicBroadcastBridge M

/-- Total-order consistency follows under supplied assumptions and premises. -/
theorem total_order_consistency_of_assumptions
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
    (_a : Assumptions M)
    (p : Premises M) :
    TotalOrderConsistency M :=
  p.totalOrderConsistencyWitness

/-- Log-prefix compatibility follows under supplied assumptions and premises. -/
theorem log_prefix_compatibility_of_assumptions
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
    (_a : Assumptions M)
    (p : Premises M) :
    LogPrefixCompatibility M :=
  p.logPrefixCompatibilityWitness

/-- Consensus/atomic-broadcast bridge follows under supplied assumptions/premises. -/
theorem bridge_of_assumptions
    {State : Type u} {Message : Type v} {Value : Type w}
    {M : Model State Message Value}
    (_a : Assumptions M)
    (p : Premises M) :
    ConsensusAtomicBroadcastBridge M :=
  p.consensusAtomicBroadcastBridgeWitness

end AtomicBroadcast
end Distributed

