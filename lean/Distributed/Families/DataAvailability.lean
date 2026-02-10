set_option autoImplicit false

/-! # Distributed.Families.DataAvailability

Reusable data-availability assumptions and theorem forms:
- data availability,
- data retrievability.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace DataAvailability

universe u v

/-- Minimal model interface for DA/retrievability reasoning. -/
structure Model (State : Type u) (Chunk : Type v) where
  n : Nat
  k : Nat
  available : State → Prop
  retrievable : State → Prop
  samplingGuarantees : Prop
  withholdingBounded : Prop

/-- Data availability property. -/
def DataAvailability
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s, M.available s

/-- Data retrievability property. -/
def DataRetrievability
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s, M.retrievable s

/-- Reusable core data-availability assumption bundle. -/
structure Assumptions
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop where
  kOfNWellFormed : M.k ≤ M.n ∧ 0 < M.k
  samplingGuarantees : M.samplingGuarantees
  withholdingBounded : M.withholdingBounded

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | kOfNWellFormed
  | samplingGuarantees
  | withholdingBounded
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable DA assumption set. -/
def coreAssumptions : List Assumption :=
  [ .kOfNWellFormed
  , .samplingGuarantees
  , .withholdingBounded
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .kOfNWellFormed =>
      { assumption := h
      , passed := true
      , detail := "k-of-n model well-formedness is provided."
      }
  | .samplingGuarantees =>
      { assumption := h
      , passed := true
      , detail := "Sampling-guarantee assumption is provided."
      }
  | .withholdingBounded =>
      { assumption := h
      , passed := true
      , detail := "Withholding-adversary bound assumption is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
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
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Additional premises used to derive DA theorem forms. -/
structure Premises
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Type (max u v) where
  availabilityWitness :
    DataAvailability M
  retrievabilityWitness :
    DataRetrievability M

/-- Data availability follows under supplied assumptions and premises. -/
theorem availability_of_assumptions
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (_a : Assumptions M)
    (p : Premises M) :
    DataAvailability M :=
  p.availabilityWitness

/-- Data retrievability follows under supplied assumptions and premises. -/
theorem retrievability_of_assumptions
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (_a : Assumptions M)
    (p : Premises M) :
    DataRetrievability M :=
  p.retrievabilityWitness

end DataAvailability
end Distributed


set_option autoImplicit false

/-! # Distributed.Families.DataAvailability.API

High-level API for automatic DA/retrievability certification.
-/

namespace Distributed
namespace DataAvailability

universe u v

/-- Certified protocol package for DA/retrievability guarantees. -/
structure DAProtocol where
  State : Type u
  Chunk : Type v
  model : Model State Chunk
  assumptions : Assumptions model
  premises : Premises model
  availability :
    DataAvailability model :=
      availability_of_assumptions assumptions premises
  retrievability :
    DataRetrievability model :=
      retrievability_of_assumptions assumptions premises

/-- Extract data-availability theorem from a certified protocol bundle. -/
theorem availability_of_protocol (P : DAProtocol) :
    DataAvailability P.model :=
  P.availability

/-- Extract data-retrievability theorem from a certified protocol bundle. -/
theorem retrievability_of_protocol (P : DAProtocol) :
    DataRetrievability P.model :=
  P.retrievability

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : DAProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end DataAvailability
end Distributed
