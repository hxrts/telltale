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
  shards : State → List Chunk
  validShard : State → Chunk → Prop
  sampled : State → Chunk → Prop
  reconstructs : State → List Chunk → Prop
  withheld : State → Chunk → Prop

/-! ## Shard, Sampling, and Reconstruction Semantics -/

/-- All valid shards for a state are sample-visible. -/
def SamplingCoversValidShards
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s c, c ∈ M.shards s → M.validShard s c → M.sampled s c

/-- The adversary cannot withhold a valid shard from the sampling surface. -/
def WithholdingBound
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s c, c ∈ M.shards s → M.validShard s c → ¬ M.withheld s c

/-- A candidate chunk set is a valid reconstruction quorum. -/
def ReconstructionQuorum
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) (s : State) (chunks : List Chunk) : Prop :=
  M.k ≤ chunks.length ∧
    ∀ c, c ∈ chunks → c ∈ M.shards s ∧ M.validShard s c ∧ M.sampled s c

/-- Every state exposes enough sampled valid shards to attempt reconstruction. -/
def ReconstructionQuorumAvailable
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s, ∃ chunks, ReconstructionQuorum M s chunks

/-- Any valid quorum reconstructs the underlying data. -/
def ReconstructionSound
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s chunks, ReconstructionQuorum M s chunks → M.reconstructs s chunks

/-- Data availability property. -/
def DataAvailability
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  SamplingCoversValidShards M ∧ WithholdingBound M

/-- Data retrievability property. -/
def DataRetrievability
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Prop :=
  ∀ s, ∃ chunks, ReconstructionQuorum M s chunks ∧ M.reconstructs s chunks

/-! ## Assumption Atoms and Contracts -/

/-- Reusable core data-availability assumption bundle. -/
structure Assumptions
    {State : Type u} {Chunk : Type v}
    (M : Model State Chunk) : Type (max u v) where
  kOfNWellFormed : M.k ≤ M.n ∧ 0 < M.k
  samplingCoversValidShards : SamplingCoversValidShards M
  withholdingBound : WithholdingBound M
  reconstructionQuorumAvailable : ReconstructionQuorumAvailable M
  reconstructionSound : ReconstructionSound M

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | kOfNWellFormed
  | samplingCoversValidShards
  | withholdingBound
  | reconstructionQuorumAvailable
  | reconstructionSound
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
  , .samplingCoversValidShards
  , .withholdingBound
  , .reconstructionQuorumAvailable
  , .reconstructionSound
  ]

/-! ## Assumption Validation API -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .kOfNWellFormed =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "k-of-n model well-formedness is provided."
      }
  | .samplingCoversValidShards =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Sampling covers every valid shard."
      }
  | .withholdingBound =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Valid shards cannot be withheld from the sampling surface."
      }
  | .reconstructionQuorumAvailable =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Every state exposes a valid reconstruction quorum."
      }
  | .reconstructionSound =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Every valid quorum reconstructs the data."
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

/-! ## Derived Results -/

/-- Data availability follows from sampling coverage and withholding bounds. -/
theorem availability_of_assumptions
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (a : Assumptions M) :
    DataAvailability M :=
  ⟨a.samplingCoversValidShards, a.withholdingBound⟩

/-- Data retrievability follows from reconstruction quorum availability and soundness. -/
theorem retrievability_of_assumptions
    {State : Type u} {Chunk : Type v}
    {M : Model State Chunk}
    (a : Assumptions M) :
    DataRetrievability M := by
  intro s
  rcases a.reconstructionQuorumAvailable s with ⟨chunks, hQuorum⟩
  exact ⟨chunks, hQuorum, a.reconstructionSound s chunks hQuorum⟩

end DataAvailability
end Distributed
