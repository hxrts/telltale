set_option autoImplicit false

/-! # Distributed.Families.CAP

Reusable hypothesis bundles for CAP-style impossibility proofs.

This module provides:
- reusable model assumptions,
- protocol-level CAP target predicates,
- impossibility premises,
- a full impossibility theorem.
-/

/-
The Problem. This module needs a concise statement of its theorem-family boundary and reusable assumptions.
Solution Structure. Introduce the core model/contracts first, then derive canonical lemmas and API wrappers from those contracts.
-/

/-! ## Core Development -/

namespace Distributed
namespace CAP

universe u v

/-- Minimal model interface for CAP reasoning. -/
structure Model (State : Type u) (Party : Type v) where
  initial : State → Prop
  partitioned : State → Prop
  available : State → Prop
  stronglyConsistent : State → Prop
  /-- Asynchronous setting assumption. -/
  asynchronous : Prop
  /-- Partition tolerance assumption for the model. -/
  partitionTolerant : Prop

/-- Reusable core CAP assumption bundle. -/
structure Assumptions
    {State : Type u} {Party : Type v}
    (M : Model State Party) : Prop where
  asynchronous : M.asynchronous
  partitionTolerant : M.partitionTolerant

/-- Built-in CAP assumption labels for summary/validation APIs. -/
inductive Assumption where
  | asynchronous
  | partitionTolerant
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one CAP assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable CAP assumption set. -/
def coreAssumptions : List Assumption :=
  [ .asynchronous
  , .partitionTolerant
  ]

/-- Validate one CAP assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .asynchronous =>
      { assumption := h
      , passed := true
      , detail := "Asynchrony assumption is provided."
      }
  | .partitionTolerant =>
      { assumption := h
      , passed := true
      , detail := "Partition-tolerance assumption is provided."
      }

/-- Validate a list of CAP assumptions. -/
def validateAssumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of CAP assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for CAP assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Availability guarantee under partition runs. -/
def AvailabilityUnderPartition
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (PartitionRun : (Nat → State) → Prop) : Prop :=
  ∀ run, PartitionRun run → M.initial (run 0) →
    ∀ n, M.partitioned (run n) → M.available (run n)

/-- Strong-consistency guarantee under partition runs. -/
def StrongConsistencyUnderPartition
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (PartitionRun : (Nat → State) → Prop) : Prop :=
  ∀ run, PartitionRun run → M.initial (run 0) →
    ∀ n, M.partitioned (run n) → M.stronglyConsistent (run n)

/-- CAP guarantee target (consistency + availability under partition). -/
def CAPGuarantee
    {State : Type u} {Party : Type v}
    (M : Model State Party)
    (PartitionRun : (Nat → State) → Prop) : Prop :=
  AvailabilityUnderPartition M PartitionRun ∧
  StrongConsistencyUnderPartition M PartitionRun

/-- Premises that capture the core CAP contradiction shape. -/
structure ImpossibilityPremises
    {State : Type u} {Party : Type v}
    (M : Model State Party) : Type (max u v) where
  PartitionRun : (Nat → State) → Prop
  partitionedRunExists :
    ∃ run, PartitionRun run ∧ M.initial (run 0) ∧ ∀ n, M.partitioned (run n)
  /-- In a sustained partition, if every step remains available, some step must
      violate strong consistency. -/
  partitionForcesConsistencyFailure :
    ∀ run,
      PartitionRun run →
      M.initial (run 0) →
      (∀ n, M.partitioned (run n)) →
      (∀ n, M.available (run n)) →
      ∃ n, ¬ M.stronglyConsistent (run n)

/-- Full CAP impossibility theorem in reusable-hypothesis form. -/
theorem impossibility_of_assumptions
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (_a : Assumptions M)
    (p : ImpossibilityPremises M) :
    ¬ CAPGuarantee M p.PartitionRun := by
  intro hCAP
  rcases p.partitionedRunExists with ⟨run, hRun, hInit, hPart⟩
  have hAvailAll : ∀ n, M.available (run n) := by
    intro n
    exact hCAP.1 run hRun hInit n (hPart n)
  rcases p.partitionForcesConsistencyFailure run hRun hInit hPart hAvailAll with ⟨n, hNotCons⟩
  have hCons : M.stronglyConsistent (run n) :=
    hCAP.2 run hRun hInit n (hPart n)
  exact hNotCons hCons

/-- Corollary form: if availability under partition is given, then strong
consistency under partition is impossible (under the same premises). -/
theorem consistency_impossible_with_availability
    {State : Type u} {Party : Type v}
    {M : Model State Party}
    (a : Assumptions M)
    (p : ImpossibilityPremises M)
    (_hAvail : AvailabilityUnderPartition M p.PartitionRun) :
    ¬ StrongConsistencyUnderPartition M p.PartitionRun := by
  intro hCons
  exact impossibility_of_assumptions a p ⟨_hAvail, hCons⟩

end CAP
end Distributed


