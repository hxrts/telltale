import Mathlib.Data.List.Basic

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Core

Search-specific fairness vocabulary.

This module defines the dynamic-work fairness surface for search scheduling.
Unlike the fixed-role `KFair` machinery used elsewhere in the runtime proofs,
search fairness is about frontier entries whose enabled set changes after each
step.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- Reduced frontier entry model for scheduler fairness reasoning. -/
structure FrontierEntry where
  node : Nat
  priority : Nat
  deriving DecidableEq, Repr

/-- Search trace specialized to frontier snapshots. -/
abbrev FrontierTrace := Nat → List FrontierEntry

/-- One reduced normalized commit record. -/
structure NormalizedCommit where
  node : Nat
  parent : Option Nat
  gScore : Nat
  deriving DecidableEq, Repr

/-- An entry is min-priority in a frontier when it is present and no frontier
entry has a lower priority. -/
def IsMinPriority (frontier : List FrontierEntry) (entry : FrontierEntry) : Prop :=
  entry ∈ frontier ∧ ∀ other, other ∈ frontier → entry.priority ≤ other.priority

/-- The canonical serial search scheduler services every entry in the current
legal min-key batch. -/
def canonicalBatch (frontier : List FrontierEntry) : List FrontierEntry :=
  frontier.filter (fun entry => ∀ other, other ∈ frontier → entry.priority ≤ other.priority)

/-- One canonical serial step removes the current min-key batch from the
frontier. -/
def frontierAfterCanonicalStep (frontier : List FrontierEntry) : List FrontierEntry :=
  frontier.filter (fun entry => entry ∉ canonicalBatch frontier)

/-- A frontier trace follows canonical serial search stepping. -/
def CanonicalSerialTrace (trace : FrontierTrace) : Prop :=
  ∀ i, trace (i + 1) = frontierAfterCanonicalStep (trace i)

/-- Search-specific bounded fairness contract for one frozen frontier: every
currently enabled min-priority entry is serviced within the next canonical
serial step. -/
def OneStepFair (frontier : List FrontierEntry) : Prop :=
  ∀ ⦃entry : FrontierEntry⦄,
    IsMinPriority frontier entry →
    entry ∉ frontierAfterCanonicalStep frontier

/-- Search-visible notion of eventual service within a finite bound. -/
def EventuallyServicedWithin
    (trace : FrontierTrace) (start bound : Nat) (entry : FrontierEntry) : Prop :=
  ∃ j, j < bound ∧ entry ∉ trace (start + j + 1)

/-- Entry remains min-priority from one start frontier until it is serviced.
This is stronger than needed for canonical serial search, but it is the right
shape for future dynamic-fairness extensions. -/
def ContinuouslyMinPriorityUntilService
    (trace : FrontierTrace) (start horizon : Nat) (entry : FrontierEntry) : Prop :=
  ∀ j, j < horizon → entry ∈ trace (start + j) → IsMinPriority (trace (start + j)) entry

/-- Entry stays present across one horizon. -/
def ContinuouslyEligible
    (trace : FrontierTrace) (start horizon : Nat) (entry : FrontierEntry) : Prop :=
  ∀ j, j < horizon → entry ∈ trace (start + j)

/-- No strictly better entry appears across one horizon. -/
def NoStrictlyBetterEntryAppears
    (trace : FrontierTrace) (start horizon : Nat) (entry : FrontierEntry) : Prop :=
  ∀ j, j < horizon →
    ∀ other, other ∈ trace (start + j) → ¬ other.priority < entry.priority

/-- Reduced normalized commit trace for one canonical serial step. -/
def canonicalNormalizedCommitTrace
    (frontier : List FrontierEntry) : List NormalizedCommit :=
  (canonicalBatch frontier).map fun entry =>
    { node := entry.node, parent := none, gScore := entry.priority }

/-- Reduced step artifact used by search refinement proofs. -/
structure StepArtifact where
  batchNodes : List Nat
  normalizedCommits : List NormalizedCommit
  nextFrontier : List FrontierEntry
  deriving DecidableEq, Repr

/-- Reduced authoritative state slice for one search step. This is the
proof-claimed state boundary for search fairness refinement: frontier residency,
committed parent/score updates, and the reduced epoch/phase/incumbent view. -/
structure StateSlice where
  frontier : List FrontierEntry
  openNodes : List Nat
  closedNodes : List Nat
  parentMap : List (Nat × Option Nat)
  gScores : List (Nat × Nat)
  incumbent : Option NormalizedCommit
  epoch : Nat
  phase : Nat
  deriving DecidableEq, Repr

/-- Reduced observable slice derived from one search step. This mirrors the
public observation classes carried by the Rust search runtime at the reduced
proof boundary. -/
structure ObservationSlice where
  incumbentCost : Option Nat
  incumbentNode : Option Nat
  normalizedCommits : List NormalizedCommit
  productiveSteps : Nat
  totalSchedulerSteps : Nat
  deriving DecidableEq, Repr

/-- Reduced exported state artifact schema. This mirrors the public
`SearchStateArtifact` boundary at the theorem-facing level. -/
structure StateArtifactSchema where
  openNodes : List (Nat × Nat)
  closedNodes : List Nat
  gScores : List (Nat × Nat)
  parentMap : List (Nat × Nat)
  incumbentCost : Option Nat
  incumbentNodePath : Option (List Nat)
  epoch : Nat
  phase : Nat
  deriving DecidableEq, Repr

/-- Reduced certified window entry exported by one run-scoped batched-exact
certificate trace. -/
structure CertifiedWindowTraceEntry where
  epoch : Nat
  phase : Nat
  normalizationMode : String
  serviceBoundSteps : Nat
  batchNodes : List Nat
  normalizedCommits : List NormalizedCommit
  deriving DecidableEq, Repr

/-- Reduced run-scoped certified window trace. -/
abbrev CertifiedWindowTrace := List CertifiedWindowTraceEntry

/-- Reduced canonical serial step artifact. -/
def canonicalStepArtifact (frontier : List FrontierEntry) : StepArtifact :=
  { batchNodes := (canonicalBatch frontier).map FrontierEntry.node
  , normalizedCommits := canonicalNormalizedCommitTrace frontier
  , nextFrontier := frontierAfterCanonicalStep frontier
  }

/-- Reduced one-step model for the threaded exact single-lane scheduler. The
runtime may parallelize successor enumeration, but the frozen legal batch and
post-normalization commit are the same as canonical serial search. -/
def frontierAfterThreadedExactSingleLaneStep
    (frontier : List FrontierEntry) : List FrontierEntry :=
  frontierAfterCanonicalStep frontier

/-- Reduced threaded exact single-lane step artifact. -/
def threadedExactSingleLaneStepArtifact (frontier : List FrontierEntry) : StepArtifact :=
  canonicalStepArtifact frontier

/-- Reduced authoritative state slice derived from one step artifact. -/
def stateSliceOfStepArtifact (artifact : StepArtifact) : StateSlice :=
  { frontier := artifact.nextFrontier
  , openNodes := artifact.nextFrontier.map FrontierEntry.node
  , closedNodes := artifact.batchNodes
  , parentMap := artifact.normalizedCommits.map fun commit => (commit.node, commit.parent)
  , gScores := artifact.normalizedCommits.map fun commit => (commit.node, commit.gScore)
  , incumbent := artifact.normalizedCommits.head?
  , epoch := 0
  , phase := 0
  }

/-- Reduced observable slice derived from one step artifact. -/
def observationSliceOfStepArtifact (artifact : StepArtifact) : ObservationSlice :=
  { incumbentCost := artifact.normalizedCommits.head?.map NormalizedCommit.gScore
  , incumbentNode := artifact.normalizedCommits.head?.map NormalizedCommit.node
  , normalizedCommits := artifact.normalizedCommits
  , productiveSteps := if artifact.normalizedCommits.isEmpty then 0 else 1
  , totalSchedulerSteps := 1
  }

/-- Exported state artifact schema derived from one reduced state slice. -/
def stateArtifactOfStateSlice (slice : StateSlice) : StateArtifactSchema :=
  { openNodes := slice.gScores.filter fun entry => entry.1 ∈ slice.openNodes
  , closedNodes := slice.closedNodes
  , gScores := slice.gScores
  , parentMap := slice.parentMap.filterMap fun
      | (node, some parent) => some (node, parent)
      | (_, none) => none
  , incumbentCost := slice.incumbent.map NormalizedCommit.gScore
  , incumbentNodePath := slice.incumbent.map fun commit => [commit.node]
  , epoch := slice.epoch
  , phase := slice.phase
  }

/-- Certified service set for one batched exact window. -/
structure BatchedExactWindowCertificate (frontier : List FrontierEntry) where
  servicedEntries : List FrontierEntry
  normalizedCommits : List NormalizedCommit
  normalizationMode : String
  serviceBoundSteps : Nat
  coversCurrentMinKeyBatch :
    ∀ ⦃entry : FrontierEntry⦄,
      entry ∈ canonicalBatch frontier →
      entry ∈ servicedEntries
  commitTraceCoversCurrentMinKeyBatch :
    ∀ ⦃entry : FrontierEntry⦄,
      entry ∈ canonicalBatch frontier →
      ∃ commit, commit ∈ normalizedCommits ∧ commit.node = entry.node

/-- Post-window frontier under one certified batched exact service window. -/
def frontierAfterCertifiedBatchWindow
    (frontier : List FrontierEntry)
    (certificate : BatchedExactWindowCertificate frontier) : List FrontierEntry :=
  frontier.filter (fun entry => entry ∉ certificate.servicedEntries)

/-- Reduced certified batched exact window artifact. -/
def certifiedBatchWindowArtifact
    (frontier : List FrontierEntry)
    (certificate : BatchedExactWindowCertificate frontier) : StepArtifact :=
  { batchNodes := certificate.servicedEntries.map FrontierEntry.node
  , normalizedCommits := certificate.normalizedCommits
  , nextFrontier := frontierAfterCertifiedBatchWindow frontier certificate
  }

/-- Exported certified window trace entry derived from one batched-exact
certificate over one frontier. -/
def certifiedWindowTraceEntryOfCertificate
    (frontier : List FrontierEntry)
    (certificate : BatchedExactWindowCertificate frontier) : CertifiedWindowTraceEntry :=
  { epoch := 0
  , phase := 0
  , normalizationMode := certificate.normalizationMode
  , serviceBoundSteps := certificate.serviceBoundSteps
  , batchNodes := certificate.servicedEntries.map FrontierEntry.node
  , normalizedCommits := certificate.normalizedCommits
  }

/-- Entry becomes min-priority within one bounded preemption window. -/
def BoundedPreemptionWindow
    (trace : FrontierTrace) (start bound : Nat) (entry : FrontierEntry) : Prop :=
  ∃ j, j < bound ∧ IsMinPriority (trace (start + j)) entry

/-- Structural validity contract for one exported certified-window trace. -/
def CertifiedWindowTraceValid
    (trace : FrontierTrace) (start bound : Nat)
    (entries : ∀ j : Fin bound, CertifiedWindowTraceEntry) : Prop :=
  ∀ j : Fin bound,
    (entries j).serviceBoundSteps = 1 ∧
      (entries j).batchNodes =
        (canonicalBatch (trace (start + j.1))).map FrontierEntry.node

end Search
end Proofs
end Runtime
