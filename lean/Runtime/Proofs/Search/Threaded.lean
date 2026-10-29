import Runtime.Proofs.Search.Core

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Threaded

Reduced execution model for the threaded exact single-lane scheduler.

This mirrors `NativeParallelExecutor::generate` in
`rust/search/src/runtime/executor.rs`:

1. the frozen canonical batch is tagged with its `batch_index`;
2. the indexed batch is split into contiguous lanes of a fixed non-zero width
   (`par_chunks`);
3. every lane processes its own entries independently, and lanes may finish in
   any order (`LaneSchedule.completion` is an arbitrary permutation of the
   lanes);
4. lane results are merged deterministically by `batch_index`.

The model is strictly more permissive than rayon's order-preserving `collect`:
lane completion order is arbitrary and the merge alone restores determinism.
The refinement theorem `threadedMergedResults_eq_canonical` shows that the
merged result is exactly the canonical serial batch, so the threaded step
artifact coincides with the canonical step artifact.
-/

namespace Runtime
namespace Proofs
namespace Search

/-! ## Indexing -/

/-- Tag each element with its position, starting from `n`. Mirrors the
`batch_index` carried by every Rust `Proposal`. -/
def indexFrom {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: indexFrom (n + 1) xs

/-- Projecting away the index recovers the original list. -/
theorem indexFrom_map_snd {α : Type} (n : Nat) (l : List α) :
    (indexFrom n l).map Prod.snd = l := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [indexFrom, ih]

/-- Indexing commutes with mapping over the payload. -/
theorem indexFrom_map {α β : Type} (f : α → β) (n : Nat) (l : List α) :
    (indexFrom n l).map (fun p => (p.1, f p.2)) = indexFrom n (l.map f) := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [indexFrom, ih]

/-- Every index produced from `n` is at least `n`. -/
theorem le_fst_of_mem_indexFrom {α : Type} {n : Nat} {l : List α} {p : Nat × α}
    (h : p ∈ indexFrom n l) : n ≤ p.1 := by
  induction l generalizing n with
  | nil => simp [indexFrom] at h
  | cons x xs ih =>
    simp only [indexFrom, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (ih h)

/-- Indexed lists are sorted by index. -/
theorem indexFrom_pairwise {α : Type} (n : Nat) (l : List α) :
    (indexFrom n l).Pairwise (fun a b => a.1 ≤ b.1) := by
  induction l generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.Pairwise.cons (fun b hb => ?_) (ih (n + 1))
    exact Nat.le_of_succ_le (le_fst_of_mem_indexFrom hb)

/-- Indices are unique keys in an indexed list. -/
theorem indexFrom_fst_injective {α : Type} {n : Nat} {l : List α} {a b : Nat × α}
    (ha : a ∈ indexFrom n l) (hb : b ∈ indexFrom n l) (h : a.1 = b.1) : a = b := by
  induction l generalizing n with
  | nil => simp [indexFrom] at ha
  | cons x xs ih =>
    simp only [indexFrom, List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have := le_fst_of_mem_indexFrom hb; simp at h; omega
    · have := le_fst_of_mem_indexFrom ha; simp at h; omega
    · exact ih ha hb

/-! ## Lane partition -/

/-- Contiguous lane partition with lane width `width + 1` (always non-zero),
mirroring rayon `par_chunks` over a `NonZeroUsize` chunk size. -/
def laneChunks {α : Type} (width : Nat) (l : List α) : List (List α) :=
  if h : l = [] then [] else l.take (width + 1) :: laneChunks width (l.drop (width + 1))
termination_by l.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < l.length := List.length_pos_iff_ne_nil.mpr h
  omega

/-- Concatenating the lanes recovers the partitioned list. -/
theorem flatten_laneChunks {α : Type} (width : Nat) (l : List α) :
    (laneChunks width l).flatten = l := by
  rw [laneChunks]
  by_cases hl : l = []
  · simp [hl]
  · rw [dif_neg hl, List.flatten_cons, flatten_laneChunks width (l.drop (width + 1)),
      List.take_append_drop]
termination_by l.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < l.length := List.length_pos_iff_ne_nil.mpr hl
  omega

/-! ## Threaded step -/

/-- One lane task: a batch index paired with the frozen frontier entry. -/
abbrev LaneTask := Nat × FrontierEntry

/-- One lane result: batch index, serviced entry, and its normalized commit. -/
abbrev LaneResult := Nat × (FrontierEntry × NormalizedCommit)

/-- Normalized commit produced when one frontier entry is serviced. -/
def entryCommit (entry : FrontierEntry) : NormalizedCommit :=
  { node := entry.node, parent := none, gScore := entry.priority }

/-- The frozen canonical batch tagged with batch indices. -/
def indexedCanonicalBatch (frontier : List FrontierEntry) : List LaneTask :=
  indexFrom 0 (canonicalBatch frontier)

/-- One admissible threaded schedule: a lane width and an arbitrary lane
completion order. -/
structure LaneSchedule (frontier : List FrontierEntry) where
  width : Nat
  completion : List (List LaneTask)
  completionPerm : completion.Perm (laneChunks width (indexedCanonicalBatch frontier))

/-- The schedule in which lanes complete in submission order. -/
def LaneSchedule.inOrder (frontier : List FrontierEntry) (width : Nat) :
    LaneSchedule frontier :=
  ⟨width, laneChunks width (indexedCanonicalBatch frontier), List.Perm.refl _⟩

/-- Work performed independently inside one lane. -/
def runLane (lane : List LaneTask) : List LaneResult :=
  lane.map fun task => (task.1, (task.2, entryCommit task.2))

/-- Deterministic merge of lane results by batch index. -/
def mergeLaneResults (results : List LaneResult) : List LaneResult :=
  results.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- Merged lane results for one threaded step under one schedule. -/
def threadedMergedResults
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) : List LaneResult :=
  mergeLaneResults (schedule.completion.map runLane).flatten

/-- Post-step frontier of the threaded exact single-lane scheduler. -/
def frontierAfterThreadedExactSingleLaneStep
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) : List FrontierEntry :=
  frontier.filter fun entry =>
    entry ∉ (threadedMergedResults frontier schedule).map fun result => result.2.1

/-- Threaded exact single-lane step artifact, built from the merged lane
results. -/
def threadedExactSingleLaneStepArtifact
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) : StepArtifact :=
  { batchNodes := (threadedMergedResults frontier schedule).map fun r => r.2.1.node
  , normalizedCommits := (threadedMergedResults frontier schedule).map fun r => r.2.2
  , nextFrontier := frontierAfterThreadedExactSingleLaneStep frontier schedule
  }

/-! ## Merge correctness -/

/-- The canonical serial result list, indexed by batch position. -/
def canonicalIndexedResults (frontier : List FrontierEntry) : List LaneResult :=
  indexFrom 0 ((canonicalBatch frontier).map fun e => (e, entryCommit e))

/-- Whatever the lane completion order, the unmerged lane results are a
permutation of the canonical indexed results. -/
theorem lane_results_perm_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    (schedule.completion.map runLane).flatten.Perm (canonicalIndexedResults frontier) := by
  have hp : schedule.completion.flatten.Perm (indexedCanonicalBatch frontier) := by
    simpa [flatten_laneChunks] using schedule.completionPerm.flatten
  have hFlat : (schedule.completion.map runLane).flatten = runLane schedule.completion.flatten := by
    simp only [runLane, List.map_flatten]
    rfl
  rw [hFlat, canonicalIndexedResults, ← indexFrom_map]
  exact hp.map _

/-- The deterministic merge of threaded lane results is exactly the canonical
indexed result list. -/
theorem threadedMergedResults_eq_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    threadedMergedResults frontier schedule = canonicalIndexedResults frontier := by
  unfold threadedMergedResults mergeLaneResults
  have hPerm := (List.mergeSort_perm _ (fun a b : LaneResult => decide (a.1 ≤ b.1))).trans (lane_results_perm_canonical frontier schedule)
  have hSorted := List.pairwise_mergeSort (le := fun a b : LaneResult => decide (a.1 ≤ b.1))
    (fun a b c h₁ h₂ => by simp at *; omega) (fun a b => by simp; omega)
    (schedule.completion.map runLane).flatten
  refine List.Perm.eq_of_pairwise (le := fun a b : LaneResult => a.1 ≤ b.1)
    (fun a b ha hb h₁ h₂ => ?_) (hSorted.imp (by simp)) (indexFrom_pairwise _ _) hPerm
  exact indexFrom_fst_injective (hPerm.mem_iff.mp ha) hb (Nat.le_antisymm h₁ h₂)

/-- Any projection of the merged results agrees with the canonical batch. -/
theorem threadedMergedResults_map
    {β : Type} (g : FrontierEntry × NormalizedCommit → β)
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    (threadedMergedResults frontier schedule).map (fun r => g r.2) =
      (canonicalBatch frontier).map fun e => g (e, entryCommit e) := by
  rw [threadedMergedResults_eq_canonical, canonicalIndexedResults,
    show (fun r : LaneResult => g r.2) = g ∘ Prod.snd from rfl, ← List.map_map,
    indexFrom_map_snd, List.map_map]
  rfl

/-- The threaded step artifact equals the canonical serial step artifact for
every lane width and every lane completion order. -/
theorem threaded_step_artifact_eq_canonical
    (frontier : List FrontierEntry) (schedule : LaneSchedule frontier) :
    threadedExactSingleLaneStepArtifact frontier schedule = canonicalStepArtifact frontier := by
  have hServiced := threadedMergedResults_map (fun p => p.1) frontier schedule
  have hNodes := threadedMergedResults_map (fun p => p.1.node) frontier schedule
  have hCommits := threadedMergedResults_map (fun p => p.2) frontier schedule
  simp only [List.map_id'] at hServiced
  simp only [threadedExactSingleLaneStepArtifact, frontierAfterThreadedExactSingleLaneStep,
    canonicalStepArtifact, frontierAfterCanonicalStep, canonicalNormalizedCommitTrace,
    hServiced, hNodes, hCommits]
  rfl

end Search
end Proofs
end Runtime
