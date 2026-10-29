import Runtime.Proofs.Search.Liveness

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.AStarOptimality

A*-style optimality of the published goal incumbent for the reduced canonical
machine.

Heuristic admissibility and consistency are defined concretely over a weighted
successor graph. Admissibility is derived from consistency plus `h goal = 0`.
Optimality of the first published goal incumbent is then proved from:

- the machine's expansion order (each step services exactly the min-priority
  batch, and the incumbent is the first serviced goal commit);
- g-score soundness for goal entries (their priority is the cost of a real
  source-to-goal path);
- the standard A* frontier invariant that, before publication, some frontier
  entry lies on an optimal path with an exact g-score.

The frontier invariant remains a premise: the reduced machine does not model
successor expansion, so it cannot be derived here. It is not equivalent to the
conclusion; the conclusion additionally needs min-priority service and
admissibility, which are proved.
-/

namespace Runtime
namespace Proofs
namespace Search

/-! ## Heuristics -/

/-- Weighted successor graph: each node lists `(successor, edgeCost)`. -/
abbrev WeightedGraph := Nat → List (Nat × Nat)

/-- `PathCost G n t c`: some path from `n` to `t` in `G` has total cost `c`. -/
inductive PathCost (G : WeightedGraph) : Nat → Nat → Nat → Prop
  | refl (n : Nat) : PathCost G n n 0
  | step {n m t w c : Nat} : (m, w) ∈ G n → PathCost G m t c → PathCost G n t (w + c)

/-- Admissibility: `h n` never exceeds the cost of any path from `n` to `goal`. -/
def HeuristicAdmissible (G : WeightedGraph) (h : Nat → Nat) (goal : Nat) : Prop :=
  ∀ n c, PathCost G n goal c → h n ≤ c

/-- Consistency: `h n ≤ c(n, n') + h n'` for every edge. -/
def HeuristicConsistent (G : WeightedGraph) (h : Nat → Nat) : Prop :=
  ∀ n m w, (m, w) ∈ G n → h n ≤ w + h m

/-- Under a consistent heuristic, `h` drops by at most the path cost. -/
theorem heuristic_le_pathCost_add_of_consistent
    {G : WeightedGraph} {h : Nat → Nat} (hCons : HeuristicConsistent G h)
    {n t c : Nat} (hPath : PathCost G n t c) : h n ≤ c + h t := by
  induction hPath with
  | refl n => simp
  | step hEdge _ ih =>
    have := hCons _ _ _ hEdge
    omega

/-- A consistent heuristic with `h goal = 0` is admissible. -/
theorem heuristic_admissible_of_consistent
    {G : WeightedGraph} {h : Nat → Nat} {goal : Nat}
    (hCons : HeuristicConsistent G h) (hGoal : h goal = 0) :
    HeuristicAdmissible G h goal := by
  intro n c hPath
  have := heuristic_le_pathCost_add_of_consistent hCons hPath
  omega

/-! ## Optimal publication -/

/-- Premise bundle for optimal publication. `optimalCost` is a lower bound on
every source-to-goal path; nothing assumes the published cost directly. -/
structure OptimalGoalPublicationPremises
    (goal : Nat)
    (trace : SearchMachineTrace)
    (start bound optimalCost : Nat) where
  publicationPremises : GoalPublicationPremises goal trace start bound
  machineTrace : CanonicalMachineTrace goal trace
  initialNoIncumbent : (trace 0).incumbent = none
  graph : WeightedGraph
  sourceNode : Nat
  heuristic : Nat → Nat
  heuristicConsistent : HeuristicConsistent graph heuristic
  heuristicGoalZero : heuristic goal = 0
  optimalCostIsLowerBound : ∀ c, PathCost graph sourceNode goal c → optimalCost ≤ c
  /-- g-score soundness: a goal entry's priority (`g + h goal = g`) is the cost
  of a real source-to-goal path. -/
  goalEntriesAreRealPaths :
    ∀ i entry, entry ∈ (trace i).frontier → entry.node = goal →
      PathCost graph sourceNode goal entry.priority
  /-- Standard A* frontier invariant: while unpublished, some frontier entry
  has priority `g + h` with `g` plus a remaining path cost within the optimum. -/
  optimalPathRepresented :
    ∀ i, (trace i).incumbent = none →
      (∃ entry ∈ (trace i).frontier, entry.node = goal) →
      ∃ rep ∈ (trace i).frontier, ∃ g c,
        rep.priority = g + heuristic rep.node ∧
        PathCost graph rep.node goal c ∧ g + c ≤ optimalCost

/-- A newly published incumbent is the commit of a min-priority goal entry. -/
theorem new_incumbent_is_min_goal_commit
    {goal : Nat} {current : SearchMachineState} {commit : NormalizedCommit}
    (hNone : current.incumbent = none)
    (hSome : (executableCanonicalStep goal current).incumbent = some commit) :
    ∃ entry, IsMinPriority current.frontier entry ∧ entry.node = goal ∧
      commit.gScore = entry.priority := by
  simp only [executableCanonicalStep, executableRefreshedIncumbent, hNone] at hSome
  have hMem := mem_of_head?_eq_some hSome
  simp only [executableGoalCommitCandidates, executableNormalizedCommits,
    canonicalNormalizedCommitTrace, List.mem_filter, List.mem_map] at hMem
  obtain ⟨⟨entry, hBatch, rfl⟩, hGoal⟩ := hMem
  exact ⟨entry, mem_canonicalBatch_iff_isMinPriority.mp hBatch, by simpa using hGoal, rfl⟩

/-- The first published goal incumbent has optimal cost. -/
theorem first_published_goal_cost_is_optimal
    {goal start bound optimalCost : Nat} {trace : SearchMachineTrace}
    (P : OptimalGoalPublicationPremises goal trace start bound optimalCost)
    {i : Nat} {commit : NormalizedCommit}
    (hNone : (trace i).incumbent = none)
    (hSome : (trace (i + 1)).incumbent = some commit) :
    commit.gScore = optimalCost := by
  rw [(P.machineTrace i).next_eq_executable] at hSome
  obtain ⟨e, hMin, hGoal, hScore⟩ := new_incumbent_is_min_goal_commit hNone hSome
  obtain ⟨r, hr, g, c, hPri, hPath, hSum⟩ := P.optimalPathRepresented i hNone ⟨e, hMin.1, hGoal⟩
  have hAdm := heuristic_admissible_of_consistent P.heuristicConsistent P.heuristicGoalZero
    _ _ hPath
  have hLe := hMin.2 r hr
  have hLower := P.optimalCostIsLowerBound _ (P.goalEntriesAreRealPaths i e hMin.1 hGoal)
  omega

/-- Every incumbent ever published along the trace has optimal cost. -/
theorem published_goal_incumbent_has_optimal_cost
    {goal start bound optimalCost : Nat} {trace : SearchMachineTrace}
    (P : OptimalGoalPublicationPremises goal trace start bound optimalCost) :
    ∀ i commit, (trace i).incumbent = some commit → commit.gScore = optimalCost := by
  intro i
  induction i with
  | zero => intro commit h; simp [P.initialNoIncumbent] at h
  | succ i ih =>
    intro commit hSome
    cases hPrev : (trace i).incumbent with
    | none => exact first_published_goal_cost_is_optimal P hPrev hSome
    | some prev =>
      rw [(P.machineTrace i).next_eq_executable] at hSome
      simp only [executableCanonicalStep, executableRefreshedIncumbent, hPrev,
        Option.some.injEq] at hSome
      exact hSome ▸ ih prev hPrev

/-- A*-style eventual optimal publication: under a consistent heuristic, the
goal incumbent is eventually published with optimal cost. -/
theorem eventual_optimal_goal_publication_under_admissible_consistent_heuristic
    {goal start bound optimalCost : Nat}
    {trace : SearchMachineTrace}
    (hPremises : OptimalGoalPublicationPremises goal trace start bound optimalCost) :
    ∃ j, j < bound ∧
      ∃ commit,
        (trace (start + j + 1)).incumbent = some commit ∧
        commit.node = goal ∧
        commit.gScore = optimalCost := by
  rcases goal_reachability_connects_to_incumbent_publication
      hPremises.publicationPremises with
    ⟨j, hj, commit, hIncumbent, hGoal⟩
  exact ⟨j, hj, commit, hIncumbent, hGoal,
    published_goal_incumbent_has_optimal_cost hPremises _ _ hIncumbent⟩

end Search
end Proofs
end Runtime
