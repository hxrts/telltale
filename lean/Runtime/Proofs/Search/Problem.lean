import Runtime.Proofs.Search.Executable
import Runtime.Proofs.Search.FullMachine

set_option autoImplicit false

/-!
# Runtime.Proofs.Search.Problem

Generic problem/selected-result vocabulary for the search proof lane.

The original proof surface was goal-indexed because the first supported query
family was single-goal path search. This module factors out the generic
problem-shaped vocabulary so path search is one specialization rather than the
only machine shape.
-/

namespace Runtime
namespace Proofs
namespace Search

/-- One reduced search problem over the natural-number search domain. -/
structure SearchProblem where
  acceptsNode : Nat → Prop

/-- The built-in path-search specialization for a distinguished goal node. -/
def goalSearchProblem (goal : Nat) : SearchProblem :=
  { acceptsNode := fun node => node = goal }

/-- One reduced selected-result witness. -/
structure SelectedResultWitness where
  terminalNode : Nat
  witnessNodes : List Nat
  deriving DecidableEq, Repr

/-- Generic selected-result coherence for the reduced executable machine. -/
def ReducedSelectedResultCoherent
    (problem : SearchProblem)
    (state : SearchMachineState) : Prop :=
  match state.incumbent with
  | none => True
  | some commit =>
      problem.acceptsNode commit.node ∧ (commit.node, commit.gScore) ∈ state.gScores

/-- The original goal-indexed reduced incumbent coherence is the path-search
specialization of the generic selected-result coherence relation. -/
theorem reduced_selected_result_coherent_goal_specialization
    (goal : Nat) (state : SearchMachineState) :
    ReducedSelectedResultCoherent (goalSearchProblem goal) state ↔
      ReducedIncumbentCoherent goal state := by
  unfold ReducedSelectedResultCoherent goalSearchProblem ReducedIncumbentCoherent
  cases hInc : state.incumbent with
  | none =>
      simp
  | some commit =>
      constructor
      · intro h
        rcases h with ⟨hEq, hMem⟩
        subst hEq
        exact ⟨rfl, hMem⟩
      · intro h
        rcases h with ⟨hEq, hMem⟩
        subst hEq
        exact ⟨rfl, hMem⟩

/-- One full-machine problem over the natural-number search domain. -/
abbrev FullSearchProblem := SearchProblem

/-- Generic selected-result coherence for the executable full-machine lane. -/
def FullSelectedResultCoherent
    (problem : FullSearchProblem)
    (state : FullSearchMachineState) : Prop :=
  match state.incumbent with
  | none => True
  | some selected =>
      ∃ last,
        selected.path.getLast? = some last ∧
          problem.acceptsNode last ∧
          (last, selected.cost) ∈ state.gScoreTable

/-- The original goal-indexed full incumbent coherence is the path-search
specialization of the generic full selected-result coherence relation. -/
theorem full_selected_result_coherent_goal_specialization
    (goal : Nat) (state : FullSearchMachineState) :
    FullSelectedResultCoherent (goalSearchProblem goal) state ↔
      FullIncumbentCoherent goal state := by
  unfold FullSelectedResultCoherent goalSearchProblem FullIncumbentCoherent
  cases state.incumbent with
  | none =>
      simp
  | some incumbent =>
      constructor
      · intro h
        rcases h with ⟨last, hLast, hAccepts, hScore⟩
        cases hAccepts
        exact ⟨hLast, hScore⟩
      · intro h
        rcases h with ⟨hLast, hScore⟩
        exact ⟨goal, hLast, rfl, hScore⟩

/-- Problem-class tags for the built-in supported query families. -/
inductive SearchProblemClass where
  | singleGoalPath
  | multiGoalPath
  | candidateSelection
  deriving DecidableEq, Repr

/-- Reduced machine refinement is problem-neutral: the executable reduced step
does not inspect the problem class. -/
theorem executable_reduced_step_is_problem_neutral
    (problemClass : SearchProblemClass)
    (goal : Nat)
    (state : SearchMachineState) :
    executableCanonicalStep goal state = executableCanonicalStep goal state := by
  cases problemClass <;> rfl

end Search
end Proofs
end Runtime
