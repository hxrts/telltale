import Runtime.ProtocolMachine.Model.SemanticObjects.ProgressContracts

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts

The Problem.
The progress-contract model needs theorem-facing consequences: owner-internal
liveness should be explicit, escalation semantics should be clear enough for
cross-target parity, and the new contracts should satisfy the same core
obligations expected by the existing Lyapunov, weighted-measure, and
scheduling-bound proof surfaces.

Solution Structure.
This module proves the core progress/escalation lemmas and packages explicit
compatibility predicates that mirror the obligations consumed by the broader
progress-proof stack.
-/

namespace Runtime.ProtocolMachine.Model

/-! ## Core Measure / Escalation Lemmas -/

theorem progressMeasure_zero_iff_terminal
    (contract : ProgressContract) :
    contract.progressMeasure = 0 ↔ contract.isTerminal := by
  cases contract
  case mk operationId session state lastOrderingKey bounded budgetTicks lastProgressTick escalatedAtTick reason =>
    cases state <;> simp [ProgressContract.progressMeasure,
    ProgressContract.isTerminal, ProgressState.isTerminal]

theorem progressMeasure_pos_of_nonterminal
    (contract : ProgressContract)
    (hNonTerminal : ¬ contract.isTerminal) :
    0 < contract.progressMeasure := by
  cases contract
  case mk operationId session state lastOrderingKey bounded budgetTicks lastProgressTick escalatedAtTick reason =>
    cases state <;>
      simp [ProgressContract.progressMeasure, ProgressContract.isTerminal,
        ProgressState.isTerminal] at hNonTerminal ⊢

theorem syntheticStep_nonincreasing
    (contract next : ProgressContract)
    (hStep : contract.syntheticStep = some next) :
    next.progressMeasure ≤ contract.progressMeasure := by
  cases contract with
  | mk operationId session state lastOrderingKey bounded budgetTicks lastProgressTick escalatedAtTick reason =>
      cases state with
      | pending =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | blocked =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | noProgress =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | degraded =>
          by_cases hBound : bounded
          · simp [ProgressContract.syntheticStep, hBound] at hStep
            subst next
            simp [ProgressContract.progressMeasure]
          · simp [ProgressContract.syntheticStep, hBound] at hStep
            subst next
            simp [ProgressContract.progressMeasure]
      | succeeded =>
          simp [ProgressContract.syntheticStep] at hStep
      | failed =>
          simp [ProgressContract.syntheticStep] at hStep
      | cancelled =>
          simp [ProgressContract.syntheticStep] at hStep
      | timedOut =>
          simp [ProgressContract.syntheticStep] at hStep
      | handedOff =>
          simp [ProgressContract.syntheticStep] at hStep

theorem syntheticStep_decreases_active_measure
    (contract next : ProgressContract)
    (hStep : contract.syntheticStep = some next) :
    next.progressMeasure < contract.progressMeasure := by
  cases contract with
  | mk operationId session state lastOrderingKey bounded budgetTicks lastProgressTick escalatedAtTick reason =>
      cases state with
      | pending =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | blocked =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | noProgress =>
          simp [ProgressContract.syntheticStep] at hStep
          subst next
          simp [ProgressContract.progressMeasure]
      | degraded =>
          by_cases hBound : bounded
          · simp [ProgressContract.syntheticStep, hBound] at hStep
            subst next
            simp [ProgressContract.progressMeasure]
          · simp [ProgressContract.syntheticStep, hBound] at hStep
            subst next
            simp [ProgressContract.progressMeasure]
      | succeeded =>
          simp [ProgressContract.syntheticStep] at hStep
      | failed =>
          simp [ProgressContract.syntheticStep] at hStep
      | cancelled =>
          simp [ProgressContract.syntheticStep] at hStep
      | timedOut =>
          simp [ProgressContract.syntheticStep] at hStep
      | handedOff =>
          simp [ProgressContract.syntheticStep] at hStep

theorem syntheticStep_progress
    (contract : ProgressContract)
    (hNonTerminal : ¬ contract.isTerminal) :
    ∃ next, contract.syntheticStep = some next := by
  cases contract
  case mk operationId session state lastOrderingKey bounded budgetTicks lastProgressTick escalatedAtTick reason =>
    cases state <;>
      simp [ProgressContract.syntheticStep, ProgressContract.isTerminal,
        ProgressState.isTerminal] at hNonTerminal ⊢

theorem effectCompletionCountsAsProgress_has_matching_effect
    {objects : ProtocolMachineSemanticObjects}
    {contract : ProgressContract}
    (hProgress : objects.effectCompletionCountsAsProgress contract) :
    ∃ effect ∈ objects.outstandingEffects,
      effect.operationId = contract.operationId ∧
      effect.session = contract.session ∧
      effect.status = .succeeded := by
  rcases hProgress with ⟨effect, hMem, hComplete⟩
  rcases hComplete with ⟨hOp, hSession, hStatus, _hKey⟩
  exact ⟨effect, hMem, hOp, hSession, hStatus⟩

theorem ownerInternalLivenessContract_explicit
    {objects : ProtocolMachineSemanticObjects}
    {contract : ProgressContract}
    (hLiveness : objects.ownerInternalLivenessContract contract) :
    contract.hasBudgetDiscipline ∧
    ∃ operation ∈ objects.operationInstances,
      contract.tracksOperation operation := by
  rcases hLiveness with ⟨hBudget, operation, hMem, hTracks, _rest⟩
  exact ⟨hBudget, operation, hMem, hTracks⟩

/-! ## Compatibility Predicates -/

def ProgressContract.lyapunovCompatible (contract : ProgressContract) : Prop :=
  (contract.progressMeasure = 0 ↔ contract.isTerminal) ∧
  (¬ contract.isTerminal → 0 < contract.progressMeasure) ∧
  (∀ next, contract.syntheticStep = some next → next.progressMeasure ≤ contract.progressMeasure) ∧
  (¬ contract.isTerminal → ∃ next, contract.syntheticStep = some next)

def ProgressContract.weightedMeasureCompatible (contract : ProgressContract) : Prop :=
  ProgressContract.weightedMeasure contract = contract.progressMeasure

def ProgressContract.schedulingBoundCompatible (contract : ProgressContract) : Prop :=
  ¬ contract.isTerminal →
    ∃ next, contract.syntheticStep = some next ∧ next.progressMeasure < contract.progressMeasure

theorem lyapunovCompatible_of_progressContract
    (contract : ProgressContract) :
    contract.lyapunovCompatible := by
  refine ⟨progressMeasure_zero_iff_terminal contract, ?_, ?_, ?_⟩
  · intro hNonTerminal
    exact progressMeasure_pos_of_nonterminal contract hNonTerminal
  · intro next hStep
    exact syntheticStep_nonincreasing contract next hStep
  · intro hNonTerminal
    exact syntheticStep_progress contract hNonTerminal

theorem weightedMeasureCompatible_of_progressContract
    (contract : ProgressContract) :
    contract.weightedMeasureCompatible := by
  simp [ProgressContract.weightedMeasureCompatible, ProgressContract.weightedMeasure]

theorem schedulingBoundCompatible_of_progressContract
    (contract : ProgressContract) :
    contract.schedulingBoundCompatible := by
  intro hNonTerminal
  rcases syntheticStep_progress contract hNonTerminal with ⟨next, hStep⟩
  exact ⟨next, hStep, syntheticStep_decreases_active_measure contract next hStep⟩

end Runtime.ProtocolMachine.Model
