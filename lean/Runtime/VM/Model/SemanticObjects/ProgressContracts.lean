import Runtime.VM.Model.SemanticObjects.Core
import Runtime.VM.Model.SemanticObjects.OutstandingEffects

set_option autoImplicit false

/-!
# Runtime.VM.Model.SemanticObjects.ProgressContracts

The Problem.
Owner-internal liveness cannot stay as prose. The protocol-machine needs
first-class progress-contract semantics that say what counts as progress, how
deferred effect completion contributes to progress, and which escalation paths
are admissible for blocked work.

Solution Structure.
This module defines explicit progress/escalation relations over
`ProgressContract`, ties contracts to `OperationInstance` and
`OutstandingEffect`, and provides a small executable step/measure model that
later proof modules can relate to the existing Lyapunov and scheduling-bound
surfaces.
-/

namespace Runtime.VM.Model

/-! ## Core State Predicates -/

def ProgressState.isTerminal (state : ProgressState) : Prop :=
  match state with
  | .succeeded | .failed | .cancelled | .timedOut | .handedOff => True
  | .pending | .blocked | .noProgress | .degraded => False

def ProgressState.expectedOperationPhase : ProgressState → OperationPhase
  | .pending => .pending
  | .blocked | .noProgress | .degraded => .blocked
  | .succeeded => .succeeded
  | .failed => .failed
  | .cancelled => .cancelled
  | .timedOut => .timedOut
  | .handedOff => .handedOff

def ProgressContract.isTerminal (contract : ProgressContract) : Prop :=
  ProgressState.isTerminal contract.state

def ProgressContract.hasBudgetDiscipline (contract : ProgressContract) : Prop :=
  contract.bounded = false ∨ contract.budgetTicks.isSome

def ProgressContract.tracksOperation
    (contract : ProgressContract)
    (operation : OperationInstance) : Prop :=
  contract.operationId = operation.operationId ∧
  contract.session = operation.session ∧
  operation.phase = contract.state.expectedOperationPhase

/-! ## Progress and Escalation -/

inductive ProgressEscalation : ProgressState → ProgressState → Prop where
  | pending_blocked : ProgressEscalation .pending .blocked
  | blocked_noProgress : ProgressEscalation .blocked .noProgress
  | noProgress_degraded : ProgressEscalation .noProgress .degraded
  | degraded_failed : ProgressEscalation .degraded .failed
  | degraded_cancelled : ProgressEscalation .degraded .cancelled
  | degraded_timedOut : ProgressEscalation .degraded .timedOut

def ProgressTransition.isEscalationFor
    (transition : ProgressTransition)
    (contract : ProgressContract) : Prop :=
  transition.operationId = contract.operationId ∧
  transition.session = contract.session ∧
  ProgressEscalation transition.fromState transition.toState

def ProgressTransition.isProductiveFor
    (transition : ProgressTransition)
    (contract : ProgressContract) : Prop :=
  transition.operationId = contract.operationId ∧
  transition.session = contract.session ∧
  (transition.toState = .succeeded ∨ transition.toState = .handedOff)

def OutstandingEffect.completesProgressFor
    (effect : OutstandingEffect)
    (contract : ProgressContract) : Prop :=
  effect.operationId = contract.operationId ∧
  effect.session = contract.session ∧
  effect.status = .succeeded ∧
  match contract.lastOrderingKey with
  | none => True
  | some orderingKey => orderingKey ≤ effect.orderingKey

def ProtocolMachineSemanticObjects.effectCompletionCountsAsProgress
    (objects : ProtocolMachineSemanticObjects)
    (contract : ProgressContract) : Prop :=
  ∃ effect ∈ objects.outstandingEffects,
    effect.completesProgressFor contract

def ProtocolMachineSemanticObjects.ownerInternalLivenessContract
    (objects : ProtocolMachineSemanticObjects)
    (contract : ProgressContract) : Prop :=
  contract.hasBudgetDiscipline ∧
  ∃ operation ∈ objects.operationInstances,
    contract.tracksOperation operation ∧
    (contract.isTerminal ∨
      objects.effectCompletionCountsAsProgress contract ∨
      ∃ transition ∈ objects.progressTransitions,
        transition.isProductiveFor contract ∨ transition.isEscalationFor contract)

/-! ## Executable Contract Step / Measure -/

def ProgressContract.progressMeasure : ProgressContract → Nat
  | { state := .pending, .. } => 4
  | { state := .blocked, .. } => 3
  | { state := .noProgress, .. } => 2
  | { state := .degraded, .. } => 1
  | { state := .succeeded, .. } => 0
  | { state := .failed, .. } => 0
  | { state := .cancelled, .. } => 0
  | { state := .timedOut, .. } => 0
  | { state := .handedOff, .. } => 0

abbrev ProgressContract.weightedMeasure : ProgressContract → Nat :=
  ProgressContract.progressMeasure

def ProgressContract.syntheticStep
    (contract : ProgressContract) : Option ProgressContract :=
  match contract.state with
  | .pending =>
      some { contract with state := .blocked }
  | .blocked =>
      some { contract with
        state := .noProgress
        , escalatedAtTick := contract.escalatedAtTick.orElse (fun _ => contract.lastProgressTick)
      }
  | .noProgress =>
      some { contract with
        state := .degraded
        , escalatedAtTick := contract.escalatedAtTick.orElse (fun _ => contract.lastProgressTick)
      }
  | .degraded =>
      some { contract with
        state := if contract.bounded then .timedOut else .failed
        , escalatedAtTick := contract.escalatedAtTick.orElse (fun _ => contract.lastProgressTick)
      }
  | .succeeded | .failed | .cancelled | .timedOut | .handedOff =>
      none

end Runtime.VM.Model
