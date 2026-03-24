import Runtime.ProtocolMachine.Model.Effects
import Runtime.ProtocolMachine.Model.SemanticObjects.Core

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects

The Problem.
Deferred effects need an explicit Lean-level lifecycle model for issuance,
blocking, completion, timeout, cancellation, invalidation, and retry. Without
that model, late-result rejection and admissibility remain prose-only.

Solution Structure.
This module defines the executable lifecycle vocabulary for `OutstandingEffect`
values, along with admissibility and late-result rejection predicates that the
proof layer can reason about directly.
-/

namespace Runtime.ProtocolMachine.Model

/-! ## Lifecycle Events -/

inductive OutstandingEffectEvent where
  | issued
  | blocked (reason : Option String := none)
  | completed (tick : Nat) (outcome : EffectOutcomeStatus)
  | timedOut (tick : Nat) (reason : Option String := none)
  | cancelled (tick : Nat) (reason : Option String := none)
  | invalidated (tick : Nat) (reason : Option String := none)
  | retried (orderingKey : Nat)
  deriving Repr, DecidableEq

def EffectOutcomeStatus.toOutstandingEffectStatus : EffectOutcomeStatus → OutstandingEffectStatus
  | .success => .succeeded
  | .blocked => .blocked
  | .failure _ _ => .failed

/-! ## Admissibility -/

def OutstandingEffect.isLive (effect : OutstandingEffect) : Prop :=
  effect.status = .pending ∨ effect.status = .blocked

def OutstandingEffect.isTerminal (effect : OutstandingEffect) : Prop :=
  ¬ effect.isLive

def OutstandingEffect.ownerMatches (effect : OutstandingEffect) (ownerId : Option String) : Prop :=
  effect.ownerId = ownerId

def OutstandingEffect.withinBudgetAt (effect : OutstandingEffect) (tick : Nat) : Prop :=
  match effect.budgetTicks with
  | none => True
  | some budget => effect.orderingKey + budget ≥ tick

def OutstandingEffect.admissibleForCommit
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) : Prop :=
  effect.isLive ∧ effect.ownerMatches ownerId ∧ effect.withinBudgetAt tick

def OutstandingEffect.rejectsCommit
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) : Prop :=
  ¬ effect.admissibleForCommit ownerId tick

def OutstandingEffect.resultIsLate
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) : Prop :=
  effect.completedAtTick.isSome ∧ effect.rejectsCommit ownerId tick

/-! ## Lifecycle Realization -/

def OutstandingEffect.applyEvent
    (effect : OutstandingEffect) (event : OutstandingEffectEvent) : OutstandingEffect :=
  match event with
  | .issued =>
      { effect with
        status := .pending
        completedAtTick := none
      }
  | .blocked _ =>
      { effect with
        status := .blocked
      }
  | .completed tick outcome =>
      { effect with
        status := outcome.toOutstandingEffectStatus
        completedAtTick := some tick
      }
  | .timedOut tick reason =>
      { effect with
        status := .invalidated
        completedAtTick := some tick
        outputs := reason.getD "timed_out"
      }
  | .cancelled tick reason =>
      { effect with
        status := .cancelled
        completedAtTick := some tick
        outputs := reason.getD "cancelled"
      }
  | .invalidated tick reason =>
      { effect with
        status := .invalidated
        completedAtTick := some tick
        outputs := reason.getD "invalidated"
      }
  | .retried orderingKey =>
      { effect with
        status := .pending
        orderingKey := orderingKey
        completedAtTick := none
      }

def OutstandingEffect.issuedFromRequest
    (request : EffectRequest)
    (ownerId : Option String)
    (handlerIdentity : String)
    (effectKind retryPolicy invalidationToken : String) : OutstandingEffect :=
  { effectId := request.effectId.getD 0
    operationId := request.operationId.getD ""
    session := request.session
    ownerId := ownerId
    effectInterface := some request.metadata.interfaceName
    effectOperation := some request.metadata.operationName
    effectKind := effectKind
    handlerIdentity := handlerIdentity
    status := .pending
    orderingKey := request.tick
    budgetTicks :=
      match request.metadata.timeoutPolicy with
      | .required budgetTicks => budgetTicks
      | .none | .inheritOperationBudget => none
    retryPolicy := retryPolicy
    invalidationToken := invalidationToken
    completedAtTick := none
    inputs := reprStr request.body
    outputs := ""
  }

def OutstandingEffect.matchesExchangeRecord
    (effect : OutstandingEffect) (exchange : EffectExchangeRecord) : Prop :=
  effect.effectId = exchange.effectId ∧
  effect.handlerIdentity = exchange.handlerIdentity ∧
  effect.orderingKey = exchange.orderingKey

end Runtime.ProtocolMachine.Model
