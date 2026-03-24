import Runtime.Proofs.EffectBisim.Core
import Runtime.ProtocolMachine.Model.SemanticObjects.OutstandingEffects

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.SemanticObjects.OutstandingEffects

The Problem.
The outstanding-effect lifecycle rules need theorem-facing consequences: when an
effect may still commit, when a late result must be rejected, and how rejected
late results remain silent at the observer boundary.

Solution Structure.
This module proves direct admissibility and invalidation lemmas over the
implementation-level lifecycle model, then packages a small observation/step
surface that plugs into `Runtime.Proofs.EffectBisim`.
-/

namespace Runtime.ProtocolMachine.Model

open Runtime.Proofs.EffectBisim

/-! ## Core Admissibility Lemmas -/

theorem cancelled_not_admissible
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    ¬ (effect.applyEvent (.cancelled tick)).admissibleForCommit ownerId tick := by
  intro h
  rcases h with ⟨hLive, _, _⟩
  simp [OutstandingEffect.isLive, OutstandingEffect.applyEvent] at hLive

theorem invalidated_not_admissible
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    ¬ (effect.applyEvent (.invalidated tick)).admissibleForCommit ownerId tick := by
  intro h
  rcases h with ⟨hLive, _, _⟩
  simp [OutstandingEffect.isLive, OutstandingEffect.applyEvent] at hLive

theorem timedOut_not_admissible
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    ¬ (effect.applyEvent (.timedOut tick)).admissibleForCommit ownerId tick := by
  intro h
  rcases h with ⟨hLive, _, _⟩
  simp [OutstandingEffect.isLive, OutstandingEffect.applyEvent] at hLive

theorem owner_mismatch_rejects_commit
    (effect : OutstandingEffect)
    {ownerId₁ ownerId₂ : Option String}
    (hOwner : effect.ownerId = ownerId₁)
    (hMismatch : ownerId₁ ≠ ownerId₂)
    (tick : Nat) :
    effect.rejectsCommit ownerId₂ tick := by
  intro hCommit
  rcases hCommit with ⟨_, hOwnerMatch, _⟩
  have hEq : ownerId₁ = ownerId₂ := by
    simpa [OutstandingEffect.ownerMatches] using hOwner.symm.trans hOwnerMatch
  exact hMismatch hEq

theorem budget_expiry_rejects_commit
    (effect : OutstandingEffect)
    {budget : Nat}
    (hBudget : effect.budgetTicks = some budget)
    {tick : Nat}
    (hExpired : effect.orderingKey + budget < tick) :
    effect.rejectsCommit effect.ownerId tick := by
  intro hCommit
  rcases hCommit with ⟨_, _, hWithin⟩
  have hGe : effect.orderingKey + budget ≥ tick := by
    simpa [OutstandingEffect.withinBudgetAt, hBudget] using hWithin
  exact (Nat.not_lt_of_ge hGe) hExpired

theorem late_result_rejected_after_cancel
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    (effect.applyEvent (.cancelled tick)).resultIsLate ownerId tick := by
  refine ⟨by simp [OutstandingEffect.applyEvent], ?_⟩
  exact cancelled_not_admissible effect ownerId tick

theorem late_result_rejected_after_invalidate
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    (effect.applyEvent (.invalidated tick)).resultIsLate ownerId tick := by
  refine ⟨by simp [OutstandingEffect.applyEvent], ?_⟩
  exact invalidated_not_admissible effect ownerId tick

theorem late_result_rejected_after_timeout
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat) :
    (effect.applyEvent (.timedOut tick)).resultIsLate ownerId tick := by
  refine ⟨by simp [OutstandingEffect.applyEvent], ?_⟩
  exact timedOut_not_admissible effect ownerId tick

/-! ## Observer / Effect-Bisim Bridge -/

def outstandingEffectObs :
    EffectObs OutstandingEffect (OutstandingEffectStatus × Option Nat × Option String) where
  observe effect := (effect.status, effect.completedAtTick, effect.ownerId)

inductive OutstandingEffectStep : OutstandingEffect → OutstandingEffect → Prop where
  | apply (effect : OutstandingEffect) (event : OutstandingEffectEvent) :
      OutstandingEffectStep effect (effect.applyEvent event)
  | rejectLateResult (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat)
      (hLate : effect.resultIsLate ownerId tick) :
      OutstandingEffectStep effect effect

theorem rejectLateResult_observationalEq
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat)
    (hLate : effect.resultIsLate ownerId tick) :
    ObservationalEq outstandingEffectObs effect effect := by
  rfl

theorem rejectLateResult_effect_bisim
    (effect : OutstandingEffect) (ownerId : Option String) (tick : Nat)
    (hLate : effect.resultIsLate ownerId tick) :
    EffectBisim outstandingEffectObs OutstandingEffectStep effect effect := by
  exact effect_bisim_refl outstandingEffectObs OutstandingEffectStep effect

end Runtime.ProtocolMachine.Model
