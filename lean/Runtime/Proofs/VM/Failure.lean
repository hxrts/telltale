import Runtime.VM.Runtime.Failure.Core
import Runtime.Proofs.VM.FailurePredicates

set_option autoImplicit false

/-! # Runtime.Proofs.VM.Failure

Proof-only lemmas for deterministic recovery and retry bounds.
-/

universe u

/-- Retry delay is bounded by the configured max-retry envelope. -/
theorem retryBackoffDelay_bounded
    (policy : RecoveryPolicy)
    {attempt : Nat}
    (hAttempt : retryAllowed policy attempt) :
    retryBackoffDelay policy attempt ≤
      policy.baseBackoffTicks + policy.maxRetries * policy.backoffStepTicks := by
  unfold retryBackoffDelay retryAllowed at *
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hAttempt) _

/-- `decideRecovery` is total: every input yields a concrete recovery action. -/
theorem decideRecovery_total
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) (f : Failure ι)
    (evidence : RecoveryEvidence := {})
    (policy : RecoveryPolicy := defaultRecoveryPolicy) :
    ∃ act, decideRecovery st sid f evidence policy = act := by
  exact ⟨decideRecovery st sid f evidence policy, rfl⟩

/-- `decideRecovery` is deterministic: equal inputs imply equal chosen actions. -/
theorem decideRecovery_deterministic
    {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) (f : Failure ι)
    (evidence : RecoveryEvidence := {})
    (policy : RecoveryPolicy := defaultRecoveryPolicy) :
    ∀ a₁ a₂,
      decideRecovery st sid f evidence policy = a₁ →
      decideRecovery st sid f evidence policy = a₂ →
      a₁ = a₂ := by
  intro a₁ a₂ h₁ h₂
  simpa [h₁] using h₂
