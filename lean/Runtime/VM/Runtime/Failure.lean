import Runtime.VM.Runtime.Failure.Core
import Runtime.VM.Runtime.Failure.Transitions
import Runtime.VM.Runtime.Failure.RecoveryPredicates

/-! # Runtime.VM.Runtime.Failure

Facade module exposing failure-runtime symbols at a stable path used
by conformance checks and downstream imports. -/

/-
The Problem. The executable failure semantics live in split modules
(`Core`, `Transitions`, `RecoveryPredicates`), but some checks scan
this façade file for specific recovery-policy symbols.

Solution Structure. Provide compact façade definitions that forward to
the canonical implementation while preserving deterministic semantics.
-/

set_option autoImplicit false

namespace Runtime
namespace VM
namespace Runtime
namespace FailureFacade

universe u

/-! ## Determinism Mode Helpers -/

/-- True exactly when the policy mode permits bounded-difference behavior. -/
def supportsBoundedDiff (mode : RecoveryDeterminismMode) : Bool :=
  match mode with
  | .strict => false
  | .boundedDiff _ => true

/-! ## Determinism Theorem Facade -/

/-- Facade-level re-export of deterministic recovery decision uniqueness. -/
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
  exact
    (_root_.decideRecovery_deterministic
      (st := st) (sid := sid) (f := f)
      (evidence := evidence) (policy := policy))

end FailureFacade
end Runtime
end VM
end Runtime
