import Runtime.ProgramLogic.GhostState
import Runtime.VM.Model.Config

/- 
The Problem. Finalization-sensitive steps (close and invoke) must be gated
by token ownership and deterministic-finalization configuration checks.

Solution Structure. Define lightweight predicates that can be threaded
through WP rules once the Iris proofs are available.
-/

set_option autoImplicit false
section

variable [Telltale.TelltaleIris]
variable [GhostMapSlot FinalizationMode]

/-! ## Finalization gating -/

def finalization_required (γ : GhostName) (ft : FinalizationToken) : iProp :=
  -- Gate finalizing actions on owning a finalization token.
  finalization_token_own γ ft

def finalization_config_ready {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (cfg : VMConfig ι γ π ε ν) : Prop :=
  -- Deterministic finalization preconditions hold.
  deterministic_finalization_ok cfg

/-! ## Finalization WP Rules -/

def wp_close_final {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (γn : GhostName) (ft : FinalizationToken) (cfg : VMConfig ι γ π ε ν) : iProp :=
  -- Close-final requires token ownership and deterministic finalization readiness.
  iProp.sep (finalization_required γn ft)
    (iProp.pure (finalization_config_ready cfg))

def wp_invoke_final {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (γn : GhostName) (ft : FinalizationToken) (cfg : VMConfig ι γ π ε ν) : iProp :=
  -- Invoke-final has the same gate surface as close-final in V2.
  iProp.sep (finalization_required γn ft)
    (iProp.pure (finalization_config_ready cfg))
