import Runtime.ProgramLogic.GhostState
import Runtime.VM.Config

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
  -- Placeholder: deterministic finalization preconditions hold.
  deterministic_finalization_ok cfg

/-! ## WP placeholders -/

def wp_close_final : iProp :=
  -- Placeholder: close requires finalization token + config readiness.
  iProp.emp

def wp_invoke_final : iProp :=
  -- Placeholder: finalizing invoke requires finalization token + config readiness.
  iProp.emp
