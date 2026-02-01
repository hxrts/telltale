import Runtime.VM.Config
import Runtime.Compat.RA

/- 
The Problem. The runtime needs a lightweight credit resource for metering
instruction execution and threading costs through WP rules.

Solution Structure. Define a minimal credit RA interface and predicates
that can later be refined with real Iris proofs.
-/

set_option autoImplicit false
noncomputable section

/-! ## Credits -/

abbrev CostCredit := Nat -- Base unit of computation credits.

def cost_credit_own (γ : GhostName) (n : CostCredit) : iProp :=
  -- Ownership of n computation credits.
  own γ n

def cost_credit_auth (γ : GhostName) (n : CostCredit) : iProp :=
  -- Authoritative credit counter for the total budget.
  own γ n

def cost_credit_split (_n m k : CostCredit) : Prop :=
  -- Split credits into two parts.
  m + k = _n

def cost_credit_consume (_n cost : CostCredit) : Prop :=
  -- Consuming cost from a credit budget is valid.
  cost ≤ _n

/-! ## Configuration checks -/

def cost_model_ok {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (cfg : VMConfig ι γ π ε ν) : Prop :=
  -- Configuration respects minimum cost assumptions.
  (cfg.costModel.minCost ≥ 1) ∧
    (∀ i, i ≠ .halt → cfg.costModel.stepCost i ≥ cfg.costModel.minCost)

def step_cost {ι γ π ε ν : Type}
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (cfg : VMConfig ι γ π ε ν) (i : Instr γ ε) : Nat :=
  -- Extract the configured step cost.
  cfg.costModel.stepCost i
