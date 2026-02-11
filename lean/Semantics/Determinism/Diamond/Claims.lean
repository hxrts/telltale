import Semantics.Determinism.Diamond.Core

/-! # Semantics.Determinism.Diamond.Claims

Claims bundle for determinism/diamond results.
-/

/-
The Problem. Downstream modules need one object carrying the determinism and
commutation facts instead of importing individual lemmas.

Solution Structure. Defines a `Claims` structure and populates it from the
proved theorems in `Core`.
-/

namespace Semantics.Determinism

/-! ## Claims Bundle -/

/-! ## Claims Bundle -/

/-- Claims bundle for determinism. -/
structure Claims where
  /-- Global step determinism (requires uniqueBranchLabels). -/
  global_step_det : ∀ {g g₁ g₂ : GlobalType} {act : GlobalActionR},
      g.uniqueBranchLabels = true → step g act g₁ → step g act g₂ → g₁ = g₂
  /-- Environment step determinism. -/
  env_step_det : ∀ {env env₁ env₂ : EnvConfig} {act : EnvAction},
      EnvConfigStep env act env₁ → EnvConfigStep env act env₂ → env₁ = env₂
  /-- Configuration step determinism. -/
  config_step_det : ∀ {c c₁ c₂ : Configuration} {act : GlobalActionR},
      ConfigStep c c₁ act → ConfigStep c c₂ act → c₁ = c₂
  /-- Diamond property for independent actions. -/
  diamond_independent : ∀ {c c₁ c₂ : Configuration} {act₁ act₂ : GlobalActionR},
      IndependentActions act₁ act₂ →
      ConfigStep c c₁ act₁ → ConfigStep c c₂ act₂ →
      ∃ c₃, ConfigStep c₁ c₃ act₂ ∧ ConfigStep c₂ c₃ act₁

/-- Build the claims bundle from proven theorems. -/
def claims : Claims where
  -- Package determinism theorems.
  global_step_det := global_step_det
  env_step_det := env_step_det
  config_step_det := config_step_det
  diamond_independent := diamond_independent

end Semantics.Determinism
