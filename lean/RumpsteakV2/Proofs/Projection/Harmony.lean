import RumpsteakV2.Semantics.EnvStep
import RumpsteakV2.Proofs.Core.Assumptions

/-! # RumpsteakV2.Proofs.Projection.Harmony

Harmony between global steps and environment steps for V2.
-/-

namespace RumpsteakV2.Proofs.Projection.Harmony

/-! ## Claims -/

/-- Claims bundle for harmony lemmas (TODO: fill with formal statements). -/
structure Claims where
  /-- Global step induces environment step. -/
  step_to_envstep : Prop

/-! ## Proofs -/

-- TODO: implement harmony proofs and build the `claims` bundle.

end RumpsteakV2.Proofs.Projection.Harmony
