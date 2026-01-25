import RumpsteakV2.Semantics.Typing

/-! # RumpsteakV2.Proofs.Safety.Progress

Progress for V2.
-/

namespace RumpsteakV2.Proofs.Safety.Progress

/-! ## Claims -/

/-- Claims bundle for progress (TODO: fill with formal statements). -/
structure Claims where
  /-- Progress: well-typed configurations can step or are terminal. -/
  progress : Prop

/-! ## Proofs -/

-- TODO: implement progress and build the `claims` bundle.

end RumpsteakV2.Proofs.Safety.Progress
