import Protocol.DeliveryModel
import Protocol.Coherence.EdgeCoherence


/-! # Head Coherence (Model-Parametric)

HeadCoherent does not depend on the delivery model for FIFO semantics.
We expose an M-parameterized wrapper for migration and prove FIFO equivalence.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-- HeadCoherent, parameterized by a delivery model (currently ignored). -/
def HeadCoherentM (_M : DeliveryModel) (G : GEnv) (D : DEnv) : Prop :=
  HeadCoherent G D

@[simp] theorem HeadCoherentM_fifo_eq (G : GEnv) (D : DEnv) :
    HeadCoherentM DeliveryModel.fifo G D = HeadCoherent G D := by
  rfl

end
