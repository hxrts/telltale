import Paco

/-! # CoinductiveRelPaco

Thin wrappers around paco's coinduction principles for reuse.
-/

namespace RumpsteakV2.Protocol.CoTypes.CoinductiveRelPaco

open Paco

/-- Coinduction up-to: wrapper around `paco_coind'`. -/
theorem coind_upto {α : Type*} (F : MonoRel α) (r : Rel α) (R : Rel α)
    (hpost : ∀ a b, R a b → F (R ⊔ r) a b) : R ≤ paco F r :=
  Paco.paco_coind' F r R hpost

/-- Pointwise coinduction up-to: wrapper around `paco_coind`. -/
theorem coind_upto_pointwise {α : Type*} (F : MonoRel α) (R r : Rel α)
    {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ r) a b)
    (hxy : R x y) : paco F r x y :=
  Paco.paco_coind F R r hpost hxy


/-- Coinduction with accumulation (pointwise): wrapper around `paco_coind_acc`. -/
theorem coind_upto_acc {α : Type*} (F : MonoRel α) (R r : Rel α)
    {x y : α}
    (hpost : ∀ a b, R a b → F (R ⊔ (paco F r ⊔ r)) a b)
    (hxy : R x y) : paco F r x y :=
  Paco.paco_coind_acc F R r hpost hxy

end RumpsteakV2.Protocol.CoTypes.CoinductiveRelPaco
