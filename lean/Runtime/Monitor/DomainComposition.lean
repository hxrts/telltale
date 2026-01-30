import Runtime.VM.TypeClasses
import Runtime.Shim.ResourceAlgebra

/-!
# Task 24: Domain Model Composition

Coproduct/product instances and bridge classes for composable domain models
from iris_runtime_2.md §20.

## Definitions

- Unit instances (`EffectModel Unit`, `GuardLayer Unit`)
- `EffectModel (ε₁ ⊕ ε₂)` — effect coproduct
- `GuardLayer (γ₁ × γ₂)` — guard product
- Bridge classes: `IdentityGuardBridge`, `EffectGuardBridge`,
  `PersistenceEffectBridge`, `IdentityPersistenceBridge`
- `effect_composition_safe`
- `composed_frame_rule`
- `protocol_federation`

Dependencies: Task 10, Shim.ResourceAlgebra.
-/

set_option autoImplicit false

-- TODO: implement Task 24
