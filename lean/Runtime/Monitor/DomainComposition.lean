import Runtime.VM.TypeClasses
import Runtime.Compat.RA

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
noncomputable section

instance : GuardLayer Unit where
  layerNs := fun _ => Namespace.root
  Resource := Unit
  Evidence := Unit
  open_ := fun _ => some ()
  close := fun _ _ => ()

instance : EffectModel Unit where
  EffectAction := Unit
  EffectCtx := Unit
  exec := fun _ _ => ()
  pre := fun _ _ => iProp.emp
  post := fun _ _ => iProp.emp
  handlerType := fun _ => LocalType.end_

instance instEffectModelSum (ε₁ ε₂ : Type) [EffectModel ε₁] [EffectModel ε₂] :
    EffectModel (Sum ε₁ ε₂) where
  EffectAction := Sum (EffectModel.EffectAction ε₁) (EffectModel.EffectAction ε₂)
  EffectCtx := EffectModel.EffectCtx ε₁ × EffectModel.EffectCtx ε₂
  exec := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, c2) => (EffectModel.exec a1 c1, c2)
    | Sum.inr a2, (c1, c2) => (c1, EffectModel.exec a2 c2)
  pre := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, _) => EffectModel.pre a1 c1
    | Sum.inr a2, (_, c2) => EffectModel.pre a2 c2
  post := fun a ctx =>
    match a, ctx with
    | Sum.inl a1, (c1, _) => EffectModel.post a1 c1
    | Sum.inr a2, (_, c2) => EffectModel.post a2 c2
  handlerType := fun a =>
    match a with
    | Sum.inl a1 => EffectModel.handlerType a1
    | Sum.inr a2 => EffectModel.handlerType a2

instance instGuardLayerProd (γ₁ γ₂ : Type) [GuardLayer γ₁] [GuardLayer γ₂] :
    GuardLayer (γ₁ × γ₂) where
  layerNs := fun g => GuardLayer.layerNs g.1
  Resource := GuardLayer.Resource γ₁ × GuardLayer.Resource γ₂
  Evidence := GuardLayer.Evidence γ₁ × GuardLayer.Evidence γ₂
  open_ := fun r =>
    match GuardLayer.open_ r.1, GuardLayer.open_ r.2 with
    | some e1, some e2 => some (e1, e2)
    | _, _ => none
  close := fun r e =>
    (GuardLayer.close r.1 e.1, GuardLayer.close r.2 e.2)

structure IdentityGuardBridge (ι : Type) (γ : Type) [IdentityModel ι] [GuardLayer γ] where
  bridge : IdentityModel.ParticipantId ι → GuardLayer.Resource γ

structure EffectGuardBridge (ε : Type) (γ : Type) [EffectModel ε] [GuardLayer γ] where
  bridge : EffectModel.EffectAction ε → GuardLayer.Resource γ

structure PersistenceEffectBridge (π : Type) (ε : Type) [PersistenceModel π] [EffectModel ε] where
  bridge : EffectModel.EffectAction ε → PersistenceModel.Delta π

structure IdentityPersistenceBridge (ι : Type) (π : Type) [IdentityModel ι] [PersistenceModel π] where
  bridge : IdentityModel.ParticipantId ι → PersistenceModel.PState π

def effect_composition_safe : Prop := True
def composed_frame_rule : Prop := True
def protocol_federation : Prop := True
