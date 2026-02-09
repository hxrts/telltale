import Runtime.VM.Composition.DomainComposition

set_option autoImplicit false

universe u

def effect_composition_safe : Prop :=
  ∀ (ε₁ ε₂ : Type u) [EffectRuntime ε₁] [EffectRuntime ε₂]
    (ctx : EffectRuntime.EffectCtx (Sum ε₁ ε₂))
    (a₁ : EffectRuntime.EffectAction ε₁) (a₂ : EffectRuntime.EffectAction ε₂),
      (EffectRuntime.exec (ε := Sum ε₁ ε₂) (Sum.inl a₁) ctx).2 = ctx.2 ∧
      (EffectRuntime.exec (ε := Sum ε₁ ε₂) (Sum.inr a₂) ctx).1 = ctx.1

theorem effect_composition_safe_holds : effect_composition_safe := by
  intro ε₁ ε₂ _ _ ctx a₁ a₂
  cases ctx
  simp [EffectRuntime.exec]

def composed_frame_rule : Prop :=
  ∀ (ι₁ ι₂ γ : Type u)
    [IdentityModel ι₁] [IdentityModel ι₂] [GuardLayer γ]
    [IdentityGuardBridge ι₁ γ] [IdentityGuardBridge ι₂ γ],
      (∀ p, IdentityGuardBridge.bridge (ι := Sum ι₁ ι₂) (γ := γ) (Sum.inl p) =
             IdentityGuardBridge.bridge (ι := ι₁) (γ := γ) p) ∧
      (∀ p, IdentityGuardBridge.bridge (ι := Sum ι₁ ι₂) (γ := γ) (Sum.inr p) =
             IdentityGuardBridge.bridge (ι := ι₂) (γ := γ) p)

theorem composed_frame_rule_holds : composed_frame_rule := by
  intro ι₁ ι₂ γ _ _ _ _ _
  constructor <;> intro p <;> rfl

def composed_persistence_commutation : Prop :=
  ∀ (π ε₁ ε₂ : Type u)
    [PersistenceModel π] [EffectRuntime ε₁] [EffectRuntime ε₂]
    [PersistenceEffectBridge π ε₁] [PersistenceEffectBridge π ε₂],
      (∀ a, PersistenceEffectBridge.bridge (π := π) (ε := Sum ε₁ ε₂) (Sum.inl a) =
             PersistenceEffectBridge.bridge (π := π) (ε := ε₁) a) ∧
      (∀ a, PersistenceEffectBridge.bridge (π := π) (ε := Sum ε₁ ε₂) (Sum.inr a) =
             PersistenceEffectBridge.bridge (π := π) (ε := ε₂) a)

theorem composed_persistence_commutation_holds : composed_persistence_commutation := by
  intro π ε₁ ε₂ _ _ _ _ _
  constructor <;> intro a <;> rfl

def protocol_federation : Prop :=
  effect_composition_safe.{u} ∧ composed_frame_rule.{u} ∧ composed_persistence_commutation.{u}

theorem protocol_federation_holds : protocol_federation := by
  exact ⟨effect_composition_safe_holds, composed_frame_rule_holds, composed_persistence_commutation_holds⟩
