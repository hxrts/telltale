import Runtime.VM.Model.Program

set_option autoImplicit false

universe u

/-! Proof-only image witnesses moved out of `Runtime.VM` so the VM tree stays
executable/translation-oriented. -/

structure VerifiedCodeImage (γ ε : Type u) [GuardLayer γ] [EffectRuntime ε] where
  image : CodeImage γ ε
  wfBlind : Prop
  projectionCorrect : Prop

def VerifiedCodeImage.fromLocalTypes {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    [Inhabited (EffectRuntime.EffectAction ε)]
    (localTypes : List (Role × SessionTypes.LocalTypeR.LocalTypeR))
    (globalType : GlobalType) : VerifiedCodeImage γ ε :=
  { image := CodeImage.fromLocalTypes (γ := γ) (ε := ε) localTypes globalType
  , wfBlind := True
  , projectionCorrect := True }
