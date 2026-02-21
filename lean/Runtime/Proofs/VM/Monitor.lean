import Runtime.VM.Runtime.Monitor

set_option autoImplicit false

/-! # Runtime.Proofs.VM.Monitor

Proof-only monitor contract lemmas.
-/

universe u

/-- Any monitor satisfies `monitor_sound` because pure control-flow instructions
    are always accepted by `monitorAllows`. -/
theorem monitor_sound_any {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (m : SessionMonitor γ) :
    monitor_sound (γ:=γ) (ε:=ε) m := by
  intro i hNoSession
  cases i <;> simp [instrNeedsSession, monitorAllows] at hNoSession ⊢

/-- The identity-step monitor preserves protocol session ids. -/
theorem unified_monitor_preserves_identity {γ : Type u} :
    unified_monitor_preserves ({ step := fun sk : SessionKind γ => some sk } : SessionMonitor γ) := by
  intro sk sk' hStep
  simpa using congrArg SessionKind.sid? (Option.some.inj hStep).symm
