import Runtime.VM.Runtime.Monitor
import Runtime.VM.Model.UnitModel
import Runtime.Proofs.EffectBisim.Bridge
import Runtime.Proofs.EffectBisim.ConfigEquivBridge

/-! # Runtime.Proofs.VM.BridgeStrengthening

Strengthened VM bridge statements with explicit premise bundling.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Runtime.Proofs.EffectBisim

section

universe u

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] [EffectSpec ε]

/-- Canonical handler-typing obligation at the VM boundary. -/
def handler_invoke_typed
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId) : Prop :=
  WellTypedInstr (γ:=γ) (ε:=ε)
    (.invoke action) (.handler hsid) (EffectSpec.handlerType action) .end_

/-- Premise bundle for VM bridge theorems.

Premise inventory:
1. `monitorSound` maps to `monitor_sound` in `Runtime/VM/Runtime/Monitor.lean`.
2. `monitorPreserves` maps to `unified_monitor_preserves` in `Runtime/VM/Runtime/Monitor.lean`.
3. `handlerTyping` is discharged by `WellTypedInstr.wt_invoke` from the same monitor layer.

Bridge transport used by end-to-end theorems:
1. `configEquiv_iff_effectBisim_silent` in `Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean`.
2. `effectBisim_implies_observationalEquivalence` in `Runtime/Proofs/EffectBisim/Bridge.lean`. -/
structure VMBridgePremises (m : SessionMonitor γ) : Prop where
  monitorSound : monitor_sound (γ:=γ) (ε:=ε) m
  monitorPreserves : unified_monitor_preserves m
  handlerTyping :
    ∀ (action : EffectRuntime.EffectAction ε) (hsid : HandlerId),
      handler_invoke_typed (γ:=γ) (ε:=ε) action hsid

/-- Canonical constructor for bridge premises from monitor contracts. -/
theorem vmBridgePremises_of_monitor
    (m : SessionMonitor γ)
    (hSound : monitor_sound (γ:=γ) (ε:=ε) m)
    (hPres : unified_monitor_preserves m) :
    VMBridgePremises (γ:=γ) (ε:=ε) m := by
  refine ⟨hSound, hPres, ?_⟩
  intro action hsid
  exact WellTypedInstr.wt_invoke action hsid

/-- Local handler-typing bridge obligation. -/
theorem handler_obligation_local
    {m : SessionMonitor γ}
    (hPrem : VMBridgePremises (γ:=γ) (ε:=ε) m)
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid :=
  hPrem.handlerTyping action hsid

/-- Short handler fragment obligation over a list of effect actions. -/
def handler_fragment_typing
    (hsid : HandlerId) (actions : List (EffectRuntime.EffectAction ε)) : Prop :=
  ∀ action, action ∈ actions →
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid

/-- Any handler fragment is well typed under bridge premises. -/
theorem handler_fragment_typing_of_premises
    {m : SessionMonitor γ}
    (hPrem : VMBridgePremises (γ:=γ) (ε:=ε) m)
    (hsid : HandlerId) (actions : List (EffectRuntime.EffectAction ε)) :
    handler_fragment_typing (γ:=γ) (ε:=ε) hsid actions := by
  intro action hMem
  exact handler_obligation_local (γ:=γ) (ε:=ε) hPrem action hsid

/-- VM-step level bridge fact for handler steps.
    The theorem states explicit pre and post typing judgments and monitor sid preservation. -/
theorem handler_vm_step_typing
    {m : SessionMonitor γ}
    (hPrem : VMBridgePremises (γ:=γ) (ε:=ε) m)
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId)
    {sk sk' : SessionKind γ}
    (hStep : m.step sk = some sk')
    (hHandler : sk = .handler hsid) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid ∧
    SessionKind.sid? sk' = SessionKind.sid? sk := by
  cases hHandler
  refine ⟨handler_obligation_local (γ:=γ) (ε:=ε) hPrem action hsid, ?_⟩
  exact hPrem.monitorPreserves _ _ hStep

/-- End-to-end bridge theorem used by paper-level bridge statements.
    Handler typing obligations are transported together with observational equivalence. -/
theorem vm_bridge_soundness_composed
    {m : SessionMonitor γ}
    (hPrem : VMBridgePremises (γ:=γ) (ε:=ε) m)
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId)
    {sk sk' : SessionKind γ}
    {C₁ C₂ : CoherenceConfig}
    (hStep : m.step sk = some sk')
    (hHandler : sk = .handler hsid)
    (hCfg : ConfigEquiv C₁ C₂) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid ∧
    ObservationalEq configErasureObs C₁ C₂ := by
  have hLocal := handler_vm_step_typing (γ:=γ) (ε:=ε) hPrem action hsid hStep hHandler
  have hBisim : EffectBisim configErasureObs configSilentStep C₁ C₂ :=
    (configEquiv_iff_effectBisim_silent C₁ C₂).1 hCfg
  have hObs : ObservationalEq configErasureObs C₁ C₂ :=
    effectBisim_implies_observationalEquivalence configErasureObs configSilentStep hBisim
  exact ⟨hLocal.1, hObs⟩

end

section

/-- Intentionally non-conforming monitor for premise-audit regression tests.
    It rewrites protocol session ids and therefore breaks sid preservation. -/
def sid_shifting_monitor : SessionMonitor UnitGuard :=
  { step := fun sk =>
      match sk with
      | .protocol sid => some (.protocol (sid + 1))
      | _ => some sk }

/-- Audit witness: `sid_shifting_monitor` violates `unified_monitor_preserves`. -/
theorem sid_shifting_monitor_not_unified_preserves :
    ¬ unified_monitor_preserves sid_shifting_monitor := by
  intro h
  have hEq : SessionKind.sid? (.protocol (0 + 1 : SessionId)) = SessionKind.sid? (.protocol (0 : SessionId)) :=
    h (.protocol (0 : SessionId)) (.protocol (0 + 1 : SessionId)) rfl
  have hContra : (some (1 : SessionId)) = some (0 : SessionId) := by
    simpa [SessionKind.sid?] using hEq
  have hSidEq : (1 : SessionId) = 0 := Option.some.inj hContra
  cases hSidEq

/-- Audit witness lifted to the bundled bridge premises. -/
theorem sid_shifting_monitor_not_bridge_premises
    {ε : Type} [EffectRuntime ε] [EffectSpec ε] :
    ¬ VMBridgePremises (γ:=UnitGuard) (ε:=ε) sid_shifting_monitor := by
  intro hPrem
  exact sid_shifting_monitor_not_unified_preserves hPrem.monitorPreserves

end
