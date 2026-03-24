import Runtime.VM.Runtime.Monitor
import Runtime.VM.Model.UnitModel
import Runtime.Proofs.EffectBisim.Bridge
import Runtime.Proofs.EffectBisim.ConfigEquivBridge

/-! # Runtime.Proofs.BridgeStrengthening

Strengthened protocol-machine bridge statements with explicit premise bundling.
-/

/-
The Problem. Protocol-machine bridge theorems rely on several monitor/typing obligations that
are easy to scatter across files, making transport assumptions hard to audit.

Solution Structure. Bundle bridge premises in one structure, derive local handler
obligations from that bundle, then compose with ConfigEquiv/EffectBisim transport.
-/

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open Runtime.Proofs.EffectBisim

section

universe u

variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε] [EffectSpec ε]

/-! ## Bridge Premises and Local Obligations -/

/-- Canonical handler-typing obligation at the protocol-machine boundary. -/
def handler_invoke_typed
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId) : Prop :=
  WellTypedInstr (γ:=γ) (ε:=ε)
    (.invoke action) (.handler hsid) (EffectSpec.handlerType action) .end_

/-- Premise bundle for protocol-machine bridge theorems.

Premise inventory:
1. `monitorSound` maps to `monitor_sound` in `Runtime/VM/Runtime/Monitor.lean`.
2. `monitorPreserves` maps to `unified_monitor_preserves` in `Runtime/VM/Runtime/Monitor.lean`.
3. `handlerTyping` is discharged by `WellTypedInstr.wt_invoke` from the same monitor layer.

Bridge transport used by end-to-end theorems:
1. `config_equiv_iff_effect_bisim_silent` in `Runtime/Proofs/EffectBisim/ConfigEquivBridge.lean`.
2. `effect_bisim_implies_observational_equivalence` in `Runtime/Proofs/EffectBisim/Bridge.lean`. -/
structure ProtocolMachineBridgePremises (m : SessionMonitor γ) : Prop where
  monitorSound : monitor_sound (γ:=γ) (ε:=ε) m
  monitorPreserves : unified_monitor_preserves m
  handlerTyping :
    ∀ (action : EffectRuntime.EffectAction ε) (hsid : HandlerId),
      handler_invoke_typed (γ:=γ) (ε:=ε) action hsid

/-- Canonical constructor for bridge premises from monitor contracts. -/
theorem protocol_machine_bridge_premises_of_monitor
    (m : SessionMonitor γ)
    (hSound : monitor_sound (γ:=γ) (ε:=ε) m)
    (hPres : unified_monitor_preserves m) :
    ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m := by
  refine ⟨hSound, hPres, ?_⟩
  intro action hsid
  exact WellTypedInstr.wt_invoke action hsid

/-- Local handler-typing bridge obligation. -/
theorem handler_obligation_local
    {m : SessionMonitor γ}
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
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
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
    (hsid : HandlerId) (actions : List (EffectRuntime.EffectAction ε)) :
    handler_fragment_typing (γ:=γ) (ε:=ε) hsid actions := by
  intro action hMem
  exact handler_obligation_local (γ:=γ) (ε:=ε) hPrem action hsid

/-! ## Nominal Effect-Interface Bridge -/

/-- Nominal DSL effect interface declaration lowered through the protocol-machine `invoke`
boundary rather than a separate host channel. -/
structure NominalEffectInterfaceDecl where
  name : String
  actions : List (EffectRuntime.EffectAction ε)

/-- Every action named by the interface must satisfy the same handler typing
obligation as a raw protocol-machine `invoke`. -/
def effect_interface_decl_typed
    (decl : NominalEffectInterfaceDecl (ε:=ε)) (hsid : HandlerId) : Prop :=
  ∀ action, action ∈ decl.actions →
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid

/-- Protocol-machine bridge premises are strong enough to justify one nominal DSL effect
interface through the existing `invoke` boundary. -/
theorem effect_interface_decl_typed_of_premises
    {m : SessionMonitor γ}
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
    (decl : NominalEffectInterfaceDecl (ε:=ε))
    (hsid : HandlerId) :
    effect_interface_decl_typed (γ:=γ) (ε:=ε) decl hsid := by
  intro action hMem
  exact handler_obligation_local (γ:=γ) (ε:=ε) hPrem action hsid

/-- Any invocation routed through a declared effect interface preserves the same
typed boundary used by the runtime monitor. -/
theorem effect_interface_invocation_preserves_boundary
    {m : SessionMonitor γ}
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
    (decl : NominalEffectInterfaceDecl (ε:=ε))
    (hsid : HandlerId)
    (action : EffectRuntime.EffectAction ε)
    (hMem : action ∈ decl.actions) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid := by
  exact effect_interface_decl_typed_of_premises (γ:=γ) (ε:=ε) hPrem decl hsid action hMem

/-! ## Protocol-Machine Step Typing Bridge -/

/-- Protocol-machine step-level bridge fact for handler steps.
    The theorem states explicit pre and post typing judgments and monitor sid preservation. -/
theorem handler_protocol_machine_step_typing
    {m : SessionMonitor γ}
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId)
    {sk sk' : SessionKind γ}
    (hStep : m.step sk = some sk')
    (hHandler : sk = .handler hsid) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid ∧
    SessionKind.sid? sk' = SessionKind.sid? sk := by
  cases hHandler
  refine ⟨handler_obligation_local (γ:=γ) (ε:=ε) hPrem action hsid, ?_⟩
  exact hPrem.monitorPreserves _ _ hStep

/-! ## Composed Observational Bridge -/

/-- End-to-end bridge theorem used by paper-level bridge statements.
    Handler typing obligations are transported together with observational equivalence. -/
theorem protocol_machine_bridge_soundness_composed
    {m : SessionMonitor γ}
    (hPrem : ProtocolMachineBridgePremises (γ:=γ) (ε:=ε) m)
    (action : EffectRuntime.EffectAction ε) (hsid : HandlerId)
    {sk sk' : SessionKind γ}
    {C₁ C₂ : CoherenceConfig}
    (hStep : m.step sk = some sk')
    (hHandler : sk = .handler hsid)
    (hCfg : ConfigEquiv C₁ C₂) :
    handler_invoke_typed (γ:=γ) (ε:=ε) action hsid ∧
    ObservationalEq configErasureObs C₁ C₂ := by
  have hLocal := handler_protocol_machine_step_typing (γ:=γ) (ε:=ε) hPrem action hsid hStep hHandler
  have hBisim : EffectBisim configErasureObs configSilentStep C₁ C₂ :=
    (config_equiv_iff_effect_bisim_silent C₁ C₂).1 hCfg
  have hObs : ObservationalEq configErasureObs C₁ C₂ :=
    effect_bisim_implies_observational_equivalence configErasureObs configSilentStep hBisim
  exact ⟨hLocal.1, hObs⟩

end

section

/-! ## Regression Audit Witnesses -/

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
theorem sid_shifting_monitor_not_protocol_machine_bridge_premises
    {ε : Type} [EffectRuntime ε] [EffectSpec ε] :
    ¬ ProtocolMachineBridgePremises (γ:=UnitGuard) (ε:=ε) sid_shifting_monitor := by
  intro hPrem
  exact sid_shifting_monitor_not_unified_preserves hPrem.monitorPreserves

end
