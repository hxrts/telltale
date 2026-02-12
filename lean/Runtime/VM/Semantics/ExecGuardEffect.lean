import Runtime.VM.Semantics.ExecHelpers


/-! # Guard and Effect Instruction Semantics

Step functions for `acquire`, `release`, and `invoke`.

`stepAcquire` opens a guard layer: checks that the layer is active, looks up the
guard resource, calls `GuardLayer.open_` to produce evidence, encodes the evidence
into a destination register, and emits an `acquired` event.

`stepRelease` closes a guard layer: decodes evidence from a register, calls
`GuardLayer.close` to update the resource, and emits a `released` event.

`stepInvoke` executes an effect action: looks up the default handler, calls
`EffectRuntime.exec` to update the effect context, applies the persistence delta
via `PersistenceEffectBridge.bridge`, and emits an `invoked` event.

All three use `primaryEndpoint` (the first owned endpoint) as the representative
endpoint for observable event attribution.
-/

set_option autoImplicit false

universe u

/-! ## Guard and effect semantics -/

private def primaryEndpoint {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (coro : CoroutineState γ ε) : Option Endpoint :=
  -- Choose a representative endpoint for observability.
  match coro.ownedEndpoints with
  | e :: _ => some e
  | [] => none

/-! ## Acquire -/

def stepAcquire {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (layer : γ) (dst : Reg) : StepPack ι γ π ε ν :=
  -- Acquire a guard-layer resource and return evidence.
  if st.config.guardChain.active layer = false then
    faultPack st coro (.acquireFault "guard-layer" "inactive layer") "inactive layer"
  else
    match guardResourceLookup st.guardResources layer with
    | none => faultPack st coro (.acquireFault "guard-layer" "unknown layer") "unknown layer"
    | some r =>
        match GuardLayer.open_ r with
        | none => blockPack st coro (.acquireDenied layer)
        | some ev =>
            let encoded := GuardLayer.encodeEvidence ev
            match setReg coro.regs dst encoded with
            | none => faultPack st coro .outOfRegisters "bad dst reg"
            | some regs' =>
                let ev :=
                  match primaryEndpoint coro with
                  | some ep => StepEvent.obs (.acquired (GuardLayer.layerId layer) ep)
                  | none => StepEvent.internal
                continuePack st { coro with regs := regs' } (some ev)

/-! ## Release -/

def stepRelease {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (_layer : γ) (_evidence : Reg) : StepPack ι γ π ε ν :=
  -- Release a guard-layer resource and record the layer.
  if st.config.guardChain.active _layer = false then
    faultPack st coro (.acquireFault "guard-layer" "inactive layer") "inactive layer"
  else
    match readReg coro.regs _evidence with
    | none => faultPack st coro .outOfRegisters "missing evidence"
    | some v =>
        match GuardLayer.decodeEvidence v with
        | none => faultPack st coro (.acquireFault "guard-layer" "bad evidence") "bad evidence"
        | some evd =>
            match guardResourceLookup st.guardResources _layer with
            | none => faultPack st coro (.acquireFault "guard-layer" "unknown layer") "unknown layer"
            | some _ =>
                let rs' := guardResourceUpdate st.guardResources _layer (fun r => GuardLayer.close r evd)
                let st' := { st with guardResources := rs' }
                let ev :=
                  match primaryEndpoint coro with
                  | some ep => StepEvent.obs (.released (GuardLayer.layerId _layer) ep)
                  | none => StepEvent.internal
                continuePack st' coro (some ev)

/-! ## Invoke -/

def stepInvoke {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π] [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (action : EffectRuntime.EffectAction ε) : StepPack ι γ π ε ν :=
  -- Execute an effect action via the bound handler.
  match SessionStore.defaultHandler st.sessions with
  | none =>
      faultPack st coro (.invokeFault "no handler bound") "no handler bound"
  | some _handlerId =>
      let ctx' := EffectRuntime.exec action coro.effectCtx
      let delta := PersistenceEffectBridge.bridge (π:=π) (ε:=ε) action
      let persist' := PersistenceModel.apply st.persistent delta
      let st' := { st with persistent := persist' }
      let ev :=
        match primaryEndpoint coro with
        | some ep => StepEvent.obs (.invoked ep action)
        | none => StepEvent.internal
      continuePack st' { coro with effectCtx := ctx' } (some ev)
