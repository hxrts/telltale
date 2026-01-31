import Std
import Runtime.VM.State

/-
The Problem. Instruction semantics need reusable helper functions for
buffers, registers, and result packaging.

Solution Structure. Provide small helpers for buffer updates, register
access, and result construction used by per-instruction steps.
-/

set_option autoImplicit false

universe u

/-! ## Helper bundles -/

structure StepPack (ι γ π ε ν : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectModel ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] where
  -- Bundle updated coroutine/state/result from a single step.
  coro : CoroutineState γ ε
  st : VMState ι γ π ε ν
  res : ExecResult γ

/-! ## Buffer helpers -/

def edgeOf (ep : Endpoint) : Edge :=
  -- Build a self-edge for single-endpoint buffering.
  { sid := ep.sid, sender := ep.role, receiver := ep.role }

def bufEnqueue (bufs : List (Edge × List Value)) (edge : Edge)
    (v : Value) : List (Edge × List Value) :=
  -- Add a value to the edge buffer, creating it if missing.
  match bufs with
  | [] => [(edge, [v])]
  | (e, vs) :: rest =>
      if _h : e = edge then
        (e, vs ++ [v]) :: rest
      else
        (e, vs) :: bufEnqueue rest edge v

def bufDequeue (bufs : List (Edge × List Value)) (edge : Edge) :
    Option (Value × List (Edge × List Value)) :=
  -- Remove the oldest value for the edge, if any.
  match bufs with
  | [] => none
  | (e, vs) :: rest =>
      if _h : e = edge then
        match vs with
        | [] => none
        | v :: vs' => some (v, (e, vs') :: rest)
      else
        match bufDequeue rest edge with
        | none => none
        | some (v, rest') => some (v, (e, vs) :: rest')

def buffersFor (bufs : List (Edge × List Value)) (sid : SessionId) :
    List (Edge × List Value) :=
  -- Project buffers for a given session id.
  bufs.filter (fun p => decide (p.fst.sid = sid))

def updateSessBuffers (store : SessionStore) (sid : SessionId)
    (bufs : List (Edge × List Value)) : SessionStore :=
  -- Refresh the buffers for a specific session.
  match store with
  | [] => []
  | (sid', s) :: rest =>
      if _h : sid' = sid then
        (sid', { s with buffers := buffersFor bufs sid }) :: rest
      else
        (sid', s) :: updateSessBuffers rest sid bufs

def appendEvent {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν)
    (ev : Option StepEvent) : VMState ι γ π ε ν :=
  -- Record an event in the observable trace.
  match ev with
  | none => st
  | some e => { st with obsTrace := st.obsTrace ++ [e] }

/-! ## Register helpers -/

def advancePc {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (coro : CoroutineState γ ε) : CoroutineState γ ε :=
  -- Advance the program counter to the next instruction.
  { coro with pc := coro.pc + 1 }

def readReg (regs : RegFile) (r : Reg) : Option Value :=
  -- Safe register read.
  regs[r]?

def setReg (regs : RegFile) (r : Reg) (v : Value) : Option RegFile :=
  -- Safe register write.
  if h : r < regs.size then
    some (regs.set (i := r) (v := v) (h := h))
  else
    none

def owns {γ ε : Type u} [GuardLayer γ] [EffectModel ε]
    (c : CoroutineState γ ε) (ep : Endpoint) : Bool :=
  -- Check endpoint ownership for linear use.
  c.ownedEndpoints.any (fun e => e == ep)

def valTypeOf (v : Value) : ValType :=
  -- Recover a value type for diagnostics only.
  match v with
  | .unit => .unit
  | .bool _ => .bool
  | .nat _ => .nat
  | .string _ => .string
  | .prod v1 v2 => .prod (valTypeOf v1) (valTypeOf v2)
  | .chan ep => .chan ep.sid ep.role

/-! ## Result helpers -/

def mkRes {γ : Type u} (status : ExecStatus γ)
    (event : Option StepEvent) : ExecResult γ :=
  -- Build an execution result.
  { status := status, event := event }

def pack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (coro : CoroutineState γ ε) (st : VMState ι γ π ε ν)
    (res : ExecResult γ) : StepPack ι γ π ε ν :=
  -- Bundle the updated coroutine, state, and result.
  { coro := coro, st := st, res := res }

def faultPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (err : Fault γ) (msg : String) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as faulted and emit a fault event.
  let coro' := { coro with status := .faulted err }
  pack coro' st (mkRes (.faulted err) (some (.fault msg)))

def blockPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (reason : BlockReason γ) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as blocked without producing an event.
  let coro' := { coro with status := .blocked reason }
  pack coro' st (mkRes (.blocked reason) none)

def continuePack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε)
    (ev : Option StepEvent) : StepPack ι γ π ε ν :=
  -- Mark the coroutine ready and continue.
  let coro' := advancePc { coro with status := .ready }
  pack coro' st (mkRes .continue ev)

def haltPack {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coro : CoroutineState γ ε) : StepPack ι γ π ε ν :=
  -- Mark the coroutine as done.
  let coro' := advancePc { coro with status := .done }
  pack coro' st (mkRes .halted none)

def chargeCost {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (cfg : VMConfig ι γ π ε ν) (coro : CoroutineState γ ε)
    (i : Instr γ ε) : Option (CoroutineState γ ε) :=
  -- Deduct instruction cost from the budget when possible.
  let cost := cfg.costModel.stepCost i
  if _h : cost ≤ coro.costBudget then
    some { coro with costBudget := coro.costBudget - cost }
  else
    none

/-! ## Coroutine updates -/

def updateCoro {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (coroId : CoroutineId)
    (coro : CoroutineState γ ε) : VMState ι γ π ε ν :=
  -- Update the coroutine array at the given index.
  if h : coroId < st.coroutines.size then
    { st with coroutines := st.coroutines.set (i := coroId) (v := coro) (h := h) }
  else
    st
