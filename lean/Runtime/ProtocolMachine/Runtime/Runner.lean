import Runtime.ProtocolMachine.Runtime.Scheduler
import Runtime.ProtocolMachine.Semantics.ExecHelpers


/-! # Scheduled Runner

N-concurrent scheduler-driven execution with receiver unblocking.
-/

set_option autoImplicit false

universe u

/-! ## Receiver Unblocking -/

/-- Move blocked receivers to the ready queue when their buffer has a message. -/
def tryUnblockReceivers {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : ProtocolMachineState ι γ π ε ν :=
  let wakeCoroutine := fun (stAcc : ProtocolMachineState ι γ π ε ν) (cid : CoroutineId) =>
    match stAcc.coroutines[cid]? with
    | none => stAcc
    | some coro =>
        let coro' := { coro with status := .ready }
        updateCoro stAcc cid coro'
  let step := fun (stAcc : ProtocolMachineState ι γ π ε ν) (p : CoroutineId × BlockReason γ) =>
    let (cid, reason) := p
    match reason with
    | .recvWait edge _ =>
        if (signedBufferLookup stAcc.buffers edge).isEmpty then
          stAcc
        else
          let sched' := unblockCoroutine stAcc.sched cid
          let st' := { stAcc with sched := sched' }
          wakeCoroutine st' cid
    | _ => stAcc
  let st' := st.sched.blockedSet.toList.foldl step { st with sched := syncLaneViews st.sched }
  st'

/-! ## Round Execution -/

/-- Execute one canonical scheduler step when possible. -/
def schedRoundOne {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : ProtocolMachineState ι γ π ε ν :=
  match schedStep st with
  | none => st
  | some st' => st'

/-- Execute one round: advance at most one ready coroutine.
    Concurrency is abstracted away in the canonical runner. -/
def schedRound {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : ProtocolMachineState ι γ π ε ν) : ProtocolMachineState ι γ π ε ν :=
  if n = 0 then
    st
  else
    schedRoundOne st

/-! ## Termination Predicates -/

/-- Check if all coroutines have reached a terminal state. -/
def allTerminal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) : Bool :=
  st.coroutines.all (fun c =>
    match c.status with
    | .done => true
    | .faulted _ => true
    | _ => false)

/-- Check if all coroutines in a specific session are terminal. -/
def sessionTerminal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : ProtocolMachineState ι γ π ε ν) (sid : SessionId) : Bool :=
  match st.sessions.find? (fun p => decide (p.fst = sid)) with
  | some (_, session) =>
      match session.phase with
      | .active => false
      | _ => true
  | none => true

/-! ## Fuel-Bounded Scheduled Runner -/

/-- Run rounds until fuel is exhausted, all coroutines are terminal, or stuck. -/
def runScheduled {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel : Nat) (concurrency : Nat) (st : ProtocolMachineState ι γ π ε ν) : ProtocolMachineState ι γ π ε ν :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
      let st' := { st with clock := st.clock + 1 }
      let st'' := tryUnblockReceivers st'
      let st''' := schedRound concurrency st''
      if allTerminal st''' then
        st'''
      else if st'''.sched.stepCount = st''.sched.stepCount then
        st'''
      else
        runScheduled fuel' concurrency st'''

/-! ## Invariance proofs live in `Runtime.Proofs.Concurrency`. -/
