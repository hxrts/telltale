import Runtime.VM.Scheduler
import Runtime.VM.ExecHelpers

/-!
# Scheduled Runner

N-concurrent scheduler-driven execution with receiver unblocking.
-/

set_option autoImplicit false

universe u

/-- Move blocked receivers to the ready queue when their buffer has a message. -/
def tryUnblockReceivers {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  let step := fun (acc : SchedQueue × BlockedSet γ) (p : CoroutineId × BlockReason γ) =>
    let (ready, blocked) := acc
    let (cid, reason) := p
    match reason with
    | .recvWait edge _ =>
        if (signedBufferLookup st.buffers edge).isEmpty then
          (ready, blocked ++ [(cid, reason)])
        else
          (ready ++ [cid], blocked)
    | _ => (ready, blocked ++ [(cid, reason)])
  let (ready', blocked') := st.sched.blockedSet.foldl step (st.sched.readyQueue, [])
  let sched' := { st.sched with readyQueue := ready', blockedSet := blocked' }
  { st with sched := sched' }

/-- Execute one round: advance at most one ready coroutine.
    Concurrency is abstracted away in the canonical runner. -/
def schedRound {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  if n = 0 then
    st
  else
    match schedStep st with
    | none => st
    | some st' => st'

/-- Check if all coroutines have reached a terminal state. -/
def allTerminal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Bool :=
  st.coroutines.all (fun c =>
    match c.status with
    | .done => true
    | .faulted _ => true
    | _ => false)

/-- Check if all coroutines in a specific session are terminal. -/
def sessionTerminal {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (sid : SessionId) : Bool :=
  st.coroutines.all (fun c =>
    if c.ownedEndpoints.any (fun ep => decide (ep.sid = sid)) then
      match c.status with
      | .done => true
      | .faulted _ => true
      | _ => false
    else
      true)

/-- Run rounds until fuel is exhausted, all coroutines are terminal, or stuck. -/
def runScheduled {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectModel ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel : Nat) (concurrency : Nat) (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  let st := { st with sched := { st.sched with policy := .roundRobin } }
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
