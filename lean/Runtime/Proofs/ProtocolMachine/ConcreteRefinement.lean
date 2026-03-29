import Runtime.ProtocolMachine.Semantics.ExecHelpers
import Runtime.Proofs.ProtocolMachine.InstrSpec.ConfigEquivSendRecv
import Runtime.Proofs.ProtocolMachine.Scheduler
import Runtime.Proofs.SchedulerApi
import Runtime.Proofs.ConcurrencyThreaded

/-! # Runtime.Proofs.ProtocolMachine.ConcreteRefinement

Concrete projection helpers for the first implementation-facing protocol-machine
refinement slice. The slice intentionally tracks only:

- session-local type counts
- buffered message counts
- scheduler ready / blocked state
- coroutine-local program counters and status tags

This is the smallest nontrivial state surface that the Rust runtime, Lean
runner, and threaded runtime can compare exactly today.
-/

set_option autoImplicit false

universe u

namespace Runtime
namespace Proofs

section

variable {ι γ π ε ν : Type u}
variable [IdentityModel ι] [GuardLayer γ]
variable [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
variable [AuthTree ν] [AccumulatedSet ν]
variable [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
variable [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
variable [IdentityVerificationBridge ι ν]

structure ConcreteCoroutineSlice where
  coroId : CoroutineId
  sessionId : SessionId
  pc : PC
  statusTag : String
  ownedEndpointCount : Nat
  progressTokenCount : Nat
  deriving Repr, DecidableEq

structure ConcreteSessionSlice where
  sid : SessionId
  roleCount : Nat
  localTypeCount : Nat
  bufferedMessageCount : Nat
  epoch : Nat
  deriving Repr, DecidableEq

structure ConcreteSchedulerSlice where
  readyQueue : List CoroutineId
  blocked : List (CoroutineId × String)
  stepCount : Nat
  deriving Repr, DecidableEq

structure ConcreteProtocolMachineSlice where
  coroutines : List ConcreteCoroutineSlice
  sessions : List ConcreteSessionSlice
  scheduler : ConcreteSchedulerSlice
  deriving Repr, DecidableEq

def concreteCoroStatusTag : CoroStatus γ → String
  | .ready => "ready"
  | .blocked _ => "blocked"
  | .done => "done"
  | .faulted _ => "faulted"
  | .speculating => "speculating"

def concreteBlockReasonTag : BlockReason γ → String
  | .recvWait _ _ => "recv_wait"
  | .sendWait _ => "send_wait"
  | .acquireDenied _ => "acquire_denied"
  | .invokeWait _ => "invoke_wait"
  | .consensusWait _ => "consensus_wait"
  | .spawnWait => "spawn_wait"
  | .closeWait _ => "close_wait"

def projectConcreteCoroutineSlice (coro : CoroutineState γ ε) : ConcreteCoroutineSlice :=
  { coroId := coro.id
  , sessionId := match coro.ownedEndpoints.head? with
      | some ep => ep.sid
      | none => 0
  , pc := coro.pc
  , statusTag := concreteCoroStatusTag coro.status
  , ownedEndpointCount := coro.ownedEndpoints.length
  , progressTokenCount := coro.progressTokens.length
  }

def projectConcreteSessionSlice (entry : SessionId × SessionState ν) : ConcreteSessionSlice :=
  { sid := entry.1
  , roleCount := entry.2.roles.length
  , localTypeCount := entry.2.localTypes.length
  , bufferedMessageCount := entry.2.buffers.foldl (fun acc p => acc + p.2.length) 0
  , epoch := entry.2.epoch
  }

def projectConcreteSchedulerSlice (sched : SchedState γ) : ConcreteSchedulerSlice :=
  { readyQueue := sched.readyQueue
  , blocked := sched.blockedSet.toList.map (fun p => (p.1, concreteBlockReasonTag p.2))
  , stepCount := sched.stepCount
  }

def projectConcreteProtocolMachineSlice
    (st : ProtocolMachineState ι γ π ε ν) : ConcreteProtocolMachineSlice :=
  { coroutines := st.coroutines.toList.map projectConcreteCoroutineSlice
  , sessions := st.sessions.map projectConcreteSessionSlice
  , scheduler := projectConcreteSchedulerSlice st.sched
  }

theorem project_concrete_scheduler_slice_syncLaneViews
    (sched : SchedState γ) :
    projectConcreteSchedulerSlice (syncLaneViews sched) =
      projectConcreteSchedulerSlice sched := by
  simp [projectConcreteSchedulerSlice, syncLaneViews]

theorem concrete_send_slice_preserves_coherent
    {G G' : GEnv} {D D' : DEnv}
    {senderEp : Endpoint} {receiverRole : Role} {T : ValType}
    (hSpec : SendSpec G G' D D' senderEp receiverRole T)
    (hCoh : Coherent G D)
    (hReady : SendReady G D) :
    Coherent G' D' :=
  send_spec_preserves_coherent hSpec hCoh hReady

theorem concrete_recv_slice_preserves_coherent
    {G G' : GEnv} {D D' : DEnv}
    {receiverEp : Endpoint} {senderRole : Role} {T : ValType}
    (hSpec : RecvSpec G G' D D' receiverEp senderRole T)
    (hCoh : Coherent G D) :
    Coherent G' D' :=
  recv_spec_preserves_coherent hSpec hCoh

theorem concrete_scheduler_slice_confluent
    (st : ProtocolMachineState ι γ π ε ν) :
    schedule_confluence st :=
  schedule_confluence_holds st

theorem concrete_scheduler_slice_cooperative_refines_concurrent
    (st : ProtocolMachineState ι γ π ε ν) :
    cooperative_refines_concurrent st :=
  cooperative_refines_concurrent_holds st

theorem concrete_slice_scheduler_iris_invariant_from_bundle [Telltale.TelltaleIris]
    {st₀ : ProtocolMachineState ι γ π ε ν}
    (bundle : Runtime.Proofs.ProtocolMachineSchedulerBundle st₀) :
    Runtime.Proofs.SchedulerIrisInvariant
      (ι := ι) (γ := γ) (π := π) (ε := ε) (ν := ν) st₀ :=
  Runtime.Proofs.scheduler_iris_invariant_from_bundle bundle

theorem concrete_slice_threaded_one_refines_canonical
    (fuel : Nat) (st : ProtocolMachineState ι γ π ε ν) :
    runScheduledThreaded fuel 1 st = runScheduled fuel 1 st :=
  run_scheduled_threaded_one_eq_run_scheduled fuel st

end

end Proofs
end Runtime
