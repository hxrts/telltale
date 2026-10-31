import Runtime.Tests.NominalImageRunner

import Lean.Data.Json
import Runtime.ProtocolMachine.Model.UnitModel
import Runtime.ProtocolMachine.Runtime.Json
import Runtime.ProtocolMachine.Runtime.Loader
import Runtime.ProtocolMachine.Runtime.Runner
import Runtime.ProtocolMachine.Runtime.Scheduler
import Runtime.ProtocolMachine.Runtime.Monitor
import Runtime.Proofs.ProtocolMachine.ConcreteRefinement
import Runtime.Proofs.ProtocolMachine.Monitor
import Runtime.ProtocolMachine.Semantics.Exec
import Choreography.Projection.Json
import Choreography.Projection.Project.Primitive

/-! # protocol machine Runner: core state and step-state JSON

Runner state initialization (`emptyArena`, `emptyMonitor`, `emptyState`), choreography
parsing, concrete scheduler/trace slice JSON encoders, and the step-state collecting
run loop used by `Runtime.Tests.ProtocolMachineRunner`.
-/

set_option autoImplicit false

open Lean (Json)
open Choreography.Projection.Json


/-- Empty arena for the runner. -/
def emptyArena : Arena :=
  { slots := #[], nextFree := 0, capacity := 0, inv := by exact Nat.le_refl 0 }

/-- Permissive monitor for the runner. -/
def emptyMonitor : SessionMonitor UnitGuard :=
  { step := fun sk => some sk }

/-- The runner monitor satisfies the control-flow acceptance contract. -/
theorem empty_monitor_monitor_sound {ε : Type} [EffectRuntime ε] :
    monitor_sound (γ:=UnitGuard) (ε:=ε) emptyMonitor := by
  simpa [emptyMonitor] using (monitor_sound_any (γ:=UnitGuard) (ε:=ε) emptyMonitor)

/-- The runner monitor preserves protocol session ids. -/
theorem empty_monitor_unified_monitor_preserves :
    unified_monitor_preserves emptyMonitor := by
  simpa [emptyMonitor] using (unified_monitor_preserves_identity (γ:=UnitGuard))

/-- Empty protocol machine state for loading choreographies. -/
def emptyState : ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
  { config := unitConfig
  , code := { code := #[], entryPoints := [], localTypes := [], handlerTypes := [], metadata := ProgramMeta.empty }
  , programs := #[]
  , coroutines := #[]
  , buffers := []
  , persistent := ()
  , nextCoroId := 0
  , nextSessionId := 0
  , arena := emptyArena
  , sessions := []
  , resourceStates := {}
  , guardResources := []
  , sched := { policy := unitConfig.schedPolicy, readyQueue := [], blockedSet := {}, timeslice := 1, stepCount := 0 }
  , monitor := emptyMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := default
  , progressSupply := () }

/-- Parse one choreography block from JSON. -/
def parseChoreo (j : Json) : Except String (GlobalType × List Role) := do
  let gJson := j.getObjValD "global_type"
  let g ← globalTypeFromJson gJson
  let rolesArr ← j.getObjValAs? (Array Json) "roles"
  let roles ← rolesArr.toList.mapM (fun rj => rj.getStr?)
  .ok (g, roles)

/-- Build a CodeImage from a global type and role list. -/
def buildImage (g : GlobalType) (roles : List Role) : CodeImage UnitGuard UnitEffect :=
  let locals := roles.map (fun r => (r, Choreography.Projection.Project.trans g r))
  CodeImage.fromLocalTypes locals g

abbrev RunnerState :=
  ProtocolMachineState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify

def execStatusTag : ExecStatus UnitGuard → String
  | .continue => "continue"
  | .yielded => "yielded"
  | .blocked _ => "blocked"
  | .halted => "halted"
  | .faulted _ => "faulted"
  | .spawned _ => "spawned"
  | .transferred _ _ => "transferred"
  | .closed _ => "closed"
  | .forked _ => "forked"
/- ## Structured Block 2 -/
  | .joined => "joined"
  | .aborted => "aborted"

def natAssocJson (entries : List (Nat × Nat)) : Json :=
  Json.mkObj <| entries.map (fun p => (toString p.fst, Json.num p.snd))

def sortedSessionStatusesJson (st : RunnerState) : Array Json :=
  ((st.sessions.map (fun p =>
      let sid : SessionId := p.fst
      (sid, Json.mkObj
        [ ("schema_version", Json.str "lean_bridge.v1")
        , ("sid", Json.num sid)
        , ("terminal", Json.bool (sessionTerminal st sid)) ]))).toArray.qsort
        (fun left right => left.1 < right.1)).map Prod.snd

def blockReasonTag : BlockReason UnitGuard → String
  | .recvWait _ _ => "recv_wait"
  | .sendWait _ => "send_wait"
  | .acquireDenied _ => "acquire_denied"
  | .invokeWait _ => "invoke_wait"
  | .consensusWait _ => "consensus_wait"
  | .spawnWait => "spawn_wait"
  | .closeWait _ => "close_wait"
  | .operationAwait _ => "operation_await"

def blockedStateJson (sched : SchedState UnitGuard) : Json :=
  Json.mkObj <|
    sched.blockedSet.toList.map (fun p =>
      (toString p.1, Json.str (blockReasonTag p.2)))

def readyQueueJson (sched : SchedState UnitGuard) : Json :=
  Json.arr <| sched.readyQueue.map Json.num |>.toArray

def selectedEndpointTypeJson (selectedType : Option LocalType) : Json :=
  match selectedType with
  | some ty => Json.str (reprStr ty)
  | none => Json.null

def concreteCoroutineSliceJson
    (coro : Runtime.Proofs.ConcreteCoroutineSlice) : Json :=
  Json.mkObj
    [ ("coro_id", Json.num coro.coroId)
    , ("session_id", Json.num coro.sessionId)
    , ("pc", Json.num coro.pc)
    , ("status", Json.str coro.statusTag)
    , ("owned_endpoints", Json.num coro.ownedEndpointCount)
    , ("progress_tokens", Json.num coro.progressTokenCount) ]

def concreteSessionSliceJson
    (sess : Runtime.Proofs.ConcreteSessionSlice) : Json :=
  Json.mkObj
    [ ("sid", Json.num sess.sid)
    , ("role_count", Json.num sess.roleCount)
    , ("local_type_entries", Json.num sess.localTypeCount)
    , ("buffer_edges", Json.num sess.bufferEdgeCount)
    , ("buffered_messages", Json.num sess.bufferedMessageCount)
    , ("status", Json.str sess.statusTag)
    , ("epoch", Json.num sess.epoch) ]

def concreteSchedulerSliceJson
    (sched : Runtime.Proofs.ConcreteSchedulerSlice) : Json :=
  Json.mkObj
    [ ("ready_queue", Json.arr <| sched.readyQueue.map Json.num |>.toArray)
    , ("blocked", Json.mkObj <| sched.blocked.map (fun p => (toString p.1, Json.str p.2)))
    , ("step_count", Json.num sched.stepCount) ]

def concreteProtocolMachineSliceJson
    (slice : Runtime.Proofs.ConcreteProtocolMachineSlice) : Json :=
  Json.mkObj
    [ ("coroutines", Json.arr <| slice.coroutines.map concreteCoroutineSliceJson |>.toArray)
    , ("sessions", Json.arr <| slice.sessions.map concreteSessionSliceJson |>.toArray)
    , ("scheduler", concreteSchedulerSliceJson slice.scheduler) ]

def concreteTraceEventJson
    (ev : Runtime.Proofs.ConcreteTraceEvent) : Json :=
  let fields :=
    [ ("schema_version", Json.str "lean_bridge.v1")
    , ("kind", Json.str ev.kind)
    , ("tick", Json.num ev.tick) ] ++
    (match ev.session with
    | some sid => [("session", Json.num sid)]
    | none => []) ++
    (match ev.sender with
    | some sender => [("sender", Json.str sender)]
    | none => []) ++
    (match ev.receiver with
    | some receiver => [("receiver", Json.str receiver)]
    | none => []) ++
    (match ev.label with
    | some label => [("label", Json.str label)]
    | none => []) ++
    (match ev.role with
    | some role => [("role", Json.str role)]
    | none => []) ++
    (match ev.target with
    | some target => [("target", Json.str target)]
    | none => []) ++
    (match ev.reason with
    | some reason => [("reason", Json.str reason)]
    | none => [])
  Json.mkObj fields

def concreteScheduledStepJson
    (stepIndex : Nat)
    (step : Runtime.Proofs.ConcreteScheduledStep) : Json :=
  let transition := step.transition
  Json.mkObj
    [ ("step_index", Json.num stepIndex)
    , ("pre_state", concreteProtocolMachineSliceJson step.preState)
    , ("post_state", concreteProtocolMachineSliceJson step.postState)
    , ("selected_coro", Json.num transition.selectedCoro)
    , ("selected_pc", Json.num transition.selectedPc)
    , ("selected_type", selectedEndpointTypeJson transition.selectedType)
    , ("exec_status", Json.str transition.execStatusTag)
    , ("session_type_counts", natAssocJson transition.sessionTypeCounts)
    , ("buffered_message_counts", natAssocJson transition.bufferedMessageCounts)
    , ("ready_queue", Json.arr <| transition.readyQueue.map Json.num |>.toArray)
    , ("blocked", Json.mkObj <| transition.blocked.map (fun p => (toString p.1, Json.str p.2)))
    , ("event", step.event.map concreteTraceEventJson |>.getD Json.null) ]

def syntheticLifecycleEvents (stepStates : List Json) : List Json :=
  stepStates.foldl
    (fun acc stepJson =>
      match stepJson.getObjVal? "event" with
      | .ok eventJson =>
          match eventJson.getObjValAs? String "kind" with
          | .ok "halted" => acc ++ [eventJson]
          | .ok "faulted" => acc ++ [eventJson]
          | _ => acc
      | .error _ => acc)
    []

def runWithStepStatesAux (fuel : Nat) (st : RunnerState)
    (stepIndex : Nat) (acc : List Json) : RunnerState × List Json :=
  match fuel with
  | 0 => (st, acc.reverse)
  | fuel' + 1 =>
      let st' := { st with clock := st.clock + 1 }
      let st'' := tryUnblockReceivers st'
      match hSched : schedule st'' with
      | none => (st'', acc.reverse)
      | some (cid, stSched) =>
          let (stExec, res) := execInstr stSched cid
          let sched' := updateAfterStep stExec.sched cid res.status
          let stNext : RunnerState := { stExec with sched := sched' }
          let projectedStep :=
            match hProjected : Runtime.Proofs.projectConcreteScheduledStep? st'' with
            | some step => step
            | none =>
                False.elim <| by
                  have hNoSchedule :=
                    (Runtime.Proofs.project_concrete_scheduled_step_none_iff (st := st'')).mp
                      hProjected
                  simp [hSched] at hNoSchedule
          let stepJson := concreteScheduledStepJson stepIndex projectedStep
          let acc' := stepJson :: acc
          if allTerminal stNext then
            (stNext, acc'.reverse)
          else
            runWithStepStatesAux fuel' stNext (stepIndex + 1) acc'

def runWithStepStates (fuel : Nat) (_concurrency : Nat)
    (st : RunnerState) : RunnerState × List Json :=
  runWithStepStatesAux fuel st 0 []
