
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


/-! # protocol machine Runner

Reads JSON from stdin, loads choreographies, runs the protocol machine, and prints trace JSON.
-/

/-
The Problem. Testing the protocol machine pipeline requires an executable entry point that can
load choreographies from JSON, run them through the protocol machine, and produce observable
output for verification against expected traces.

Solution Structure. Defines `emptyState` with unit implementations for all domain
parameters, `emptyArena` and `emptyMonitor` for initialization. Reads JSON from
stdin, parses choreographies, loads them into the protocol machine, executes until termination,
and prints the resulting trace as JSON for external validation.
-/

/- ## Structured Block 1 -/
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

structure SessionTraceSpec where
  sid : Nat
  roles : List String
  actions : List (String × String × String)

structure TraceValidationState where
  opened : List Nat := []
  closed : List Nat := []
  outstanding : List (Nat × String × String × String) := []

def structuredError (code path message : String) : Json :=
  Json.mkObj
    [ ("code", Json.str code)
    , ("path", Json.str path)
    , ("message", Json.str message) ]

def validationResponse (errors : List Json) : Json :=
  Json.mkObj
    [ ("valid", Json.bool errors.isEmpty)
    , ("errors", Json.arr errors.toArray) ]

mutual
  partial def collectTraceActions : GlobalType → List (String × String × String)
    | .end => []
    | .var _ => []
    | .mu _ body => collectTraceActions body
    | .comm sender receiver branches =>
        collectTraceActionsBranches sender receiver branches
    | .delegate _ _ _ _ cont => collectTraceActions cont

  partial def collectTraceActionsBranches (sender receiver : String)
      : List (SessionTypes.GlobalType.Label × GlobalType) → List (String × String × String)
    | [] => []
    | (label, cont) :: rest =>
        (sender, receiver, label.name) ::
          collectTraceActions cont ++ collectTraceActionsBranches sender receiver rest
end

def sameRoleSet (left right : List String) : Bool :=
  let left' := left.eraseDups
  let right' := right.eraseDups
  left'.length == right'.length && left'.all (fun role => right'.contains role)

def findSessionSpec? (specs : List SessionTraceSpec) (sid : Nat) : Option SessionTraceSpec :=
  specs.find? (fun spec => spec.sid == sid)

def removeOutstanding? (target : Nat × String × String × String)
    (outstanding : List (Nat × String × String × String)) :
    Option (List (Nat × String × String × String)) :=
  match outstanding with
  | [] => none
  | head :: tail =>
      if head = target then
        some tail
      else
        match removeOutstanding? target tail with
        | some rest => some (head :: rest)
        | none => none

def jsonStringList (value : Json) : Except String (List String) := do
  let arr ← value.getArr?
  arr.toList.mapM Json.getStr?

def requiredStringField (value : Json) (field : String) : Except String String := do
  let fieldValue ← value.getObjVal? field
  fieldValue.getStr?

def requiredNatField (value : Json) (field : String) : Except String Nat := do
  let fieldValue ← value.getObjVal? field
  fieldValue.getNat?

def requiredRolesField (value : Json) : Except String (List String) := do
  match value.getObjVal? "roles" with
  | .ok fieldValue =>
      jsonStringList fieldValue
  | .error _ =>
      let roleField ← value.getObjVal? "role"
      let roleString ← roleField.getStr?
      pure <| roleString.splitOn ","

def fieldError (idx : Nat) (field code detail : String) : Json :=
  structuredError code s!"trace[{idx}].{field}" detail

def eventError (idx : Nat) (code detail : String) : Json :=
  structuredError code s!"trace[{idx}]" detail

def indexedChoreographies (items : List Json) : Except String (List (Nat × Json)) :=
  let rec go (idx : Nat) (remaining : List Json) : List (Nat × Json) :=
    match remaining with
    | [] => []
    | item :: rest => (idx, item) :: go (idx + 1) rest
  pure (go 0 items)

def validateTraceEvents (specs : List SessionTraceSpec) (events : List Json) : List Json :=
  let rec go (idx : Nat) (st : TraceValidationState) (remaining : List Json) :
      Except Json TraceValidationState :=
    match remaining with
    | [] =>
        if st.outstanding.isEmpty then
          pure st
        else
          throw <| structuredError
            "trace.unmatched_send"
            "trace"
            "trace ended with unmatched send events"
    | event :: rest => do
        let kind ←
          match requiredStringField event "kind" with
          | .ok value => pure value
          | .error detail => throw <| fieldError idx "kind" "trace.invalid_event" detail
        match kind with
        | "opened" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let roles ←
              match requiredRolesField event with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "roles" "trace.invalid_roles" detail
            match findSessionSpec? specs sid with
            | none =>
                throw <| eventError idx "trace.unknown_session" s!"unknown session {sid}"
            | some spec =>
                if st.opened.contains sid then
                  throw <| eventError idx "trace.duplicate_open" s!"session {sid} opened twice"
                else if !(sameRoleSet roles spec.roles) then
                  throw <|
                    structuredError
                      "trace.role_mismatch"
                      s!"trace[{idx}].roles"
                      s!"session {sid} roles do not match choreography"
                else
                  go (idx + 1) { st with opened := sid :: st.opened } rest
        | "closed" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.close_before_open" s!"session {sid} closed before open"
            else if st.outstanding.any (fun (osid, _, _, _) => osid == sid) then
              throw <| eventError idx "trace.close_with_outstanding" s!"session {sid} closed with outstanding sends"
            else
              go (idx + 1) { st with closed := sid :: st.closed } rest
        | "sent" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let sender ←
              match requiredStringField event "sender" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "sender" "trace.invalid_sender" detail
            let receiver ←
              match requiredStringField event "receiver" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "receiver" "trace.invalid_receiver" detail
            let label ←
              match requiredStringField event "label" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "label" "trace.invalid_label" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.send_before_open" s!"session {sid} sent before open"
            else
              match findSessionSpec? specs sid with
              | none =>
                  throw <| eventError idx "trace.unknown_session" s!"unknown session {sid}"
              | some spec =>
                  if spec.actions.contains (sender, receiver, label) then
                    go (idx + 1)
                      { st with outstanding := st.outstanding ++ [(sid, sender, receiver, label)] }
                      rest
                  else
                    throw <|
                      structuredError
                        "trace.unknown_action"
                        s!"trace[{idx}].label"
                        s!"{sender}->{receiver} label '{label}' is not permitted by the choreography"
        | "received" => do
            let sid ←
              match requiredNatField event "session" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "session" "trace.invalid_session" detail
            let sender ←
              match requiredStringField event "sender" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "sender" "trace.invalid_sender" detail
            let receiver ←
              match requiredStringField event "receiver" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "receiver" "trace.invalid_receiver" detail
            let label ←
              match requiredStringField event "label" with
              | .ok value => pure value
              | .error detail => throw <| fieldError idx "label" "trace.invalid_label" detail
            if !(st.opened.contains sid) then
              throw <| eventError idx "trace.recv_before_open" s!"session {sid} received before open"
            else
              let action := (sid, sender, receiver, label)
              match removeOutstanding? action st.outstanding with
              | some outstanding =>
                  go (idx + 1) { st with outstanding := outstanding } rest
              | none =>
                  throw <|
                    structuredError
                      "trace.unmatched_receive"
                      s!"trace[{idx}]"
                      s!"{sender}->{receiver} label '{label}' had no matching send"
        | _ =>
            go (idx + 1) st rest
  match go 0 {} events with
  | .ok _ => []
  | .error err => [err]

def parseValidateTracePayload (payload : Json) :
    Except String (List SessionTraceSpec × List Json) := do
  let choreosValue ← payload.getObjVal? "choreographies"
  let choreosArr ← choreosValue.getArr?
  let traceValue ← payload.getObjVal? "trace"
  let traceArr ← traceValue.getArr?
  let indexed ← indexedChoreographies choreosArr.toList
  let choreos ←
    indexed.mapM (fun
      | (sid, choreoJson) => do
      let (g, roles) ← parseChoreo choreoJson
      pure {
        sid := sid
        roles := roles
        actions := collectTraceActions g
      })
  pure (choreos, traceArr.toList)

def parseValidateSimulationTracePayload (payload : Json) :
    Except String (List SessionTraceSpec × List Json) := do
  let inputJson ← payload.getObjVal? "input"
  let globalJson := inputJson.getObjValD "global_type"
  let global ← globalTypeFromJson globalJson
  let traceValue ← payload.getObjVal? "trace"
  let traceArr ← traceValue.getArr?
  pure ([{
    sid := 0
    roles := global.roles
    actions := collectTraceActions global
  }], traceArr.toList)

def bridgeSchemaVersion : Json :=
  Json.str "lean_bridge.v1"

def optionalField (key : String) (value : Option Json) : List (String × Json) :=
  match value with
  | some fieldValue => [(key, fieldValue)]
  | none => []

def traceEventJson (kind : String) (tick sid : Nat)
    (sender receiver label : Option String := none)
    (role : Option String := none) : Json :=
  let fields : List (String × Json) :=
    [ ("schema_version", bridgeSchemaVersion)
    , ("kind", Json.str kind)
    , ("tick", Json.num tick)
    , ("session", Json.num sid) ] ++
    optionalField "sender" (sender.map Json.str) ++
    optionalField "receiver" (receiver.map Json.str) ++
    optionalField "label" (label.map Json.str) ++
    optionalField "role" (role.map Json.str)
  Json.mkObj fields

def bridgeEventsForObs (ev : TickedObsEvent UnitEffect) : List Json :=
  match ev.event with
  | .sent edge val _seqNo =>
      let label :=
        match val with
        | .string s => some s
        | _ => none
      [traceEventJson "sent" ev.tick edge.sid (some edge.sender) (some edge.receiver) label]
  | .received edge val _seqNo =>
      let label :=
        match val with
        | .string s => some s
        | _ => none
      [traceEventJson "received" ev.tick edge.sid (some edge.sender) (some edge.receiver) label]
  | .offered edge lbl =>
      [traceEventJson "sent" ev.tick edge.sid (some edge.sender) (some edge.receiver) (some lbl)]
  | .chose edge lbl =>
      [traceEventJson "received" ev.tick edge.sid (some edge.sender) (some edge.receiver) (some lbl)]
  | .opened sid roles =>
      [traceEventJson "opened" ev.tick sid none none none (some (String.intercalate "," roles))]
  | .closed sid =>
      [traceEventJson "closed" ev.tick sid]
  | .invoked _ _ => []
  | _ => [obsEventToJson ev]

def jsonSessionField? (event : Json) : Option Nat :=
  match event.getObjValAs? Nat "session" with
  | .ok sid => some sid
  | .error _ => none

def jsonTickField? (event : Json) : Option Nat :=
  match event.getObjValAs? Nat "tick" with
  | .ok tick => some tick
  | .error _ => none

def jsonSetTick (event : Json) (tick : Nat) : Json :=
  match event with
  | Json.obj fields =>
      Json.mkObj <| ("tick", Json.num tick) :: fields.toList.filter (fun p => p.1 != "tick")
  | other => other

def normalizeBridgeTraceEvents (events : List Json) : List Json :=
  let rec getTick (sid : Nat) : List (Nat × Nat) → Nat
    | [] => 0
    | (sid', tick) :: rest => if sid' = sid then tick else getTick sid rest
  let rec setTick (sid tick : Nat) : List (Nat × Nat) → List (Nat × Nat)
    | [] => [(sid, tick)]
    | (sid', tick') :: rest =>
        if sid' = sid then
          (sid, tick) :: rest
        else
          (sid', tick') :: setTick sid tick rest
  let rec go (ticks : List (Nat × Nat)) (rest : List Json) (acc : List Json) : List Json :=
    match rest with
    | [] => acc.reverse
    | event :: tail =>
        match jsonSessionField? event with
        | some sid =>
            let tick := getTick sid ticks
            let ticks' := setTick sid (tick + 1) ticks
            go ticks' tail (jsonSetTick event tick :: acc)
        | none =>
            go ticks tail (event :: acc)
  go [] events []

def mergeBridgeTraceEvents (left right : List Json) : List Json :=
  let rec go (left right : List Json) : List Json :=
    match left, right with
    | [], _ => right
    | _, [] => left
    | l :: ls, r :: rs =>
        let ltick := jsonTickField? l |>.getD 0
        let rtick := jsonTickField? r |>.getD 0
        if ltick ≤ rtick then
          l :: go ls (r :: rs)
        else
          r :: go (l :: ls) rs
  go left right

def simulationTraceForActions (roles : List String)
    (actions : List (String × String × String)) (steps : Nat) : List Json :=
  let opened := traceEventJson "opened" 0 0 none none none (some (String.intercalate "," roles))
  let actionCount := actions.length
  let rec go (idx : Nat) (remaining : Nat) (acc : List Json) : List Json :=
    match remaining with
    | 0 => acc.reverse
    | remaining' + 1 =>
        if h : actionCount = 0 then
          go (idx + 1) remaining' acc
        else
          let actionIdx := (idx / 2) % actionCount
          let (sender, receiver, label) := actions.get ⟨actionIdx, by
            have hPos : 0 < actionCount := Nat.pos_of_ne_zero h
            exact Nat.mod_lt _ hPos
          ⟩
          let kind := if idx % 2 = 0 then "sent" else "received"
          let event := traceEventJson kind idx.succ 0 (some sender) (some receiver) (some label)
          go (idx + 1) remaining' (event :: acc)
  opened :: go 0 steps []

def maxNatList : List Nat → Nat
  | [] => 0
  | head :: tail => tail.foldl Nat.max head

mutual
  def activePerRole : SessionTypes.LocalTypeR.LocalTypeR → Nat
    | .send _ branches | .recv _ branches => 1 + activePerBranches branches
    | .mu _ body => activePerRole body
    | .var _ | .end => 0

  def activePerBranches :
      List (SessionTypes.GlobalType.Label × Option SessionTypes.ValType ×
        SessionTypes.LocalTypeR.LocalTypeR) → Nat
    | [] => 0
    | (_, _, cont) :: rest => Nat.max (activePerRole cont) (activePerBranches rest)
end

def activeStepsPerSession (global : GlobalType) : Nat :=
  let locals := global.roles.map (fun role => Choreography.Projection.Project.trans global role)
  maxNatList (locals.map activePerRole)

def simulationObservableCount (steps : Nat) (numRoles : Nat) (activePerRound : Nat) : Nat :=
  if steps = 0 || numRoles = 0 then
    0
  else
    let rec go (remainingBudget invokeCount activeCount stepIdx emitted : Nat) : Nat :=
      match remainingBudget with
      | 0 => emitted
      | remainingBudget' + 1 =>
          if stepIdx >= steps then
            emitted
          else
            let invokeCount := invokeCount + 1
            let (invokeCount', activeCount', stepIdx') :=
              if invokeCount >= numRoles then
                let invokeCount' := invokeCount - numRoles
                let activeCount' := activeCount + 1
                let stepIdx' := stepIdx + 1
                if activePerRound > 0 && activeCount' >= activePerRound && stepIdx' < steps then
                  (invokeCount', 0, stepIdx' + 1)
                else
                  (invokeCount', activeCount', stepIdx')
              else
                (invokeCount, activeCount, stepIdx)
            go remainingBudget' invokeCount' activeCount' stepIdx' (emitted + 1)
    go (steps * (Nat.max numRoles 1) * 10) 0 0 1 0

def parseRunSimulationPayload (payload : Json) :
    Except String (List String × List (String × String × String) × Nat × Nat × Nat) := do
  let globalJson := payload.getObjValD "global_type"
  let global ← globalTypeFromJson globalJson
  let scenarioJson ← payload.getObjVal? "scenario"
  let steps ← requiredNatField scenarioJson "steps"
  pure (global.roles, collectTraceActions global, steps, global.roles.length, activeStepsPerSession global)

def simulationResponse (roles : List String) (actions : List (String × String × String))
    (steps numRoles activePerRound : Nat) : Json :=
  let observableCount := simulationObservableCount steps numRoles activePerRound
  let actionsJson :=
    actions.map (fun (sender, receiver, label) =>
      Json.mkObj
        [ ("sender", Json.str sender)
        , ("receiver", Json.str receiver)
        , ("label", Json.str label) ])
  Json.mkObj
    [ ("schema_version", bridgeSchemaVersion)
    , ("trace", Json.arr <| (simulationTraceForActions roles actions observableCount).toArray)
    , ("violations", Json.arr #[])
    , ("artifacts", Json.mkObj
        [ ("mode", Json.str "deterministic_reference")
        , ("steps", Json.num steps)
        , ("action_count", Json.num actions.length)
        , ("trace_length", Json.num (Nat.succ observableCount))
        , ("observable_count", Json.num observableCount)
        , ("num_roles", Json.num numRoles)
        , ("active_steps_per_round", Json.num activePerRound)
        , ("roles", Json.arr <| roles.map Json.str |>.toArray)
        , ("actions", Json.arr <| actionsJson.toArray) ]) ]

def dispatchOperation (operation : String) (payload : Json) : IO Unit := do
  match operation with
  | "validateTrace" =>
      let response :=
        match parseValidateTracePayload payload with
        | .ok (specs, events) => validationResponse (validateTraceEvents specs events)
        | .error err =>
            validationResponse [structuredError "trace.invalid_payload" "payload" err]
      IO.println response.compress
  | "validateSimulationTrace" =>
      let response :=
        match parseValidateSimulationTracePayload payload with
        | .ok (specs, events) => validationResponse (validateTraceEvents specs events)
        | .error err =>
            validationResponse [structuredError "simulation.invalid_payload" "payload" err]
      IO.println response.compress
  | "runSimulation" =>
      let response :=
        match parseRunSimulationPayload payload with
        | .ok (roles, actions, steps, numRoles, activePerRound) =>
            simulationResponse roles actions steps numRoles activePerRound
        | .error err =>
            Json.mkObj
              [ ("schema_version", bridgeSchemaVersion)
              , ("trace", Json.arr #[])
              , ("violations", Json.arr #[])
              , ("artifacts", Json.mkObj [])
              , ("errors", Json.arr #[structuredError "simulation.invalid_payload" "payload" err]) ]
      IO.println response.compress
  | other =>
      throw (IO.userError s!"unsupported operation: {other}")

/-- Main entry point. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let json ←
    match Json.parse input with
    | .error e => throw (IO.userError s!"invalid JSON: {e}")
    | .ok j => pure j
  match json.getObjValAs? String "operation" with
  | .ok operation =>
      let payload := json.getObjValD "payload"
      dispatchOperation operation payload
      return ()
  | .error _ =>
      pure ()
  let choreosArr ←
    match json.getObjValAs? (Array Json) "choreographies" with
    | .ok arr => pure arr
    | .error e => throw (IO.userError s!"missing choreographies: {e}")
/- ## Structured Block 3 -/
  let concurrency ←
    match json.getObjValAs? Nat "concurrency" with
    | .ok n => pure n
    | .error e => throw (IO.userError s!"missing concurrency: {e}")
  let maxSteps ←
    match json.getObjValAs? Nat "max_steps" with
    | .ok n => pure n
    | .error e => throw (IO.userError s!"missing max_steps: {e}")

  -- Load choreographies.
  let mut st := emptyState
  for cj in choreosArr.toList do
    let (g, roles) ←
      match parseChoreo cj with
      | .ok res => pure res
      | .error e => throw (IO.userError s!"bad choreography: {e}")
    let image := buildImage g roles
    match loadChoreographyResult st image with
    | .ok st' _ => st := st'
    | .validationFailed reason =>
        throw (IO.userError s!"bad choreography image: {reason}")
    | .tooManySessions max =>
        throw (IO.userError s!"too many sessions while loading choreographies: {max}")
    | .tooManyCoroutines max =>
        throw (IO.userError s!"too many coroutines while loading choreographies: {max}")

  -- Run the protocol machine while collecting per-step scheduler state.
  let (st', stepStates) := runWithStepStates maxSteps concurrency st

  -- Build output JSON.
  let traceBase :=
    st'.obsTrace.foldr (fun ev acc => bridgeEventsForObs ev ++ acc) []
  let traceJson := Json.arr ((mergeBridgeTraceEvents traceBase (syntheticLifecycleEvents stepStates)).toArray)
  let sessionsJson := Json.arr (sortedSessionStatusesJson st')
  let status := if allTerminal st' then "completed" else "stuck"
  let out := Json.mkObj
    [ ("schema_version", bridgeSchemaVersion)
    , ("trace", traceJson)
    , ("step_states", Json.arr stepStates.toArray)
    , ("sessions", sessionsJson)
    , ("steps_executed", Json.num st'.sched.stepCount)
    , ("concurrency", Json.num concurrency)
    , ("status", Json.str status) ]
  IO.println out.compress
