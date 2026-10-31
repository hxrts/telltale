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
import Runtime.Tests.ProtocolMachineRunner.Core
import Runtime.Tests.ProtocolMachineRunner.TraceValidation


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
  | .sent edge val _seqNo lbl =>
      let label :=
        match lbl, val with
        | some l, _ => some l
        | none, .string s => some s
        | none, _ => none
      [traceEventJson "sent" ev.tick edge.sid (some edge.sender) (some edge.receiver) label]
  | .received edge val _seqNo lbl =>
      let label :=
        match lbl, val with
        | some l, _ => some l
        | none, .string s => some s
        | none, _ => none
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
  | "runNominalImage" =>
      match Runtime.Tests.NominalImageRunner.runNominalImage payload with
      | .ok response => IO.println response.compress
      | .error reason => throw (IO.userError s!"nominal executable image refused: {reason}")
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
