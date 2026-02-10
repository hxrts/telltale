import Lean.Data.Json
import Runtime.VM.Model.UnitModel
import Runtime.VM.Runtime.Json
import Runtime.VM.Runtime.Loader
import Runtime.VM.Runtime.Runner
import Runtime.VM.Runtime.Scheduler
import Runtime.VM.Runtime.Monitor
import Runtime.VM.Semantics.Exec
import Choreography.Projection.Json
import Choreography.Projection.Trans

/-!
# VM Runner

Reads JSON from stdin, loads choreographies, runs the VM, and prints trace JSON.
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

/-- Empty VM state for loading choreographies. -/
def emptyState : VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify :=
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
  , resourceStates := []
  , guardResources := []
  , sched := { policy := unitConfig.schedPolicy, readyQueue := [], blockedSet := [], timeslice := 1, stepCount := 0 }
  , monitor := emptyMonitor
  , obsTrace := []
  , clock := 0
  , crashedSites := []
  , partitionedEdges := []
  , mask := ()
  , ghostSessions := ()
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
  let locals := roles.map (fun r => (r, Choreography.Projection.Trans.trans g r))
  CodeImage.fromLocalTypes locals g

abbrev RunnerState :=
  VMState UnitIdentity UnitGuard UnitPersist UnitEffect UnitVerify

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
  | .joined => "joined"
  | .aborted => "aborted"

def sessionTypeCounts (sessions : SessionStore UnitVerify) : List (SessionId × Nat) :=
  sessions.map (fun p => (p.fst, p.snd.localTypes.length))

def sessionTypeCountsJson (sessions : SessionStore UnitVerify) : Json :=
  Json.mkObj <| (sessionTypeCounts sessions).map (fun p =>
    (toString p.fst, Json.num p.snd))

def stepEventToJson (tick : Nat) (ev : Option (StepEvent UnitEffect)) : Json :=
  match ev with
  | some (.obs obs) => obsEventToJson { tick := tick, event := obs }
  | _ => Json.null

def runWithStepStatesAux (fuel : Nat) (st : RunnerState)
    (stepIndex : Nat) (acc : List Json) : RunnerState × List Json :=
  match fuel with
  | 0 => (st, acc.reverse)
  | fuel' + 1 =>
      let st' := { st with clock := st.clock + 1 }
      let st'' := tryUnblockReceivers st'
      match schedule st'' with
      | none => (st'', acc.reverse)
      | some (cid, stSched) =>
          let (stExec, res) := execInstr stSched cid
          let sched' := updateAfterStep stExec.sched cid res.status
          let stNext : RunnerState := { stExec with sched := sched' }
          let stepJson :=
            Json.mkObj
              [ ("step_index", Json.num stepIndex)
              , ("selected_coro", Json.num cid)
              , ("exec_status", Json.str (execStatusTag res.status))
              , ("session_type_counts", sessionTypeCountsJson stNext.sessions)
              , ("event", stepEventToJson stNext.clock res.event) ]
          let acc' := stepJson :: acc
          if allTerminal stNext then
            (stNext, acc'.reverse)
          else
            runWithStepStatesAux fuel' stNext (stepIndex + 1) acc'

def runWithStepStates (fuel : Nat) (_concurrency : Nat)
    (st : RunnerState) : RunnerState × List Json :=
  runWithStepStatesAux fuel st 0 []

/-- Main entry point. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let json ←
    match Json.parse input with
    | .error e => throw (IO.userError s!"invalid JSON: {e}")
    | .ok j => pure j
  let choreosArr ←
    match json.getObjValAs? (Array Json) "choreographies" with
    | .ok arr => pure arr
    | .error e => throw (IO.userError s!"missing choreographies: {e}")
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
    let (st', _) := loadChoreography st image
    st := st'

  -- Run the VM while collecting per-step scheduler state.
  let (st', stepStates) := runWithStepStates maxSteps concurrency st

  -- Build output JSON.
  let traceJson := traceToJson st'.obsTrace
  let sessionsJson := Json.arr (st'.sessions.map (fun p =>
    let sid : SessionId := p.fst
    Json.mkObj
      [ ("sid", Json.num sid)
      , ("terminal", Json.bool (sessionTerminal st' sid)) ])
    |>.toArray)
  let status := if allTerminal st' then "completed" else "stuck"
  let out := Json.mkObj
    [ ("trace", traceJson)
    , ("step_states", Json.arr stepStates.toArray)
    , ("sessions", sessionsJson)
    , ("steps_executed", Json.num st'.sched.stepCount)
    , ("concurrency", Json.num concurrency)
    , ("status", Json.str status) ]
  IO.println out.compress
