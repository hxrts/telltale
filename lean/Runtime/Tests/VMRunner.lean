import Lean.Data.Json
import Runtime.VM.UnitModel
import Runtime.VM.Json
import Runtime.VM.LoadChoreography
import Runtime.VM.RunScheduled
import Runtime.Monitor.Monitor
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

  -- Run the VM.
  let st' := runScheduled maxSteps concurrency st

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
    , ("sessions", sessionsJson)
    , ("steps_executed", Json.num st'.sched.stepCount)
    , ("concurrency", Json.num concurrency)
    , ("status", Json.str status) ]
  IO.println out.compress
