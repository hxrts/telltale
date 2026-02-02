import Lean.Data.Json
import Choreography.Projection.Json
import Choreography.Projection.Trans

/-
The Problem. Provide a command-line executable that reads a GlobalType and role
list from JSON on stdin, projects each role using `trans`, and writes LocalTypeR
results as JSON to stdout. This bridges the Lean verification environment to the
Rust simulation pipeline via the lean-bridge JSON schema.

Solution Structure. Parse input JSON with fields "global_type" and "roles",
call `trans` for each role, emit a JSON object mapping role names to local types.
-/

/-! # Choreography.Projection.Runner

Command-line projection executable. Reads GlobalType + roles from stdin JSON,
projects via `trans`, writes LocalTypeR results as JSON to stdout.

## Input format

```json
{
  "global_type": { "kind": "comm", ... },
  "roles": ["A", "B"]
}
```

## Output format

```json
{
  "projections": {
    "A": { "kind": "send", ... },
    "B": { "kind": "recv", ... }
  }
}
```
-/

open Lean (Json)
open Choreography.Projection.Trans
open Choreography.Projection.Json

/-- Project a GlobalType for each role and produce output JSON. -/
def projectAll (gt : SessionTypes.GlobalType.GlobalType) (roles : List String) : Json :=
  -- Build a JSON object mapping each role name to its projected local type.
  let projections := roles.map fun role =>
    let localType := trans gt role
    (role, localTypeRToJson localType)
  Json.mkObj [("projections", Json.mkObj projections)]

/-- Parse input, project, and produce output. -/
def runProjection (input : String) : Except String String := do
  let json ← Json.parse input
  let gt ← globalTypeFromJson (json.getObjValD "global_type")
  let rolesArr ← json.getObjValAs? (Array String) "roles"
  let result := projectAll gt rolesArr.toList
  .ok (result.pretty)

/-- Main entry point: read stdin, project, write stdout. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match runProjection input with
  | .ok output => IO.println output
  | .error err => do
      IO.eprintln s!"projection error: {err}"
      IO.Process.exit 1
