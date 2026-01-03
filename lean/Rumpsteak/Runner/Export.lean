import Lean.Data.Json
import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Runner.Json

/-! # Rumpsteak.Runner.Export

Export Lean types to JSON for Rust equivalence testing.

## Overview

This module provides functions to serialize LocalTypeR, GlobalType, and
projection results to JSON format matching the Rust lean-bridge format.

This enables true equivalence testing: Lean computes a value, exports it
to JSON, and Rust can compare its own computation against Lean's result.

## JSON Format

LocalTypeR:
- `end` → `{"kind": "end"}`
- `send p branches` → `{"kind": "send", "partner": p, "branches": [...]}`
- `recv p branches` → `{"kind": "recv", "partner": p, "branches": [...]}`
- `mu t body` → `{"kind": "rec", "var": t, "body": {...}}`
- `var t` → `{"kind": "var", "name": t}`

GlobalType:
- `end` → `{"kind": "end"}`
- `comm s r branches` → `{"kind": "comm", "sender": s, "receiver": r, "branches": [...]}`
- `mu t body` → `{"kind": "rec", "var": t, "body": {...}}`
- `var t` → `{"kind": "var", "name": t}`
-/

namespace Rumpsteak.Runner.Export

open Lean
open Rumpsteak.Protocol.GlobalType (GlobalType Label PayloadSort)
open Rumpsteak.Protocol.LocalTypeR (LocalTypeR)
open Rumpsteak.Protocol.ProjectionR (ProjectionError ProjectionResult projectR projectAllR)
open Rumpsteak.Runner.Json

/-! ## Payload Sort Export -/

/-- Export a PayloadSort to JSON. -/
def sortToJson : PayloadSort → Json
  | .unit => Json.str "unit"
  | .nat => Json.str "nat"
  | .bool => Json.str "bool"
  | .string => Json.str "string"
  | .prod left right =>
      Json.mkObj [("prod", Json.arr #[sortToJson left, sortToJson right])]

/-! ## Label Export -/

/-- Export a Label to JSON. -/
def labelToJson (l : Label) : Json :=
  Json.mkObj [
    ("name", Json.str l.name),
    ("sort", sortToJson l.sort)
  ]

/-! ## LocalTypeR Export -/

/-- Export a LocalTypeR to JSON matching the Rust lean-bridge format. -/
partial def localTypeRToJson : LocalTypeR → Json
  | .end => Json.mkObj [("kind", Json.str "end")]

  | .send partner branches =>
      let branchesJson := branches.map fun (label, cont) =>
        Json.mkObj [
          ("label", labelToJson label),
          ("continuation", localTypeRToJson cont)
        ]
      Json.mkObj [
        ("kind", Json.str "send"),
        ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)
      ]

  | .recv partner branches =>
      let branchesJson := branches.map fun (label, cont) =>
        Json.mkObj [
          ("label", labelToJson label),
          ("continuation", localTypeRToJson cont)
        ]
      Json.mkObj [
        ("kind", Json.str "recv"),
        ("partner", Json.str partner),
        ("branches", Json.arr branchesJson.toArray)
      ]

  | .mu var body =>
      Json.mkObj [
        ("kind", Json.str "rec"),
        ("var", Json.str var),
        ("body", localTypeRToJson body)
      ]

  | .var name =>
      Json.mkObj [
        ("kind", Json.str "var"),
        ("name", Json.str name)
      ]

/-! ## GlobalType Export -/

/-- Export a GlobalType to JSON matching the Rust lean-bridge format. -/
partial def globalTypeToJson : GlobalType → Json
  | .end => Json.mkObj [("kind", Json.str "end")]

  | .comm sender receiver branches =>
      let branchesJson := branches.map fun (label, cont) =>
        Json.mkObj [
          ("label", labelToJson label),
          ("continuation", globalTypeToJson cont)
        ]
      Json.mkObj [
        ("kind", Json.str "comm"),
        ("sender", Json.str sender),
        ("receiver", Json.str receiver),
        ("branches", Json.arr branchesJson.toArray)
      ]

  | .mu var body =>
      Json.mkObj [
        ("kind", Json.str "rec"),
        ("var", Json.str var),
        ("body", globalTypeToJson body)
      ]

  | .var name =>
      Json.mkObj [
        ("kind", Json.str "var"),
        ("name", Json.str name)
      ]

/-! ## Projection Error Export -/

/-- Export a ProjectionError to JSON. -/
def projectionErrorToJson : ProjectionError → Json
  | .mergeFailed lt1 lt2 =>
      Json.mkObj [
        ("error", Json.str "merge_failed"),
        ("type1", localTypeRToJson lt1),
        ("type2", localTypeRToJson lt2)
      ]
  | .emptyBranches =>
      Json.mkObj [("error", Json.str "empty_branches")]
  | .unboundVariable v =>
      Json.mkObj [
        ("error", Json.str "unbound_variable"),
        ("variable", Json.str v)
      ]

/-! ## Projection Result Export -/

/-- Export a projection result (LocalTypeR or error) to JSON. -/
def projectionResultToJson : ProjectionResult → Json
  | .ok lt =>
      Json.mkObj [
        ("success", Json.bool true),
        ("result", localTypeRToJson lt)
      ]
  | .error err =>
      Json.mkObj [
        ("success", Json.bool false),
        ("error", projectionErrorToJson err)
      ]

/-- Export all projections for a global type to JSON. -/
def projectAllToJson (g : GlobalType) : Json :=
  match projectAllR g with
  | .ok projections =>
      let projectionsJson := projections.map fun (role, lt) =>
        Json.mkObj [
          ("role", Json.str role),
          ("localType", localTypeRToJson lt)
        ]
      Json.mkObj [
        ("success", Json.bool true),
        ("projections", Json.arr projectionsJson.toArray)
      ]
  | .error err =>
      Json.mkObj [
        ("success", Json.bool false),
        ("error", projectionErrorToJson err)
      ]

/-! ## Coherence Bundle Export -/

/-- Export a coherence check result to JSON.
    Note: Some coherence fields require proofs and are computed approximately. -/
def coherenceToJson (g : GlobalType)
    (linear size action uniqLabels projectable good : Bool) : Json :=
  Json.mkObj [
    ("linear", Json.bool linear),
    ("size", Json.bool size),
    ("action", Json.bool action),
    ("uniqLabels", Json.bool uniqLabels),
    ("projectable", Json.bool projectable),
    ("good", Json.bool good),
    ("isCoherent", Json.bool (linear && size && action && uniqLabels && projectable && good))
  ]

/-! ## File Output Helpers -/

/-- Write JSON to a file. -/
def writeJsonFile (path : System.FilePath) (json : Json) : IO Unit := do
  IO.FS.writeFile path (json.pretty 2)

/-- Export a GlobalType to a JSON file. -/
def exportGlobalType (g : GlobalType) (path : System.FilePath) : IO Unit :=
  writeJsonFile path (globalTypeToJson g)

/-- Export a projection result for a specific role to a JSON file. -/
def exportProjection (g : GlobalType) (role : String) (path : System.FilePath) : IO Unit :=
  writeJsonFile path (projectionResultToJson (projectR g role))

/-- Export all projections for a global type to a JSON file. -/
def exportAllProjections (g : GlobalType) (path : System.FilePath) : IO Unit :=
  writeJsonFile path (projectAllToJson g)

end Rumpsteak.Runner.Export
