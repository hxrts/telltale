import Lean.Data.Json
import SessionTypes.GlobalType
import SessionTypes.LocalTypeR
import Choreography.Projection.Json
import Choreography.Projection.Project.Primitive

/-! # Choreography.Projection.Validator

CLI validator for Lean projection results.
-/

/-
The Problem. The Rust lean-bridge exports choreography and program JSON files,
but we need Lean-side validation that projection produces the expected local types.
This enables cross-language verification of projection correctness.

Solution Structure. We implement:
1. JSON parsing for choreography and program exports
2. `localTypeREq`: structural equality checker for local types
3. `validate`: compares Lean-computed projection against Rust-exported expectation
4. CLI main function for integration with the verification pipeline
-/

set_option autoImplicit false

/-! ## Core Development -/

namespace Choreography.Projection.Validator

open Lean (Json)
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open Choreography.Projection.Json
open Choreography.Projection.Project

/-! ## Program Parsing -/

/-- Program export payload: role plus expected local type. -/
structure ProgramExport where
  role : String
  localType : LocalTypeR

/-- Parse program export JSON. -/
def parseProgram (j : Json) : Except String ProgramExport := do
  let role ← j.getObjValAs? String "role"
  let localJson := j.getObjValD "local_type"
  let localType ← localTypeRFromJson localJson
  .ok { role := role, localType := localType }

/-! ## Structural Equality -/

mutual
  /-- Structural equality on LocalTypeR. -/
  def localTypeREq : LocalTypeR → LocalTypeR → Bool
    | .end, .end => true
    | .var v1, .var v2 => v1 == v2
    | .mu v1 b1, .mu v2 b2 => (v1 == v2) && localTypeREq b1 b2
    | .send p1 bs1, .send p2 bs2 => (p1 == p2) && branchesEq bs1 bs2
    | .recv p1 bs1, .recv p2 bs2 => (p1 == p2) && branchesEq bs1 bs2
    | _, _ => false

  /-- Structural equality on branch lists. -/
  def branchesEq : List BranchR → List BranchR → Bool
    | [], [] => true
    | b1 :: bs1, b2 :: bs2 => branchEq b1 b2 && branchesEq bs1 bs2
    | _, _ => false

  /-- Structural equality on a single branch. -/
  def branchEq : BranchR → BranchR → Bool
    | (l1, v1, t1), (l2, v2, t2) =>
        decide (l1 = l2) && decide (v1 = v2) && localTypeREq t1 t2
end

/-! ## File and Log Utilities -/

/-- Read and parse a JSON file. -/
def readJsonFile (path : System.FilePath) : IO (Except String Json) := do
  let content ← IO.FS.readFile path
  pure (Json.parse content)

/-- Format a validation log as JSON. -/
def validationJson (role : String) (ok : Bool) (msg : String)
    (expected provided : LocalTypeR) : Json :=
  Json.mkObj
    [ ("role", Json.str role)
    , ("status", Json.str (if ok then "ok" else "fail"))
    , ("message", Json.str msg)
    , ("expected", localTypeRToJson expected)
    , ("provided", localTypeRToJson provided)
    ]

/-- Optional text log sink. -/
def writeLog (path : System.FilePath) (role : String) (ok : Bool) (msg : String) : IO Unit := do
  let status := if ok then "ok" else "fail"
  let line := s!"role={role},status={status},message={msg}"
  IO.FS.writeFile path (line ++ "\n")

/-- Optional JSON log sink. -/
def writeJsonLog (path : System.FilePath) (payload : Json) : IO Unit := do
  IO.FS.writeFile path (payload.pretty ++ "\n")

/-! ## Validation Runner -/

/-- Validate a program export against the projected local type. -/
def runValidation (chPath progPath : System.FilePath)
    (logPath : Option System.FilePath := none)
    (jsonLog : Option System.FilePath := none) : IO UInt32 := do
  let choreoJson ← readJsonFile chPath
  match choreoJson with
  | .error err =>
      IO.eprintln s!"Failed to parse choreography JSON: {err}"
      pure 1
  | .ok choreoDoc =>
      match globalTypeFromJson choreoDoc with
      | .error err =>
          IO.eprintln s!"Failed to decode global type: {err}"
          pure 1
      | .ok global =>
          let programJson ← readJsonFile progPath
          match programJson with
          | .error err =>
              IO.eprintln s!"Failed to parse program JSON: {err}"
              pure 1
          | .ok programDoc =>
              match parseProgram programDoc with
              | .error err =>
                  IO.eprintln s!"Failed to decode program: {err}"
                  pure 1
              | .ok program =>
                  let expected := trans global program.role
                  let ok := localTypeREq expected program.localType
                  let msg := if ok then "ok" else "local type mismatch"
                  let payload := validationJson program.role ok msg expected program.localType
                  match logPath with
                  | some path => writeLog path program.role ok msg
                  | none => pure ()
                  match jsonLog with
                  | some path => writeJsonLog path payload
                  | none => pure ()
                  if ok then
                    IO.println s!"Lean validator: projection matches for {program.role}"
                    pure 0
                  else
                    IO.eprintln s!"Projection mismatch for {program.role}"
                    pure 1

/-! ## Projection Export Runners -/

/-- Export a projection for a single role to a JSON file. -/
def runExportProjection (inputPath : System.FilePath) (role : String)
    (outputPath : System.FilePath) : IO UInt32 := do
  let inputJson ← readJsonFile inputPath
  let (payload, ok) ←
    match inputJson with
    | .error err =>
        pure (Json.mkObj [("success", Json.bool false), ("error", Json.str err)], false)
    | .ok inputDoc =>
        match globalTypeFromJson inputDoc with
        | .error err =>
            pure (Json.mkObj [("success", Json.bool false), ("error", Json.str err)], false)
        | .ok global =>
            let localType := trans global role
            pure (Json.mkObj
              [ ("success", Json.bool true)
              , ("projection", localTypeRToJson localType)
              ], true)
  IO.FS.writeFile outputPath (payload.pretty ++ "\n")
  pure (if ok then 0 else 1)

/-- Export projections for all roles to a JSON file. -/
def runExportAllProjections (inputPath : System.FilePath)
    (outputPath : System.FilePath) : IO UInt32 := do
  let inputJson ← readJsonFile inputPath
  let (payload, ok) ←
    match inputJson with
    | .error err =>
        pure (Json.mkObj [("success", Json.bool false), ("error", Json.str err)], false)
    | .ok inputDoc =>
        match globalTypeFromJson inputDoc with
        | .error err =>
            pure (Json.mkObj [("success", Json.bool false), ("error", Json.str err)], false)
        | .ok global =>
            let roles := global.roles
            let projections := roles.map fun role =>
              (role, localTypeRToJson (trans global role))
            pure (Json.mkObj
              [ ("success", Json.bool true)
              , ("projections", Json.mkObj projections)
              ], true)
  IO.FS.writeFile outputPath (payload.pretty ++ "\n")
  pure (if ok then 0 else 1)

/-! ## CLI Entry -/

/-- Usage message. -/
def usage : String :=
  "usage: telltale_validator --choreography <path> --program <path> [--log <path>] [--json-log <path>]\n" ++
  "       telltale_validator --export-projection <path> --role <role> --output <path>\n" ++
  "       telltale_validator --export-all-projections <path> --output <path>"

/-- CLI entry point. -/
def validatorMain (args : List String) : IO UInt32 :=
  match args with
  | ["--choreography", chPath, "--program", progPath] =>
      runValidation ⟨chPath⟩ ⟨progPath⟩ none none
  | ["--choreography", chPath, "--program", progPath, "--log", logPath] =>
      runValidation ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) none
  | ["--choreography", chPath, "--program", progPath, "--json-log", jsonLog] =>
      runValidation ⟨chPath⟩ ⟨progPath⟩ none (some ⟨jsonLog⟩)
  | ["--choreography", chPath, "--program", progPath, "--log", logPath, "--json-log", jsonLog] =>
      runValidation ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) (some ⟨jsonLog⟩)
  | ["--choreography", chPath, "--program", progPath, "--json-log", jsonLog, "--log", logPath] =>
      runValidation ⟨chPath⟩ ⟨progPath⟩ (some ⟨logPath⟩) (some ⟨jsonLog⟩)
  | ["--export-projection", inputPath, "--role", role, "--output", outputPath] =>
      runExportProjection ⟨inputPath⟩ role ⟨outputPath⟩
  | ["--export-all-projections", inputPath, "--output", outputPath] =>
      runExportAllProjections ⟨inputPath⟩ ⟨outputPath⟩
  | _ =>
      IO.println usage *> pure (1 : UInt32)

end Choreography.Projection.Validator

def main (args : List String) : IO UInt32 :=
  Choreography.Projection.Validator.validatorMain args
