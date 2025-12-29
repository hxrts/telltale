import Lean.Data.Json
import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Choreography
import Rumpsteak.Protocol.Program

/-! # Rumpsteak.Runner.Json

JSON parsing utilities for the verification runner.

## Overview

This module provides helper functions for parsing JSON documents exported
by the Rust choreography compiler. It handles choreography AST parsing
and program effect parsing.

## Main Definitions

- `getField`, `parseArray`, `parseString` - Low-level JSON accessors
- `parseRoles`, `parseAction`, `parseActions` - Choreography parsing
- `parseEffect`, `parseBranch`, `parseProgramExport` - Program parsing
- `readJsonFile` - File I/O helper
-/

namespace Rumpsteak.Runner.Json

open Lean
open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Choreography
open Rumpsteak.Protocol.Program

/-! ## Low-level JSON Helpers -/

/-- Extract a field from a JSON object, returning an error if missing. -/
def getField (json : Json) (key : String) : Except String Json :=
  match json.getObjVal? key with
  | Except.ok v => Except.ok v
  | Except.error _ => Except.error s!"Missing field '{key}'"

/-- Parse a JSON value as an array. -/
def parseArray (json : Json) : Except String (Array Json) :=
  match json.getArr? with
  | Except.ok arr => Except.ok arr
  | Except.error _ => Except.error "Expected JSON array"

/-- Parse a JSON value as a string. -/
def parseString (json : Json) : Except String String :=
  match json.getStr? with
  | Except.ok s => Except.ok s
  | Except.error _ => Except.error "Expected JSON string"

/-! ## Choreography Parsing -/

/-- Parse the roles array from a choreography JSON document. -/
def parseRoles (json : Json) : Except String (List Role) := do
  let arr ← getField json "roles" >>= parseArray
  arr.toList.mapM (fun j => do
    let name ← parseString j
    pure { name := name })

/-- Parse a single action object from JSON. -/
def parseAction (json : Json) : Except String Action := do
  let origin ← getField json "from" >>= parseString
  let dest ← getField json "to" >>= parseString
  let label ← getField json "label" >>= parseString
  pure (origin, dest, label)

/-- Parse the actions array from a choreography JSON document. -/
def parseActions (json : Json) : Except String (List Action) := do
  let arr ← getField json "actions" >>= parseArray
  arr.toList.mapM parseAction

/-- Parse a complete choreography from JSON. -/
def parseChoreography (json : Json) : Except String Choreography := do
  let roles ← parseRoles json
  let actions ← parseActions json
  pure { roles := roles, actions := actions }

/-! ## Program Parsing -/

/-- A program branch with optional name and effect sequence. -/
structure ProgramBranch where
  /-- Optional branch name (for choice branches). -/
  branch : Option String
  /-- The sequence of effects in this branch. -/
  effects : List Effect

/-- Exported program with role and multiple branches. -/
structure ProgramExport where
  /-- The role this program is for. -/
  role : String
  /-- The program branches (one for linear protocols, multiple for choices). -/
  programs : List ProgramBranch

/-- Parse a single effect object from JSON. -/
def parseEffect (json : Json) : Except String Effect := do
  let kind ← getField json "kind" >>= parseString
  let partner ← getField json "partner" >>= parseString
  let label ← getField json "label" >>= parseString
  match kind with
  | "send" => Except.ok (.send partner label)
  | "recv" => Except.ok (.recv partner label)
  | _ => Except.error s!"Unknown effect kind '{kind}'"

/-- Parse a program branch from JSON. -/
def parseBranch (json : Json) : Except String ProgramBranch := do
  let branch ← match json.getObjVal? "branch" with
    | Except.ok v =>
        if v == Json.null then
          Except.ok none
        else
          parseString v >>= fun s => Except.ok (some s)
    | Except.error _ => Except.ok none
  let effArr ← getField json "effects" >>= parseArray
  let effects ← effArr.toList.mapM parseEffect
  pure { branch, effects }

/-- Parse a complete program export from JSON. -/
def parseProgramExport (json : Json) : Except String ProgramExport := do
  let role ← getField json "role" >>= parseString
  let branchesArr ← getField json "programs" >>= parseArray
  let programs ← branchesArr.toList.mapM parseBranch
  pure { role, programs }

/-! ## File I/O -/

/-- Read and parse a JSON file. -/
def readJsonFile (path : System.FilePath) : IO (Except String Json) := do
  let content ← IO.FS.readFile path
  pure (Json.parse content)

end Rumpsteak.Runner.Json
